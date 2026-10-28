#!/usr/bin/env python3
"""Verify the Lumenary compute experiments and write the compute report.

What it does, in order:

1. Reads each ``compute/experiments/<id>.py``'s ``EXPERIMENT`` metadata
   statically (the file is not imported for this step) and hashes the file.
2. Runs each experiment as a separate process, ``python -I -X utf8 <file>``,
   with a timeout. ``ran`` is true only for exit status 0 with non-empty output.
3. Runs the pytest suite in ``compute/tests`` in-process with a small
   collector plugin, counting passed / failed / skipped tests and mapping each
   test to the experiment(s) it exercises:
     * every test in ``tests/test_<id>.py`` belongs to experiment ``<id>``;
     * a parametrized test whose parameter id is ``<id>`` belongs to it too.
   ``testsPassed`` is true only if at least one mapped test passed and none failed.
4. Writes ``content/verification/compute-report.json`` matching the
   ``ComputeReport`` zod schema in ``src/lib/schema.ts``.

The report is always written. The exit status is non-zero if any experiment
failed to run, any test failed, or the report does not match the schema.

Usage:  compute/.venv/bin/python compute/verify.py [--report PATH] [--timeout SECONDS]
(or ``npm run verify:compute``, which calls scripts/verify-compute.mjs).
"""

import argparse
import ast
import datetime
import hashlib
import json
import pathlib
import platform
import re
import subprocess
import sys
import time
from importlib import metadata

# Importing experiments/tests in-process must not litter the tree with __pycache__.
sys.dont_write_bytecode = True

COMPUTE_DIR = pathlib.Path(__file__).resolve().parent
REPO_ROOT = COMPUTE_DIR.parent
EXPERIMENTS_DIR = COMPUTE_DIR / "experiments"
TESTS_DIR = COMPUTE_DIR / "tests"
DEFAULT_REPORT = REPO_ROOT / "content" / "verification" / "compute-report.json"

#: Must match EVIDENCE_TYPES in src/lib/schema.ts (checked by the test suite).
EVIDENCE_TYPES = ("exact", "symbolic", "numerical", "experimental", "exhaustive-finite", "statistical", "counterexample")
#: Distributions whose installed versions are recorded in the report.
REPORTED_PACKAGES = ("sympy", "mpmath", "numpy", "pytest")
DEFAULT_TIMEOUT_S = 30.0
METADATA_KEYS = ("id", "title", "evidence", "lessons", "summary", "packages")


# --------------------------------------------------------------------------
# Experiments
# --------------------------------------------------------------------------

def experiment_files(directory=EXPERIMENTS_DIR):
    """All experiment files, sorted by id (files starting with '_' are helpers, not experiments)."""
    return sorted(p for p in pathlib.Path(directory).glob("*.py") if not p.name.startswith("_"))


def read_metadata(path):
    """Return the ``EXPERIMENT`` dict of an experiment file without executing it.

    Raises ValueError if there is no top-level ``EXPERIMENT = {...}`` literal.
    """
    tree = ast.parse(pathlib.Path(path).read_text(encoding="utf-8"), filename=str(path))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "EXPERIMENT" for t in node.targets):
            try:
                value = ast.literal_eval(node.value)
            except ValueError as exc:
                raise ValueError(f"{path}: EXPERIMENT must be a plain literal ({exc})") from None
            if not isinstance(value, dict):
                raise ValueError(f"{path}: EXPERIMENT must be a dict")
            return value
    raise ValueError(f"{path}: no top-level EXPERIMENT = {{...}} assignment")


def metadata_problems(meta, expected_id):
    """List the ways ``meta`` is malformed (empty list when it is fine)."""
    problems = []
    if set(meta) != set(METADATA_KEYS):
        problems.append(f"keys must be exactly {list(METADATA_KEYS)}, got {sorted(meta)}")
    if meta.get("id") != expected_id:
        problems.append(f"id {meta.get('id')!r} does not match file name {expected_id!r}")
    for key in ("title", "summary"):
        if not isinstance(meta.get(key), str) or not meta.get(key, "").strip():
            problems.append(f"{key} must be a non-empty string")
    for key in ("evidence", "lessons", "packages"):
        if not isinstance(meta.get(key), list) or not all(isinstance(x, str) for x in meta.get(key, [])):
            problems.append(f"{key} must be a list of strings")
    evidence = meta.get("evidence") if isinstance(meta.get("evidence"), list) else []
    if not evidence:
        problems.append("evidence must list at least one evidence type")
    unknown = [e for e in evidence if e not in EVIDENCE_TYPES]
    if unknown:
        problems.append(f"unknown evidence types {unknown}")
    return problems


def sha256_file(path):
    """Hex sha256 of a file's bytes."""
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def run_experiment(python, path, timeout=DEFAULT_TIMEOUT_S):
    """Run one experiment file in a fresh, isolated interpreter.

    Returns a dict with keys ran, durationMs, returncode, stdout, stderr.
    ``durationMs`` is wall-clock time including interpreter start-up and imports.
    """
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            [python, "-I", "-X", "utf8", str(path)],
            cwd=str(COMPUTE_DIR),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "ran": False,
            "durationMs": round((time.perf_counter() - start) * 1000),
            "returncode": None,
            "stdout": exc.stdout or "",
            "stderr": f"timed out after {timeout} s",
        }
    except OSError as exc:
        return {"ran": False, "durationMs": 0, "returncode": None, "stdout": "", "stderr": str(exc)}
    return {
        "ran": proc.returncode == 0 and bool(proc.stdout.strip()),
        "durationMs": round((time.perf_counter() - start) * 1000),
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


# --------------------------------------------------------------------------
# pytest
# --------------------------------------------------------------------------

class OutcomeCollector:
    """A pytest plugin object that records one final outcome per test node id."""

    def __init__(self):
        self.outcomes = {}

    def pytest_runtest_logreport(self, report):
        previous = self.outcomes.get(report.nodeid)
        if report.failed:
            self.outcomes[report.nodeid] = "failed"
        elif report.skipped:
            if previous != "failed":
                self.outcomes[report.nodeid] = "skipped"
        elif report.when == "call" and previous is None:
            self.outcomes[report.nodeid] = "passed"

    def pytest_collectreport(self, report):
        if report.failed:
            self.outcomes[report.nodeid or "<collection>"] = "failed"


def run_pytest(tests_dir=TESTS_DIR):
    """Run the test suite in-process. Returns (outcomes dict, exit code, duration in ms)."""
    try:
        import pytest
    except ImportError:
        print("verify: pytest is not installed in this interpreter; see docs/compute.md", file=sys.stderr)
        return {}, None, 0
    collector = OutcomeCollector()
    start = time.perf_counter()
    code = pytest.main(
        [str(tests_dir), "-q", "--rootdir", str(COMPUTE_DIR), "-c", str(COMPUTE_DIR / "pytest.ini")],
        plugins=[collector],
    )
    return collector.outcomes, int(code), round((time.perf_counter() - start) * 1000)


def count_outcomes(outcomes):
    """{'passed': n, 'failed': n, 'skipped': n} from a node-id -> outcome mapping."""
    counts = {"passed": 0, "failed": 0, "skipped": 0}
    for outcome in outcomes.values():
        counts[outcome] += 1
    return counts


def experiments_for_test(nodeid, experiment_ids):
    """The experiment ids a pytest node id belongs to (see module docstring for the rules)."""
    ids = set(experiment_ids)
    path, _, rest = nodeid.partition("::")
    stem = pathlib.PurePosixPath(path.replace("\\", "/")).stem
    found = set()
    if stem.startswith("test_") and stem[len("test_"):] in ids:
        found.add(stem[len("test_"):])
    for params in re.findall(r"\[([^\]]*)\]", rest):
        found.update(part for part in params.split("-") if part in ids)
    return found


def tests_passed_by_experiment(outcomes, experiment_ids):
    """{id: bool}: True when at least one mapped test passed and none failed."""
    mapped = {eid: [] for eid in experiment_ids}
    for nodeid, outcome in outcomes.items():
        for eid in experiments_for_test(nodeid, experiment_ids):
            mapped[eid].append(outcome)
    return {eid: ("passed" in results and "failed" not in results) for eid, results in mapped.items()}


# --------------------------------------------------------------------------
# Report
# --------------------------------------------------------------------------

def package_versions(names=REPORTED_PACKAGES):
    """Installed versions of the given distributions (missing ones are left out)."""
    versions = {}
    for name in names:
        try:
            versions[name] = metadata.version(name)
        except metadata.PackageNotFoundError:
            pass
    return versions


def _is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def _is_num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool)


def validate_report(report):
    """Check a report against the ComputeReport zod schema; return a list of problems."""
    problems = []

    def need(cond, message):
        if not cond:
            problems.append(message)

    need(isinstance(report, dict), "report must be an object")
    if not isinstance(report, dict):
        return problems
    need(isinstance(report.get("generatedAt"), str), "generatedAt must be a string")
    need(isinstance(report.get("python"), str), "python must be a string")
    pkgs = report.get("packages")
    need(isinstance(pkgs, dict) and all(isinstance(k, str) and isinstance(v, str) for k, v in pkgs.items()),
         "packages must map strings to strings")
    pt = report.get("pytest")
    need(isinstance(pt, dict), "pytest must be an object")
    if isinstance(pt, dict):
        for key in ("passed", "failed", "skipped"):
            need(_is_int(pt.get(key)), f"pytest.{key} must be an integer")
        need(_is_num(pt.get("durationMs")), "pytest.durationMs must be a number")
    exps = report.get("experiments")
    need(isinstance(exps, list), "experiments must be an array")
    for i, e in enumerate(exps if isinstance(exps, list) else []):
        where = f"experiments[{i}]"
        if not isinstance(e, dict):
            problems.append(f"{where} must be an object")
            continue
        for key in ("id", "title", "file", "summary", "sha256"):
            need(isinstance(e.get(key), str), f"{where}.{key} must be a string")
        ev = e.get("evidence")
        need(isinstance(ev, list) and len(ev) >= 1 and all(x in EVIDENCE_TYPES for x in ev),
             f"{where}.evidence must be a non-empty list of evidence types")
        for key in ("lessons", "packages"):
            need(isinstance(e.get(key), list) and all(isinstance(x, str) for x in e.get(key)),
                 f"{where}.{key} must be a list of strings")
        for key in ("ran", "testsPassed"):
            need(isinstance(e.get(key), bool), f"{where}.{key} must be a boolean")
        need(_is_num(e.get("durationMs")), f"{where}.durationMs must be a number")
    return problems


def display_path(path):
    """Repository-relative POSIX path when possible (absolute otherwise)."""
    path = pathlib.Path(path).resolve()
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def build_report(python, timeout=DEFAULT_TIMEOUT_S, run_tests=True, log=print, experiments_dir=EXPERIMENTS_DIR):
    """Run everything and return (report dict, list of failure messages).

    With ``run_tests=False`` pytest is not run, which is recorded as a failure.
    """
    failures = []
    entries = []
    for path in experiment_files(experiments_dir):
        eid = path.stem
        try:
            meta = read_metadata(path)
        except (ValueError, SyntaxError) as exc:
            failures.append(f"{eid}: unreadable metadata: {exc}")
            continue
        problems = metadata_problems(meta, eid)
        if problems:
            failures.extend(f"{eid}: {p}" for p in problems)
            continue
        result = run_experiment(python, path, timeout)
        if not result["ran"]:
            last = (result["stderr"].strip().splitlines() or ["no output"])[-1]
            failures.append(f"{eid}: did not run cleanly (exit {result['returncode']}): {last}")
            if result["stderr"].strip():
                log(result["stderr"].rstrip())
        entries.append({
            "id": eid,
            "title": meta["title"],
            "file": display_path(path),
            "evidence": list(meta["evidence"]),
            "lessons": list(meta["lessons"]),
            "summary": meta["summary"],
            "packages": list(meta["packages"]),
            "ran": result["ran"],
            "testsPassed": False,
            "durationMs": result["durationMs"],
            "sha256": sha256_file(path),
        })
        log(f"  ran  {eid:<26} {'ok ' if result['ran'] else 'FAIL'} {result['durationMs']:>6} ms")

    outcomes, code, duration = run_pytest() if run_tests else ({}, None, 0)
    counts = count_outcomes(outcomes)
    if code is None:
        failures.append("pytest did not run")
    elif code != 0:
        failures.append(f"pytest exited with status {code}")
    passed_map = tests_passed_by_experiment(outcomes, [e["id"] for e in entries])
    for entry in entries:
        entry["testsPassed"] = passed_map.get(entry["id"], False)
        if not entry["testsPassed"]:
            failures.append(f"{entry['id']}: its tests did not all pass (or none were found)")

    report = {
        "generatedAt": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
        "python": platform.python_version(),
        "packages": package_versions(),
        "pytest": {**counts, "durationMs": duration},
        "experiments": entries,
    }
    failures.extend(f"schema: {p}" for p in validate_report(report))
    return report, failures


def write_report(report, path):
    """Write the report as pretty JSON with a trailing newline."""
    path = pathlib.Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--report", default=str(DEFAULT_REPORT), help="where to write the JSON report")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT_S, help="per-experiment timeout in seconds")
    args = parser.parse_args(argv)

    print(f"verify: Python {platform.python_version()} at {sys.executable}")
    report, failures = build_report(sys.executable, timeout=args.timeout)
    write_report(report, args.report)
    pt = report["pytest"]
    print(f"verify: pytest {pt['passed']} passed, {pt['failed']} failed, {pt['skipped']} skipped ({pt['durationMs']} ms)")
    print(f"verify: wrote {args.report}")
    if failures:
        print(f"verify: {len(failures)} problem(s):", file=sys.stderr)
        for message in failures:
            print(f"  - {message}", file=sys.stderr)
        return 1
    print(f"verify: all {len(report['experiments'])} experiments ran and their tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
