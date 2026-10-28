"""Checks that apply to every experiment file.

* EXPERIMENT metadata is well formed and agrees with the website's schema.
* The file only uses modules that exist in Pyodide and declares the packages
  the browser must load.
* main() runs in under 2 seconds, prints a short, deterministic, plain-text
  report and ends with an explicit "Epistemic status:" paragraph.
"""

import ast
import importlib
import pathlib
import re
import time

import pytest

from conftest import EXPECTED_IDS, EXPERIMENTS_DIR, REPO_ROOT, experiment_ids, load_experiment

import verify

KNOWN_LESSONS = {"collections", "sets", "integers", "functions", "composition"}
KNOWN_TRAILS = {
    "inverses-and-structure",
    "arrows-that-compose",
    "clock-arithmetic",
    "remainder-families",
    "how-many-infinities",
}
#: Standard-library modules experiments may import (all present in Pyodide 0.29.3).
ALLOWED_STDLIB = {
    "bisect", "cmath", "collections", "dataclasses", "decimal", "fractions", "functools",
    "heapq", "itertools", "math", "numbers", "operator", "random", "statistics", "string",
    "textwrap", "typing",
}
#: Third-party packages the browser can load, keyed by import name -> Pyodide package name.
BROWSER_PACKAGES = {"sympy": "sympy", "numpy": "numpy"}
#: Built-ins that would do I/O or dynamic code execution - not allowed in experiments.
FORBIDDEN_NAMES = {"open", "input", "exec", "eval", "compile", "__import__", "breakpoint", "help"}

MAX_SECONDS = 2.0
MAX_LINES = 40
MAX_WIDTH = 80

IDS = experiment_ids()


def source_of(experiment_id):
    return (EXPERIMENTS_DIR / f"{experiment_id}.py").read_text(encoding="utf-8")


def imported_modules(tree):
    """Top-level module names imported anywhere in the AST."""
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.update(alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                names.add("." * node.level + (node.module or ""))
            else:
                names.add(node.module.split(".")[0])
    return names


def test_expected_experiments_exist():
    assert IDS == sorted(EXPECTED_IDS)


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_metadata_well_formed(experiment_id):
    meta = load_experiment(experiment_id).EXPERIMENT
    assert set(meta) == {"id", "title", "evidence", "lessons", "summary", "packages"}
    assert meta["id"] == experiment_id
    assert re.fullmatch(r"[a-z][a-z0-9_]*", meta["id"])
    assert isinstance(meta["title"], str) and 5 <= len(meta["title"]) <= 80
    assert meta["title"] == meta["title"].strip()
    evidence = meta["evidence"]
    assert isinstance(evidence, list) and evidence, "at least one evidence type"
    assert len(set(evidence)) == len(evidence), "no duplicate evidence types"
    assert set(evidence) <= set(verify.EVIDENCE_TYPES)
    lessons = meta["lessons"]
    assert isinstance(lessons, list) and lessons
    assert len(set(lessons)) == len(lessons)
    for slug in lessons:
        assert re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", slug), slug
        assert slug in KNOWN_LESSONS | KNOWN_TRAILS, f"unknown lesson/trail slug {slug!r}"
    assert isinstance(meta["summary"], str) and 60 <= len(meta["summary"]) <= 600
    assert isinstance(meta["packages"], list)
    assert set(meta["packages"]) <= set(BROWSER_PACKAGES.values())
    assert meta["packages"] == sorted(set(meta["packages"]))


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_metadata_is_a_static_literal(experiment_id):
    """verify.py reads EXPERIMENT without executing the file, so it must be a plain literal."""
    assert verify.read_metadata(EXPERIMENTS_DIR / f"{experiment_id}.py") == load_experiment(experiment_id).EXPERIMENT


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_imports_are_browser_safe_and_declared(experiment_id):
    tree = ast.parse(source_of(experiment_id))
    modules = imported_modules(tree)
    third_party = modules - ALLOWED_STDLIB
    assert third_party <= set(BROWSER_PACKAGES), f"not available in the browser: {third_party - set(BROWSER_PACKAGES)}"
    declared = set(load_experiment(experiment_id).EXPERIMENT["packages"])
    assert declared == {BROWSER_PACKAGES[m] for m in third_party}, "EXPERIMENT['packages'] must match the imports"


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_no_io_or_dynamic_code(experiment_id):
    tree = ast.parse(source_of(experiment_id))
    used = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}
    assert not used & FORBIDDEN_NAMES
    attrs = {node.attr for node in ast.walk(tree) if isinstance(node, ast.Attribute)}
    assert not attrs & {"stdin", "system", "popen", "Thread", "Process"}


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_has_main_guard_and_no_import_side_effects(experiment_id, capsys):
    source = source_of(experiment_id)
    assert 'if __name__ == "__main__":\n    main()' in source
    importlib.reload(load_experiment(experiment_id))
    assert capsys.readouterr().out == "", "importing an experiment must not print"


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_main_runs_fast_with_honest_plain_output(experiment_id, capsys):
    module = load_experiment(experiment_id)
    start = time.perf_counter()
    module.main()
    elapsed = time.perf_counter() - start
    out = capsys.readouterr().out
    assert elapsed < MAX_SECONDS, f"main() took {elapsed:.2f} s"
    lines = out.rstrip("\n").split("\n")
    assert 5 <= len(lines) <= MAX_LINES, f"{len(lines)} lines"
    assert all(len(line) <= MAX_WIDTH for line in lines), max(lines, key=len)
    assert "\x1b" not in out and "\t" not in out, "plain text only (no ANSI colours or tabs)"
    assert all(line == line.rstrip() for line in lines), "no trailing whitespace"
    last_paragraph = out.rstrip("\n").split("\n\n")[-1]
    assert last_paragraph.startswith("Epistemic status:")


@pytest.mark.parametrize("experiment_id", IDS, ids=IDS)
def test_main_is_deterministic(experiment_id, capsys):
    module = load_experiment(experiment_id)
    module.main()
    first = capsys.readouterr().out
    module.main()
    assert capsys.readouterr().out == first


def test_evidence_types_match_website_schema():
    schema = REPO_ROOT / "src" / "lib" / "schema.ts"
    if not schema.exists():
        pytest.skip("src/lib/schema.ts not present")
    match = re.search(r"EVIDENCE_TYPES\s*=\s*\[(.*?)\]\s*as const", schema.read_text(encoding="utf-8"), re.S)
    assert match, "EVIDENCE_TYPES not found in schema.ts"
    assert re.findall(r'"([^"]+)"', match.group(1)) == list(verify.EVIDENCE_TYPES)
