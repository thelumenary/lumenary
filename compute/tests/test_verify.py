"""Tests for compute/verify.py (the report generator), not for any one experiment."""

import json
import sys

import pytest

import verify

IDS = ["alpha", "beta_gamma", "delta"]


def good_report():
    return {
        "generatedAt": "2026-01-01T00:00:00Z",
        "python": "3.13.2",
        "packages": {"sympy": "1.13.3"},
        "pytest": {"passed": 3, "failed": 0, "skipped": 1, "durationMs": 12},
        "experiments": [{
            "id": "alpha", "title": "A", "file": "compute/experiments/alpha.py", "evidence": ["exact"],
            "lessons": ["sets"], "summary": "s", "packages": [], "ran": True, "testsPassed": True,
            "durationMs": 5.5, "sha256": "0" * 64,
        }],
    }


def test_read_metadata_reads_literal_without_running(tmp_path):
    path = tmp_path / "x.py"
    path.write_text('raise SystemExit("must not run")\nEXPERIMENT = {"id": "x", "summary": ("a" "b")}\n')
    assert verify.read_metadata(path) == {"id": "x", "summary": "ab"}


@pytest.mark.parametrize("source", ["X = 1\n", "EXPERIMENT = dict(id='x')\n", "EXPERIMENT = [1]\n"])
def test_read_metadata_rejects_missing_or_dynamic(tmp_path, source):
    path = tmp_path / "x.py"
    path.write_text(source)
    with pytest.raises(ValueError):
        verify.read_metadata(path)


def test_metadata_problems():
    meta = {"id": "x", "title": "T", "evidence": ["exact"], "lessons": [], "summary": "S", "packages": []}
    assert verify.metadata_problems(meta, "x") == []
    assert verify.metadata_problems({**meta, "id": "y"}, "x")
    assert verify.metadata_problems({**meta, "evidence": []}, "x")
    assert verify.metadata_problems({**meta, "evidence": ["proof"]}, "x")
    assert verify.metadata_problems({**meta, "extra": 1}, "x")
    assert verify.metadata_problems({**meta, "title": " "}, "x")


@pytest.mark.parametrize("nodeid,expected", [
    ("tests/test_alpha.py::test_one", {"alpha"}),
    ("tests/test_beta_gamma.py::test_x[3-4]", {"beta_gamma"}),
    ("tests/test_meta.py::test_runs[delta]", {"delta"}),
    ("tests/test_meta.py::test_pair[alpha-delta]", {"alpha", "delta"}),
    ("tests/test_meta.py::test_other", set()),
    ("tests/test_alphabet.py::test_one", set()),
    ("tests\\test_alpha.py::test_win", {"alpha"}),
    ("tests/test_meta.py::test_runs[alphax]", set()),
])
def test_experiments_for_test(nodeid, expected):
    assert verify.experiments_for_test(nodeid, IDS) == expected


def test_tests_passed_by_experiment():
    outcomes = {
        "tests/test_alpha.py::a": "passed",
        "tests/test_alpha.py::b": "skipped",
        "tests/test_meta.py::m[beta_gamma]": "passed",
        "tests/test_beta_gamma.py::c": "failed",
        "tests/test_meta.py::m[delta]": "skipped",
    }
    assert verify.tests_passed_by_experiment(outcomes, IDS) == {"alpha": True, "beta_gamma": False, "delta": False}


def test_count_outcomes():
    assert verify.count_outcomes({"a": "passed", "b": "failed", "c": "passed", "d": "skipped"}) == \
        {"passed": 2, "failed": 1, "skipped": 1}
    assert verify.count_outcomes({}) == {"passed": 0, "failed": 0, "skipped": 0}


class _Report:
    def __init__(self, nodeid, when, outcome):
        self.nodeid, self.when, self.outcome = nodeid, when, outcome
        self.failed = outcome == "failed"
        self.skipped = outcome == "skipped"


def test_outcome_collector_resolves_phases():
    c = verify.OutcomeCollector()
    for phase in [("ok", "setup", "passed"), ("ok", "call", "passed"), ("ok", "teardown", "passed"),
                  ("skip", "setup", "skipped"), ("skip", "teardown", "passed"),
                  ("bad", "setup", "passed"), ("bad", "call", "failed"), ("bad", "teardown", "passed"),
                  ("td", "setup", "passed"), ("td", "call", "passed"), ("td", "teardown", "failed")]:
        c.pytest_runtest_logreport(_Report(*phase))
    assert c.outcomes == {"ok": "passed", "skip": "skipped", "bad": "failed", "td": "failed"}


def test_validate_report_accepts_good_and_rejects_bad():
    assert verify.validate_report(good_report()) == []
    bad = good_report()
    bad["pytest"]["passed"] = 1.5
    bad["experiments"][0]["evidence"] = []
    bad["experiments"][0]["ran"] = "yes"
    del bad["python"]
    problems = verify.validate_report(bad)
    assert len(problems) == 4
    assert verify.validate_report([]) == ["report must be an object"]


def test_sha256_file(tmp_path):
    path = tmp_path / "f"
    path.write_bytes(b"abc")
    assert verify.sha256_file(path) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"


def test_run_experiment_success_failure_and_timeout(tmp_path):
    ok = tmp_path / "ok.py"
    ok.write_text("print('∅ hello')\n", encoding="utf-8")
    result = verify.run_experiment(sys.executable, ok, timeout=20)
    assert result["ran"] and result["stdout"] == "∅ hello\n" and result["returncode"] == 0

    silent = tmp_path / "silent.py"
    silent.write_text("x = 1\n")
    assert not verify.run_experiment(sys.executable, silent, timeout=20)["ran"]

    boom = tmp_path / "boom.py"
    boom.write_text("print('partial')\nraise RuntimeError('boom')\n")
    result = verify.run_experiment(sys.executable, boom, timeout=20)
    assert not result["ran"] and result["returncode"] == 1 and "boom" in result["stderr"]

    slow = tmp_path / "slow.py"
    slow.write_text("while True:\n    pass\n")
    result = verify.run_experiment(sys.executable, slow, timeout=0.5)
    assert not result["ran"] and result["returncode"] is None and "timed out" in result["stderr"]


def test_run_experiment_is_isolated_from_sibling_modules(tmp_path):
    (tmp_path / "helper.py").write_text("VALUE = 1\n")
    script = tmp_path / "uses_helper.py"
    script.write_text("import helper\nprint(helper.VALUE)\n")
    # Each experiment must be self-contained, as in the browser: -I keeps the script's folder off sys.path.
    assert not verify.run_experiment(sys.executable, script, timeout=20)["ran"]


def test_write_report_round_trips(tmp_path):
    path = tmp_path / "nested" / "report.json"
    verify.write_report(good_report(), path)
    text = path.read_text(encoding="utf-8")
    assert text.endswith("\n")
    assert json.loads(text) == good_report()


def test_package_versions_records_installed_versions_only():
    versions = verify.package_versions(("pytest", "definitely-not-a-real-package-xyz"))
    assert set(versions) == {"pytest"}
    assert versions["pytest"] == pytest.__version__


def test_experiment_files_skip_helpers(tmp_path):
    for name in ("b.py", "a.py", "_helper.py", "notes.txt"):
        (tmp_path / name).write_text("")
    assert [p.name for p in verify.experiment_files(tmp_path)] == ["a.py", "b.py"]


def test_build_report_records_failures_but_still_produces_a_valid_report(tmp_path):
    good = tmp_path / "good_one.py"
    good.write_text(
        'EXPERIMENT = {"id": "good_one", "title": "Good", "evidence": ["exact"], "lessons": ["sets"],\n'
        '              "summary": "Prints a line.", "packages": []}\n'
        'print("Epistemic status: fine.")\n'
    )
    crash = tmp_path / "crashes.py"
    crash.write_text(
        'EXPERIMENT = {"id": "crashes", "title": "Crash", "evidence": ["numerical"], "lessons": [],\n'
        '              "summary": "Raises.", "packages": []}\n'
        'raise ZeroDivisionError("on purpose")\n'
    )
    (tmp_path / "bad_meta.py").write_text('EXPERIMENT = {"id": "other"}\n')
    report, failures = verify.build_report(sys.executable, timeout=20, run_tests=False,
                                           log=lambda *a: None, experiments_dir=tmp_path)
    assert verify.validate_report(report) == []
    by_id = {e["id"]: e for e in report["experiments"]}
    assert set(by_id) == {"good_one", "crashes"}  # malformed metadata is reported, not published
    assert by_id["good_one"]["ran"] is True
    assert by_id["crashes"]["ran"] is False
    assert all(e["testsPassed"] is False for e in by_id.values())  # no tests were run
    text = "\n".join(failures)
    assert "crashes: did not run cleanly" in text and "ZeroDivisionError" in text
    assert "bad_meta:" in text
    assert "pytest did not run" in text
