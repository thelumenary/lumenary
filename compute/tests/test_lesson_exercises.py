"""Check every Python exercise in content/math/lessons/*/exercises.json.

For each exercise with ``"type": "python"``:

* the first ```python fenced block in its ``solution`` markdown, followed by
  its ``tests``, must run without raising (the model solution passes);
* its ``starter`` followed by its ``tests`` must raise (so the tests really
  test something - an untouched starter must not pass);
* the starter must at least be valid Python, so learners see a test failure
  rather than a syntax error;
* the solution and tests must run well within the browser's time budget.

Each piece runs in a fresh namespace, as it does in the browser. If there are
no lesson exercise files yet, the tests are skipped. Set LUMENARY_LESSONS_DIR
to point the checker at another folder of <lesson>/exercises.json files.
"""

import json
import os
import pathlib
import re
import time

import pytest

from conftest import REPO_ROOT

#: LUMENARY_LESSONS_DIR lets the checker itself be tried on a scratch folder.
LESSONS_DIR = pathlib.Path(os.environ.get("LUMENARY_LESSONS_DIR", REPO_ROOT / "content" / "math" / "lessons"))
FENCE = re.compile(r"```python[^\n]*\n(.*?)```", re.S)
MAX_SECONDS = 2.0


def first_python_block(markdown):
    """The code inside the first ```python fenced block, or None."""
    match = FENCE.search(markdown)
    return match.group(1) if match else None


def fresh_namespace():
    return {"__name__": "__lumenary_exercise__"}


def run_in_fresh_namespace(*sources):
    """exec each source in order in one new namespace (as the browser does)."""
    namespace = fresh_namespace()
    for label, source in sources:
        exec(compile(source, f"<{label}>", "exec"), namespace)
    return namespace


def collect_python_exercises():
    params = []
    for path in sorted(LESSONS_DIR.glob("*/exercises.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        for exercise in data.get("exercises", []):
            if exercise.get("type") == "python":
                params.append(pytest.param(exercise, id=f"{path.parent.name}/{exercise.get('id', '?')}"))
    if not params:
        params.append(pytest.param(None, id="no-python-exercises",
                                   marks=pytest.mark.skip(reason="no Python exercises in content/math/lessons yet")))
    return params


EXERCISES = collect_python_exercises()


def test_fence_extraction_helper():
    md = "Intro\n\n```python\nx = 1\n```\n\nThen\n\n```python\ny = 2\n```"
    assert first_python_block(md) == "x = 1\n"
    assert first_python_block("no code here") is None
    assert first_python_block("```js\nlet x\n```") is None


def test_fresh_namespaces_are_isolated():
    run_in_fresh_namespace(("a", "leak = 1"))
    with pytest.raises(NameError):
        run_in_fresh_namespace(("b", "leak"))


@pytest.mark.parametrize("exercise", EXERCISES)
def test_solution_passes_tests(exercise):
    for key in ("solution", "starter", "tests"):
        assert isinstance(exercise.get(key), str), f"python exercise needs a string {key!r}"
    code = first_python_block(exercise["solution"])
    assert code is not None, "solution markdown must contain a ```python fenced block"
    start = time.perf_counter()
    run_in_fresh_namespace(("solution", code), ("tests", exercise["tests"]))
    assert time.perf_counter() - start < MAX_SECONDS


@pytest.mark.parametrize("exercise", EXERCISES)
def test_starter_is_valid_python(exercise):
    compile(exercise["starter"], "<starter>", "exec")


@pytest.mark.parametrize("exercise", EXERCISES)
def test_starter_fails_tests(exercise):
    with pytest.raises(Exception):
        run_in_fresh_namespace(("starter", exercise["starter"]), ("tests", exercise["tests"]))
