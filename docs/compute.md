# Computational mathematics in the Lumenary

This is the **C** mode of the Lumenary's three modes of reasoning (Human, Formal,
Computational). The `compute/` folder holds small Python experiments that
learners run in their own browser. Each one is honest about what kind of evidence
it gives, and none of them claims that a computation is a proof when it is not.

```
compute/
  experiments/<id>.py   one self-contained experiment per file (run unchanged in the browser)
  tests/                pytest suite: unit tests per experiment + metadata/runtime checks
                        + lesson-exercise checks (test_lesson_exercises.py)
  verify.py             runs everything and writes content/verification/compute-report.json
  requirements.txt      pinned versions (match Pyodide 0.29.3)
  pytest.ini
scripts/verify-compute.mjs   Node wrapper used by `npm run verify:compute`
content/verification/compute-report.json   generated: never edit by hand
```

## Setup and running

You need CPython 3.10 or newer and Node 22. Install into a project virtualenv at
`compute/.venv`, which is gitignored. Never install into the system Python.

```bash
python3 -m venv compute/.venv
compute/.venv/bin/python -m pip install -r compute/requirements.txt

# run one experiment exactly as the verifier does (isolated mode, UTF-8 output)
compute/.venv/bin/python -I -X utf8 compute/experiments/set_identities.py

# run the tests
compute/.venv/bin/python -m pytest -c compute/pytest.ini compute/tests
#   (or: cd compute && .venv/bin/python -m pytest)

# full verification + report (what CI should run)
npm run verify:compute          # = node scripts/verify-compute.mjs
```

`scripts/verify-compute.mjs` uses `compute/.venv/bin/python` when it exists. If
it doesn't, it prints a warning and falls back to `python3` on `PATH`; in that
case the versions may not match the pins. Set `LUMENARY_PYTHON=/path/to/python`
to pick an interpreter yourself. Any extra arguments go through to `verify.py`
(`--report PATH`, `--timeout SECONDS`).

### What `verify.py` does

1. It reads each experiment's `EXPERIMENT` metadata **statically** (with
   `ast.literal_eval`, without running the file), checks that it is well formed
   and computes the file's sha256.
2. It runs each experiment in a fresh interpreter, `python -I -X utf8 <file>`, with
   a timeout (30 s by default). The `-I` flag keeps the experiment's own folder
   off `sys.path`, so an experiment can't import a sibling file. That matches the
   browser, where each file runs on its own. `ran` is true only when the exit
   status is 0 and something was printed. `durationMs` is the wall-clock time of
   that process, including interpreter start-up and imports.
3. It runs the pytest suite in-process with a small collector plugin, so the
   passed/failed/skipped counts are exact. Each test is then mapped to
   experiments:
   - every test in `tests/test_<id>.py` belongs to experiment `<id>`;
   - a parametrized test whose parameter id is `<id>` (for example
     `test_main_runs_fast_with_honest_plain_output[set_identities]`) belongs to it too.

   `testsPassed` is true only when at least one mapped test passed and none
   failed. Tests that map to no experiment (lesson exercises, tests of
   `verify.py` itself) still count in the totals.
4. It writes `content/verification/compute-report.json` in the exact shape of the
   `ComputeReport` zod schema in `src/lib/schema.ts`, and checks it against a
   Python mirror of that schema.

The report is **always written**. The exit status is non-zero if any experiment
failed to run, any test failed, pytest could not run, or the report does not
match the schema. The website derives the `computationally-tested` label only
from this report: a lesson cannot assert that label by hand.

What `testsPassed: true` means: the experiment ran, and the tests that exercise its
functions passed on the recorded Python and package versions. It does **not**
mean the mathematics in the lesson has been proved. See the evidence types below.

## Writing an experiment

Every experiment is one file, `compute/experiments/<id>.py`:

```python
EXPERIMENT = {
    "id": "set_identities",                      # must equal the file name
    "title": "Checking set identities exhaustively",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["sets"],                         # lesson slugs or Wonder Trail slugs
    "summary": "One or two sentences, honest about what this does and does NOT establish.",
    "packages": [],                              # Pyodide packages to load: "sympy", "numpy"
}

# pure, importable, documented functions ...

def main():
    ...
    print("Epistemic status: ...")              # always the final paragraph

if __name__ == "__main__":
    main()
```

The website runs these files **unchanged** in the learner's browser, so every
experiment must follow these rules. Apart from the first one, each rule is
enforced by `tests/test_experiments_meta.py`:

- **Use only the standard library, `sympy` and `numpy`.** Prefer the standard
  library when it teaches just as well. The `packages` list must match the
  imports exactly, because the browser loads only what is declared.
- **No I/O and no dynamic code:** no `open`, `input`, `exec`, `eval`, files,
  network, threads or subprocesses.
- **Keep `EXPERIMENT` a plain literal.** The verifier reads it without
  running the file.
- **Don't print at import time.** `main()` must stay behind the `__main__` guard.
- **Make `main()` fast, short and deterministic:**
  - it must run in under 2 s (the current experiments take under 50 ms each on
    CPython, which leaves plenty of room for the slower WebAssembly interpreter);
  - at most 40 lines of output, each at most 80 characters;
  - plain text only: no ANSI colours, no tabs, no trailing spaces;
  - the same output every run, so any randomness uses a fixed seed.
- **End with an epistemic status.** The last paragraph of the output must begin
  with `Epistemic status:` and say plainly what was shown and what was not.

## Evidence types

Every experiment declares one or more of these (`EVIDENCE_TYPES` in
`src/lib/schema.ts`). None of them is a proof in the usual sense. A few can
*be* proofs of narrower or negative statements, as the list explains.

- **`exact`**: arithmetic with no rounding (integers, `fractions.Fraction`,
  exact counts). The *answers* are exactly right for the inputs given. Exact
  arithmetic on particular cases is still about those cases only.
- **`symbolic`**: a computer-algebra system such as SymPy manipulates
  expressions like `(-a)*(-b)` with the letters left as letters. A symbolic
  identity covers all values at once, but it is only as trustworthy as the
  software's built-in rules. It also does not explain *why* the identity holds.
- **`numerical`**: floating-point approximation, for example `0.1 + 0.2`, or
  Newton's method in floats. Every result carries rounding error, which has to
  be measured or bounded. A numerical result can suggest that something is
  true; on its own it can never establish an exact equality.
- **`experimental`**: checking a pattern on chosen examples or a finite search
  window, such as Euler's polynomial for n = 0..39, or a grid of integers.
  This produces conjectures and confidence, and it can be badly misleading
  (forty primes in a row, then a failure). It is not a proof.
- **`exhaustive-finite`**: checking **every** case of a finite problem, such
  as all 4096 triples of subsets of a 4-element set. Within that finite
  universe this *is* a proof by exhaustion. It says nothing by itself about
  larger or infinite cases; the lesson's argument is what generalises.
- **`statistical`**: estimates from random sampling, reported with a
  confidence interval and a fixed seed. Statistical evidence is never certain:
  about 1 in 20 95% intervals misses the true value by chance. It cannot tell
  apart a probability of 1 and one of 0.9999.
- **`counterexample`**: a single explicit case where a claimed general
  statement fails, such as A − (B − C) ≠ (A − B) − C. A verified
  counterexample is a genuine **disproof** of the general claim. That is the
  one place where a computation settles a universal question outright.

A **mathematical proof** is a chain of reasoning from definitions and axioms
that covers every case, including the infinitely many that no program can
visit. In the Lumenary, proofs live in the lesson (H mode) and, where possible,
in Lean (F mode, reported separately in `lean-report.json`). The experiments are
there to build intuition, test conjectures, find counterexamples and check
calculations.

## Version pinning and Pyodide

The browser runs the experiments with **Pyodide v0.29.3**.
`compute/requirements.txt` pins the mathematical packages to exactly the
versions bundled in that release. The source of truth is
<https://cdn.jsdelivr.net/pyodide/v0.29.3/full/pyodide-lock.json>.

| Component | Pyodide 0.29.3 (browser) | Local pin (`requirements.txt`) | Match |
|---|---|---|---|
| Python | CPython 3.13.2 (wasm32/emscripten) | not pinned; verified with CPython 3.10.12 | **no** |
| sympy | 1.13.3 | 1.13.3 | yes |
| mpmath (sympy dependency) | 1.3.0 | 1.3.0 | yes |
| numpy | 2.2.5 | 2.2.5 | yes |
| pytest (local only, never loaded in the browser) | 8.3.5 in the lock file | 8.3.5 | yes |

All the exact package versions install on CPython 3.10, so the only mismatch is
the **interpreter**. Local verification ran on CPython 3.10.12, while the browser
uses CPython 3.13.2 compiled to WebAssembly. The experiments avoid behaviour
that differs between those versions. For example, the built-in `sum()` of
floats became compensated (more accurate) in Python 3.12, so
`exact_vs_numerical` uses an explicit loop for its "naive" float sum. The
report records the interpreter actually used (`"python"` field). To verify on
the same interpreter as the browser, create the venv with Python 3.13
(`python3.13 -m venv compute/.venv`); no other change is needed.

Note: the lock file's `info.version` field reads `0.28.0.dev0`, although it is
served from the v0.29.3 release (whose `package.json` says `0.29.3`). The package
versions above are taken from that v0.29.3 lock file.

When upgrading Pyodide, re-read the new lock file, update `requirements.txt`
to match, rebuild the venv and re-run `npm run verify:compute`.

## How the browser sandbox works (high level)

Learner code and experiments are **never executed on a server**. The site is
static, and all Python runs on the learner's own device:

1. A **Web Worker** (a background thread with no access to the page) loads
   Pyodide, CPython compiled to WebAssembly. Before running a file, it loads the
   packages listed in the experiment's `packages` field. The first load of
   SymPy can take noticeably longer than running the experiment itself.
2. The worker runs the experiment file (or the learner's code followed by an
   exercise's `tests`) and streams `stdout`/`stderr` back to the page as plain
   text.
3. If a run takes too long, the page **terminates the whole worker**, which is
   the only reliable way to stop runaway WebAssembly code, and starts a fresh
   one for the next run. Nothing persists between runs.
4. Pyodide's sandbox has no access to the learner's files and no
   general-purpose network sockets. The experiments are written not to need
   either.

The implementation lives in the website code under `src/`, which is outside
`compute/`. This section describes the contract the experiments are written
against.

**Measured in Pyodide itself (a one-off manual check, not part of
`verify.py`).** All 12 experiment files were run unchanged with the `pyodide`
0.29.3 npm package under Node 22 on the development machine (CPython 3.13.2,
packages fetched from the jsDelivr CDN). Every file printed output
**byte-for-byte identical** to local CPython 3.10.12 with the pinned packages.
Timings:

| Step | Time |
|---|---|
| Interpreter boot | about 1.0 s |
| Package download, first time only (numpy + sympy) | about 1.6 s |
| First `import numpy` | about 0.27 s |
| First `import sympy` | about 1.85 s |
| Each experiment's `main()` | at most about 120 ms (`sign_rules`); most under 40 ms |

Because the first `import sympy` alone is close to 2 s, the worker should
start an experiment's time limit **after** loading and importing its declared
`packages` (a warm-up step), or allow several seconds more for the first run.
Browser timings vary by device.

## Lesson exercises

`tests/test_lesson_exercises.py` checks every exercise with `"type": "python"`
in `content/math/lessons/*/exercises.json`:

- the first ```` ```python ```` block of the exercise's `solution` markdown,
  followed by its `tests`, must run without error in a fresh namespace;
- the untouched `starter`, followed by the same `tests`, **must raise**, so the
  tests really test something;
- the `starter` must be valid Python, so learners see a failing test rather
  than a syntax error;
- solution and tests must finish in under 2 s.

When no exercise files exist yet, these tests are skipped and the skip is
counted in the report. To try the checker on another folder, set
`LUMENARY_LESSONS_DIR`.

## The experiments

Every lesson has at least one experiment, so there are several hundred. Their ids start with the lesson slug in snake case (`point_set_topology_open_sets`). The authoritative list — with title, evidence types, lessons and whether each ran and passed its tests — is the generated `content/verification/compute-report.json`; the site's Math lab lists them by level, and each has its own page (`/[locale]/lab/<id>/`).

## Adding an experiment

1. Create `compute/experiments/<id>.py` in the format above. Use pure, documented
   functions and a `main()` that ends with an `Epistemic status:` paragraph.
2. Add `compute/tests/test_<id>.py` with unit tests for those functions,
   including boundary cases. Tests in that file are what `testsPassed` reports.
3. List the lesson or trail slugs that show it in `EXPERIMENT["lessons"]` (they
   must exist; the tests derive the known slugs from `content/`).
4. Reference it from the lesson or trail frontmatter (`compute: [<id>]`), check
   it with `npm run check:lesson -- <slug>`, run `npm run verify:compute`, and
   commit the regenerated report.
