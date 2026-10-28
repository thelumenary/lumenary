# Verification status

This file records what has actually been run and checked, and what has not. The machine-readable reports in `content/verification/` are the source of truth, and the site's Verification page reads them directly.

_Last updated: 2026-10-28, local run on Linux (Node 22.14, Python 3.10.12, Lean 4.35.0)._

## What was run, and the results

| Check | Command | Result |
| --- | --- | --- |
| Lean build (library and exercises) | `npm run verify:lean` | **Passed.** `lake build` succeeded with `leanprover/lean4:v4.35.0`, core Lean only, no Mathlib. 88 declarations: 59 proved here, 3 applying a core library theorem, 26 definitions. None depends on `sorry`. Axioms are recorded per declaration (`propext`, `Quot.sound`, and `Classical.choice` only where classical logic is used, e.g. `compl_inter`). The 7 exercises elaborate, each with one `sorry` placeholder and a compiled solution. |
| Python experiments | `npm run verify:compute` | **Passed.** All 12 experiments ran, and pytest reported 571 passed, 0 failed. This includes the 4 Python exercises from the lessons: each reference solution passes and each starter fails. |
| Pyodide parity | manual, once | All 12 experiment files were run under `pyodide@0.29.3` in Node and gave the same output as CPython. **Not automated.** |
| Content, graph, registries, i18n | `npm test` | **Passed:** 105 tests in 6 files. |
| TypeScript | `npm run typecheck` | **Passed** (strict). |
| Static build | `npm run build` | **Passed:** 1,203 pages across 6 locales. |
| Browser end-to-end | `npm run test:e2e` | **Passed:** 15 checks in Chrome via Playwright. These cover all main pages in every locale, exercises, regional numerals, hints, the arrow diagram, the graph, consent-gated progress, a Pyodide experiment, a Python exercise, and the time limit on an infinite loop. |
| Screenshots | `npm run screenshots` | 8 pages (light, dark, RTL) captured with no console errors. |

## What has not happened

- **No human review of any kind.** No mathematician, educator or translator has reviewed any lesson, trail, exercise, solution, glossary, registry entry or translation. Every lesson is labelled *AI-drafted · awaiting human review*.
- **No Mathlib.** Formal content uses core Lean 4 only, and Mathlib analogues are named without being checked.
- **No CI run.** `.github/workflows/ci.yml` is written but has not been run on GitHub Actions, so all results above are from a local machine.
- **No deployment.** The site has not been published anywhere.
- **No accessibility audit**, and no screen-reader testing.
- **No git commits** have been made. The repository was initialised and left for the maintainer to review and commit.
- **Not reconciled against cited sources:** the language registry's "top-100" seed list, and the 62 country entries flagged `needsReview`.

## Translations

| Locale | Interface | Lesson 1 (Collections) | Other lessons, trails, pages |
| --- | --- | --- | --- |
| en | canonical | canonical | canonical |
| es, ar, hi, zh-Hans, sw | machine draft (all keys) | machine draft, `sourceHash` d6fb718cfdb2 | English fallback with notice |

Machine drafts were produced by an AI system and are labelled as such on every page where they appear.

## Reproducing

```bash
npm install
python3 -m venv compute/.venv && compute/.venv/bin/pip install -r compute/requirements.txt
# Lean: install elan (it reads formal/lean-toolchain), or extract the official
# lean-4.35.0 release into .toolchain/ — scripts/verify-lean.mjs finds either.
npm run verify && npm run build && npm run test:e2e
```
