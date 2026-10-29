# Verification status

This file records what has actually been run and checked, and what has not. The machine-readable reports in `content/verification/` are the source of truth, and the site's Verification page reads them directly.

_Last updated: 2026-10-29, local run on Linux (Node 22.14, Python 3.10.12, Lean 4.35.0, Mathlib v4.35.0)._

## What was run, and the results

| Check | Command | Result |
| --- | --- | --- |
| Lean build (library and exercises) | `npm run verify:lean` | **Passed.** `lake build Lumenary LumenaryExercises` succeeded with `leanprover/lean4:v4.35.0` and Mathlib `v4.35.0` (commit `56a005855ea1`). 380 files; **3,666 declarations**: 2,139 proved here, 716 applying a library theorem (core Lean or Mathlib), 811 definitions; 2,603 in modules built on Mathlib and 1,063 in core-Lean modules (every Kindergarten–Grade 8 module). **None depends on `sorry`.** Axioms are recorded per declaration. The **349 Lean exercises** elaborate, each with `sorry` placeholders and a compiled solution. (The library had been built module by module while lessons were written; CI rebuilds it from the Mathlib cache.) |
| Lesson-by-lesson checks | `npm run check:lesson -- <slug>` | Passed for every one of the 200 lessons when it was written: render with the real components, Lean conventions and `#print axioms`, experiment tests, browser-safety checks and Python exercises. |
| Python experiments | `npm run verify:compute` | **Passed.** All **368 experiments** ran, and pytest reported **5,993 passed, 0 failed**. This includes every Python exercise in the lessons: each reference solution passes and each starter fails. The same suite also passed on CPython 3.13.1, the interpreter version Pyodide uses, which is what CI runs. |
| Content, lessons, widgets, graph, registries, i18n | `npm test` | **Passed: 2,638 tests in 13 files.** Every lesson follows the lesson rules (including the viewpoint requirement from UG 1 upwards) and renders with the real blocks and widgets, with exactly the widget strings its page ships and no KaTeX errors; the knowledge graph (200 topics, all implemented) is acyclic and level-monotone; 12 pathways respect prerequisites; all 30 widgets pass their logic and render tests. |
| TypeScript | `npm run typecheck` | **Passed** (strict). |
| Static build | `npm run build` | **Passed:** 2,967 HTML pages (1.9 GB), about 110 s on a 20-core machine. Lesson, practice and worksheet pages exist in English and in each locale with a translation (Collections in all six); lab and formal detail pages in English. |
| Browser end-to-end | `npm run test:e2e` | **Passed: 15 checks** in Chrome via Playwright: main pages in every locale, exercises, regional numerals, hints, the arrow diagram, the graph, consent-gated progress, a Pyodide experiment, a Python exercise, and the time limit on an infinite loop. |
| Browser crawl (manual, once) | ad hoc Playwright script | All **231** pages visited — every English lesson and Wonder Trail plus samples of the lab, formal, practice and localised pages — loaded with **no console errors** (which would include React hydration errors). |
| Screenshots | `npm run screenshots` | 8 pages (light, dark, RTL) captured with no console errors. |

## What has not happened

- **No human review of any kind.** No mathematician, educator or translator has reviewed any lesson, trail, exercise, solution, proof, Lean statement, glossary, registry entry or translation. All 200 lessons are labelled *AI-drafted · awaiting human review*. The lesson authors flagged specific historical attributions, recent research results and literature citations they were less sure of; these are the first things a reviewer should check.
- **Formal coverage is partial.** Lessons formalise what they cite; at graduate and research level that is often a key lemma, special case or definition, and many central theorems are cited from Mathlib or not formalised at all. Each lesson's formal section says exactly what is and is not formalised. A compiled statement is only as faithful as its wording, which no human has checked.
- **Pyodide parity is not automated.** Experiments are tested under CPython; one experiment and one exercise run in Pyodide in the e2e suite. A few experiments print floating-point values whose last digits may differ in the browser.
- **Widgets were checked by their authors' own scratch harnesses and by server-render tests**, and every lesson page by the browser crawl above, but there has been no systematic visual or usability review, and no accessibility audit or screen-reader testing.
- **Not reconciled against cited sources:** the language registry's "top-100" seed list, and the country entries flagged `needsReview`.

## Translations

| Locale | Interface | Lesson 1 (Collections) | Other lessons, trails, pages |
| --- | --- | --- | --- |
| en | canonical | canonical | canonical |
| es, ar, hi, zh-Hans, sw | machine draft (all keys) | machine draft | lessons offered in English (marked "EN"); trails and pages in English with a notice |

Machine drafts were produced by an AI system and are labelled as such on every page where they appear.

## Reproducing

```bash
npm install
python3 -m venv compute/.venv && compute/.venv/bin/pip install -r compute/requirements.txt
# Lean: install elan (it reads formal/lean-toolchain), or extract the official
# lean-4.35.0 release into .toolchain/ — scripts/verify-lean.mjs finds either.
(cd formal && lake exe cache get)    # prebuilt Mathlib
npm run verify && npm run build && npm run test:e2e
```
