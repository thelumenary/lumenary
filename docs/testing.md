# Testing strategy

The Lumenary has four layers of automated checks. Together they back every verification label shown on the site. None of them is a substitute for human review.

| Layer | Command | What it checks |
| --- | --- | --- |
| Formal | `npm run verify:lean` | `lake build` of the Lean library and exercises; axioms used by every declaration (`#print axioms`); no `sorry` in the library; each exercise elaborates and links to a compiled solution. Writes `content/verification/lean-report.json`. |
| Computational | `npm run verify:compute` | Runs every experiment as a script (time-limited), then runs pytest. The tests cover the pure functions, boundary cases, browser-safety rules (allowed imports, no I/O, output limits, determinism) and the Python exercises from the lesson files. Writes `content/verification/compute-report.json`. |
| Lessons | `npm test` (`tests/lesson-check.test.ts`), or `npm run check:lesson -- <slug>` for one lesson | Every lesson follows the lesson rules (`tests/lesson-rules.ts`: frontmatter and graph agree, required sections, viewpoint lenses from UG 1 upwards, known components and lenses, citations that exist in source, exercise schema) and is rendered with the real blocks and widgets, with exactly the message subset the page ships; unknown tags, crashing widget props, missing widget strings and KaTeX errors fail. `check:lesson` also builds the lesson's Lean modules, checks `#print axioms` and Lean conventions, and runs its experiments' tests and Python exercises. |
| Widgets | `npm test` (`tests/widgets-*.test.ts`) | Pure logic of every widget (parsers, geometry, simulations) and a server render of each widget with default, example and malformed props, in English and Arabic; the MDX examples in `docs/widgets/*.md` compile and render. |
| Content | `npm test` (Vitest) | Schemas for every JSON and MDX file; MDX compiles; the knowledge graph has unique ids, no dangling or self-referencing edges, acyclic required edges, no prerequisite at a higher level, and distinct optional edges; pathways respect prerequisite order; lessons cite only compiled Lean and passing experiments; trails return to real anchors; exercises are well formed with unique ids; translations keep their identifiers and record a `sourceHash`; registries cover all UN member states with consistent codes and language references; i18n catalogues have no orphan keys and keep their placeholders; answer parsing (regional numerals, set notation); graph layout has no overlaps. |
| Types and build | `npm run typecheck`, `npm run build` | TypeScript in strict mode, and a complete static export of every page in every locale. |

`npm run verify` runs all four and writes `content/verification/vitest-report.json`, which the Verification page reads.

## Browser end-to-end checks

`npm run test:e2e` serves the exported site and drives it in Chrome through Playwright (set `PW_CHANNEL=chromium` to use the bundled Chromium instead). It checks that:

- every main page renders in all six locales with the right `lang` (and `dir="rtl"` for Arabic) and no console errors;
- exercises give targeted feedback, accept answers in any order and in regional numerals, and reveal hints one at a time;
- the arrow diagram and knowledge graph respond to interaction;
- progress tracking stores nothing unless the learner opts in;
- Pyodide runs a lesson experiment and a Python exercise, and an infinite loop is stopped by the time limit. Set `E2E_SKIP_PYODIDE=1` to skip these, since they download Pyodide from the CDN.

The script writes `content/verification/e2e-report.json`.

## Manual and visual checks

`npm run screenshots` serves the exported site, opens key pages in Chrome through Playwright (light, dark, and right-to-left), saves screenshots for the evaluation package, and fails if any page logs a console error.

## What is not yet automated

- Running *every* experiment under Pyodide in CI and diffing its output against CPython. This was checked once by hand under Node, and the e2e suite runs one experiment in the browser.
- End-to-end coverage of every widget: only the exercises, the arrow diagram, the graph and the Python runner are exercised.
- Accessibility audits (axe or similar) and screen-reader testing.
- Link checking of external references.
