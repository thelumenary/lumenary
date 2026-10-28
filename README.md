# The Lumenary

**One mathematics. Many languages. Every nation.**
**Understand. Prove. Compute. Verify.**

The Lumenary is a free, open-source, Christian-inspired education platform. Its first subject, **Lumenary Math**, is planned to run from kindergarten counting to first-year graduate mathematics, with optional research pathways. Every suitable idea is taught in three connected modes: **H**uman (intuition and proof), **F**ormal (Lean 4) and **C**omputational (Python).

This repository holds a **working vertical slice**, not the finished curriculum. What it contains is listed below, along with what has and has not been verified.

## What exists today

| Area | Status |
| --- | --- |
| Website | Static Next.js 16 site, 6 demo locales (en, es, ar RTL, hi, zh-Hans, sw), light/dark themes, works without accounts |
| Lessons | 5 lessons: Collections → Sets → Integers → Functions → Composition |
| Wonder Trails | 7 optional trails toward algebraic structures, modular arithmetic, quotients, set-theoretic foundations, countability and category theory |
| Interactive explorations | 12 (sorting game, Venn explorer, number line, arrow diagrams, composition machines, clock lab, diagonal machine, …) |
| Knowledge graph | Every level from K–2 to research, with required prerequisites (acyclic, checked automatically), optional discovery edges and 8 learning pathways, browsable as an interactive map or a list |
| Formal library | Core Lean 4 (v4.35.0, no Mathlib yet): the report records every declaration with its axioms and whether it applies a library theorem or is proved here; 7 Lean exercises |
| Computation | 12 Python experiments that run in the browser (Pyodide, sandboxed Web Worker) and are tested with pytest |
| Practice | Exercises with progressive hints, targeted feedback, worked solutions and in-browser Python tests; no scores, streaks or rankings |
| Registries | Language registry (BCP 47) and a country registry covering all 193 UN member states plus the 2 observer states |
| Educators | Printable worksheets with answer keys, curriculum map, classroom activities, evaluation package |

The figures on the website come from generated reports (`content/verification/*.json`), not from hand-written claims.

### Honesty notes

- **No content has been reviewed by a human mathematician, educator or translator.** Every lesson is labelled *AI-drafted · awaiting human review*.
- A lesson shows **Formally verified** only if every Lean declaration it cites is in the latest Lean build report, compiled, and uses no `sorry`. It shows **Computationally tested** only if its experiments ran and passed their tests.
- Non-English interface strings and the translated first lesson are **machine-generated drafts**, labelled as such. Six demo locales are not global coverage.
- See [`docs/verification-status.md`](docs/verification-status.md) for exactly what was run and what was not.

## Quick start

Requirements: Node ≥ 22, Python ≥ 3.10, and a Lean 4 toolchain (via [elan](https://github.com/leanprover/elan), or the official release archive extracted to `.toolchain/`).

```bash
npm install
python3 -m venv compute/.venv && compute/.venv/bin/pip install -r compute/requirements.txt

npm run verify:lean       # lake build + write content/verification/lean-report.json
npm run verify:compute    # run experiments + pytest, write compute-report.json
npm run typecheck
npm test                  # content, graph, registry, i18n and parser tests

npm run dev               # http://localhost:3000
npm run build             # static export to out/
npm start                 # serve out/ at http://localhost:4173
```

`npm run verify` runs all the checks and writes `content/verification/vitest-report.json` as well.

## Repository layout

```
content/
  math/graph/        graph.json (levels, subjects, topics), pathways.json
  math/lessons/<slug>/   en.mdx (canonical), <locale>.mdx, exercises.json, exercises.<locale>.json
  math/trails/<slug>/    en.mdx
  pages/             About, Contribute, Educators, evaluation package (MDX)
  registry/          languages.json, countries.json, glossaries/
  verification/      generated reports — never edit by hand
formal/              Lean 4 project (lakefile.toml, Lumenary/, LumenaryExercises/)
compute/             Python experiments, tests, verify.py, pinned requirements
src/
  app/[locale]/      routes (static export)
  components/        UI, lesson blocks, widgets, graph, exercises
  i18n/              locale config and message catalogues
  lib/               schemas (zod), content loaders, MDX, layout, sandbox
scripts/             verification, screenshots, static server, source hashes
tests/               vitest suites
docs/                architecture, curriculum, i18n, design, testing, licensing, roadmap
```

## Documentation

- [Architecture](docs/architecture.md) · [Design system](docs/design-system.md) · [Testing strategy](docs/testing.md)
- [Curriculum taxonomy](docs/curriculum/taxonomy.md) · [Set theory progression](docs/curriculum/set-theory-progression.md) · [Category theory progression](docs/curriculum/category-theory-progression.md) · [Wonder Trails](docs/curriculum/wonder-trails.md)
- [Formal mathematics](docs/formal.md) · [Computation](docs/compute.md)
- [Language registry](docs/i18n/language-registry.md) · [Translation workflow](docs/i18n/translation-workflow.md) · [Geography](docs/geography.md)
- [Licensing](docs/licensing.md) · [Roadmap](docs/roadmap.md) · [Verification status](docs/verification-status.md)

## Licences

Software, Lean proofs and Python experiments: [Apache-2.0](LICENSE). Educational content (text, exercises, diagrams): [CC BY-SA 4.0](LICENSE-CONTENT). See [docs/licensing.md](docs/licensing.md).

The Lumenary is an independent project. No institutional endorsement is implied.
