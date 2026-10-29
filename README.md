# The Lumenary

**One mathematics. Many languages. Every nation.**
**Understand. Prove. Compute. Verify.**

The Lumenary is a free, open-source, Christian-inspired education platform. Its first subject, **Lumenary Math**, runs from kindergarten counting to first-year graduate mathematics, with optional research pathways. Every lesson is taught in three connected modes: **H**uman (intuition and proof), **F**ormal (Lean 4 + Mathlib) and **C**omputational (Python).

Every topic in the curriculum now has a **first-draft lesson**. None has yet been reviewed by a human mathematician or teacher — see the honesty notes below.

## What exists today

| Area | Status |
| --- | --- |
| Website | Static Next.js 16 site at [lumenary.academy](https://lumenary.academy), 6 demo interface locales (en, es, ar RTL, hi, zh-Hans, sw), light/dark themes, works without accounts |
| Lessons | **200 lessons**, one for every topic in the knowledge graph, from K–2 counting and shapes to graduate topics and research directions; each with exercises, a Lean module and tested Python experiments |
| Viewpoints | From early undergraduate level every lesson shows its subject through several mathematicians' eyes — topologist, geometer, analyst, algebraist, number theorist, probabilist, logician, physicist — as well as through set theory and category theory |
| Wonder Trails | 19 optional trails, toward algebraic structures, modular arithmetic, quotients, foundations, countability, category theory, topology, curvature, infinite sums, primes, random walks, computability and planetary orbits |
| Interactive explorations | About 30 generic widgets (place value, fractions, area, data, functions and calculus, vector fields, the complex plane, matrices, graphs, truth tables, probability, polyhedra and the Euler characteristic, curved triangles, surface gluing, knots, winding numbers, curvature) plus commutative diagrams; documented in `docs/widgets/` |
| Knowledge graph | 200 topics across 8 levels and 10 subjects, required prerequisites (acyclic, checked automatically), optional discovery edges, 12 learning pathways (including geometry and topology, analysis and dynamics, algebra and number theory, mathematical physics) |
| Formal library | Lean 4.35.0 with Mathlib `v4.35.0` (K–8 modules use core Lean only): 3,666 declarations in 202 modules, none depending on `sorry`, each recorded with its axioms, provenance (proved here / applies a library theorem / definition) and foundation; 349 Lean exercises |
| Computation | 368 Python experiments that run in the browser (Pyodide, sandboxed Web Worker), tested by 5,993 pytest tests |
| Practice | Exercises with progressive hints, targeted feedback, worked solutions and in-browser Python tests; no scores, streaks or rankings |
| Registries | Language registry (BCP 47) and a country registry covering all 193 UN member states plus the 2 observer states |
| Educators | Printable worksheets with answer keys, curriculum map, evaluation package |

The figures on the website come from generated reports (`content/verification/*.json`), not from hand-written claims.

### Honesty notes

- **No content has been reviewed by a human mathematician, educator or translator.** All 200 lessons were drafted with AI assistance and are labelled *AI-drafted · awaiting human review*. At graduate and research level many central theorems are stated with references or proved in outline; each lesson says which.
- A lesson shows **Formally verified** only if every Lean declaration it cites is in the latest Lean build report, compiled, and uses no `sorry`. Formal sections often formalise a key lemma, special case or definition rather than the headline theorem, and each says precisely what is and is not formalised.
- A lesson shows **Computationally tested** only if its experiments ran and passed their tests. Experiments label their evidence (exact, numerical, statistical, …); evidence is never presented as proof.
- Non-English interface strings and the translated first lesson are **machine-generated drafts**, labelled as such. Other lessons exist in English only; in other locales they are linked in English and marked "EN". Six demo locales are not global coverage.
- See [`docs/verification-status.md`](docs/verification-status.md) for exactly what was run and what was not.

## Quick start

Requirements: Node ≥ 22, Python ≥ 3.10, a Lean 4 toolchain (via [elan](https://github.com/leanprover/elan), or the official release archive extracted to `.toolchain/`), and about 8 GB of disk for Mathlib's prebuilt files.

```bash
npm install
python3 -m venv compute/.venv && compute/.venv/bin/pip install -r compute/requirements.txt

(cd formal && lake exe cache get)   # prebuilt Mathlib
npm run verify:lean       # lake build + write content/verification/lean-report.json
npm run verify:compute    # run experiments + pytest, write compute-report.json
npm run typecheck
npm test                  # lessons (render + rules), widgets, graph, registry, i18n and parser tests
npm run check:lesson -- integers   # everything for one lesson

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
- [Lesson authoring guide](docs/authoring-guide.md) · [Widgets](docs/widgets/)
- [Curriculum taxonomy](docs/curriculum/taxonomy.md) · [Viewpoints](docs/curriculum/viewpoints.md) · [Geometry and topology progression](docs/curriculum/geometry-topology-progression.md) · [Set theory progression](docs/curriculum/set-theory-progression.md) · [Category theory progression](docs/curriculum/category-theory-progression.md) · [Pathways](docs/curriculum/pathways.md) · [Wonder Trails](docs/curriculum/wonder-trails.md)
- [Formal mathematics](docs/formal.md) · [Computation](docs/compute.md)
- [Language registry](docs/i18n/language-registry.md) · [Translation workflow](docs/i18n/translation-workflow.md) · [Geography](docs/geography.md)
- [Licensing](docs/licensing.md) · [Roadmap](docs/roadmap.md) · [Verification status](docs/verification-status.md)

## Licences

Software, Lean proofs and Python experiments: [Apache-2.0](LICENSE). Educational content (text, exercises, diagrams): [CC BY-SA 4.0](LICENSE-CONTENT). See [docs/licensing.md](docs/licensing.md).

The Lumenary is an independent project. No institutional endorsement is implied.
