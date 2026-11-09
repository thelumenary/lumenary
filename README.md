# The Lumenary

**One mathematics. Many languages. Every nation.**

The Lumenary is a Christian-inspired education project in three divisions. This repository holds its website, [lumenary.academy](https://lumenary.academy), and the first subject of Lumenary Scientia, **Lumenary Math**.

## The three divisions

| Division | What it is | Status |
| --- | --- | --- |
| **Lumenary Scientia** | The sciences, free and open source for ever: no accounts, no advertising, no paid tiers | Mathematics available: **[Lumenary Math](content/math/README.md)**. Computer science, electrical engineering, physics, chemistry, biology and other sciences pending |
| **Lumenary Lingua** | Languages, each taught through a language the learner already knows | Pending |
| **Lumenary Prep** | Exam preparation as a paid service: one price per course, paid once, for lifetime access | At [prep.lumenary.academy](https://prep.lumenary.academy), built in a separate repository |

Paying for Prep is never needed to use Scientia, and Scientia stays free and open source. The site's [divisions page](https://lumenary.academy/en/divisions/) (`content/pages/divisions/en.mdx`) has the details.

## Lumenary Math

Mathematics from kindergarten counting to the first year of graduate school, every lesson taught three ways: human (intuition and proof), formal (Lean 4 + Mathlib) and computational (Python). Every topic in the curriculum has a first-draft lesson; none has yet been reviewed by a human mathematician or teacher.

**[Lumenary Math's README](content/math/README.md)** covers what exists today, the honesty notes, the Lean and Python toolchain and the curriculum documentation.

## Quick start

Requirements: Node ≥ 22.

```bash
npm install
npm run dev               # http://localhost:3000
npm run typecheck
npm test                  # lessons, widgets, graph, registry, i18n and parser tests
npm run build             # static export to out/
npm start                 # serve out/ at http://localhost:4173
npm run test:e2e          # browser checks against out/ (Playwright)
```

The Lean and Python checks behind Lumenary Math need their own toolchains: see [its quick start](content/math/README.md#quick-start).

## Repository layout

```
content/
  math/              Lumenary Math: knowledge graph, lessons, trails (see its README)
  pages/             About, Divisions, Contribute, Educators, evaluation package (MDX)
  registry/          languages.json, countries.json, glossaries/
  verification/      generated reports — never edit by hand
formal/              Lean 4 project for Lumenary Math
compute/             Python experiments for Lumenary Math, tests, verify.py, pinned requirements
src/
  app/[locale]/      routes (static export): the front page (the three divisions), math/, and the project pages
  components/        UI, lesson blocks, widgets, graph, exercises
  i18n/              locale config and message catalogues
  lib/               schemas (zod), content loaders, MDX, layout, sandbox
scripts/             verification, screenshots, static server, source hashes
tests/               vitest suites
docs/                architecture, curriculum, i18n, design, testing, licensing, roadmap
```

## Documentation

- [Architecture](docs/architecture.md) · [Design system](docs/design-system.md) · [Testing strategy](docs/testing.md)
- [Language registry](docs/i18n/language-registry.md) · [Translation workflow](docs/i18n/translation-workflow.md) · [Geography](docs/geography.md)
- [Licensing](docs/licensing.md) · [Roadmap](docs/roadmap.md) · [Contributing](CONTRIBUTING.md)
- Lumenary Math's own documentation is listed in [its README](content/math/README.md#documentation).

## Licences

Software, Lean proofs and Python experiments: [Apache-2.0](LICENSE). Educational content (text, exercises, diagrams): [CC BY-SA 4.0](LICENSE-CONTENT). See [docs/licensing.md](docs/licensing.md).

The Lumenary is an independent project. No institutional endorsement is implied.
