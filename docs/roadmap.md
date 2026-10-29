# Roadmap

The Lumenary is built in reviewable increments. Small and trustworthy comes before large and unverified.

## Phase A — Architecture ✅ (this repository)

Repository structure · website architecture · brand and design system · subject taxonomy and knowledge graph · set-theory and category-theory progressions · Wonder Trail schema · language and geographic registries · testing strategy · licensing proposal · this roadmap.

## Phase B — Working vertical slice ✅ (first version; awaiting human review)

- Homepage, curriculum browser, knowledge graph, lesson reader, Wonder Trails, math lab, formal lab, practice, optional progress, educator resources, About, Contribute, language selector and registry pages
- Lessons: Collections → Sets → Integers → Functions → Composition
- Wonder Trails toward algebraic structures, modular arithmetic, quotients, foundations, countability and category theory
- Compiling Lean proofs (core Lean 4), tested Python experiments, automated tests, reproducible static build
- Six demo locales across language families, scripts and both writing directions

**Next steps for Phase B:**

1. **Human review.** Recruit mathematicians and teachers to review the lessons, trails and exercises, and record each review.
2. **Translation review.** Ask fluent mathematics teachers to review the machine-drafted locales.
3. **Accessibility.** Run an accessibility audit and test with screen-reader users.
4. **Browser tests.** Automate end-to-end tests of the widgets and exercises, and run the Pyodide experiments in CI.
5. ~~**Mathlib.** Add Mathlib as a dependency, using its cache.~~ Done: Mathlib `v4.35.0` is a pinned dependency.

## Phases C, D and E — first drafts of the whole curriculum ✅ (AI-drafted; awaiting human review)

Every topic in the knowledge graph now has a lesson — 201 in all, from counting in kindergarten to research directions — each with exercises, a Lean module and at least one tested Python experiment. The graph was extended so that the higher levels are not seen only through set theory and category theory: geometry and topology now have their own thread from K–2 to research (non-Euclidean and projective geometry, surfaces, knots, differential forms, manifolds, Riemannian geometry, Lie groups, homotopy theory, characteristic classes, Riemann surfaces, low-dimensional topology, geometric group theory, symplectic and Kähler geometry), alongside analysis (harmonic analysis, PDE, dynamics, ergodic theory, geometric analysis), number theory (analytic, arithmetic geometry, Langlands), probability (random geometry) and physics (relativity, gauge theory). Every lesson from early undergraduate onwards has a required *Viewpoints* section, and four specialisation pathways were added. About thirty generic widgets and twelve new Wonder Trails support the lessons. Formal sections moved to Mathlib from Grade 9 onwards.

After the first review of the live site (October 2026): the three cat guides now appear at every level (and can be hidden from the header); every lesson was checked against new safety and geographic-balance rules, so examples no longer include dangerous actions and everyday settings mix the Global North and South; a research lesson on AI-assisted mathematical research records the dated results of 2021–2026; and headings use Source Serif 4.

**What these drafts are not:** reviewed. Every lesson is labelled *AI-drafted*. At graduate and research level many central theorems are stated with references or proved in outline, and formal sections often formalise a key lemma rather than the headline result; each lesson says which.

**Next steps:**

1. **Human review, level by level.** Recruit mathematicians and teachers to review lessons, exercises, proofs, history and attributions, starting with K–8 and with the claims agents flagged as uncertain. Record each review.
2. **Missing widgets** noted by authors: box plots, tree diagrams, scatter plots with line fitting, directed graphs (state machines, blueprints, Cayley graphs), and a grid robot for young children.
3. **Translations** of the lessons themselves (only Collections is translated), starting where the interface is already translated.
4. **Deepen the formal library** where Mathlib grows (e.g. plane graphs, degree theory, characteristic classes), and contribute upstream.

## Phase F — Globalisation and educational review

Human-reviewed translations, terminology glossaries reviewed by mathematicians, regional adaptation of examples and the first periodic geographic-representation audit.

## Phase G — Research pathways

First-draft orientation lessons now exist for the research skills (reading the literature, mathematical writing, formalising published mathematics, computational reproducibility, experimental mathematics, research ethics) and for twenty-two research directions across topology, geometry, analysis, number theory, probability, combinatorics, physics, logic and category theory. Still to do: advanced laboratories (larger formalisation and computation projects), curated reading lists checked by specialists, and regular updates of the "known versus open" sections as the literature moves.
