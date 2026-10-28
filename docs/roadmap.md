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

1. **Human review.** Recruit mathematicians and teachers to review the five lessons, seven trails and all exercises, and record each review.
2. **Translation review.** Ask fluent mathematics teachers to review the machine-drafted locales.
3. **Accessibility.** Run an accessibility audit and test with screen-reader users.
4. **Browser tests.** Automate end-to-end tests of the widgets and exercises, and run the Pyodide experiments in CI.
5. **Mathlib.** Add Mathlib as a dependency, using its cache, and cross-check the formal library against it.

## Phase C — Elementary and secondary expansion

Arithmetic, place value, fractions, measurement, geometry, algebra, logic, relations, equivalence relations, proof techniques, introductory probability and statistics. Each lesson must ship with its exercises, its verification and a review plan.

## Phase D — Undergraduate expansion

Calculus, linear algebra, real analysis, abstract algebra, topology, probability, numerical methods, introductory category theory (categories, functors, natural transformations, universal properties). Formal sections move to Mathlib.

## Phase E — Graduate expansion

Measure theory, functional analysis, graduate algebra, commutative algebra, representation theory, categorical logic and topos theory, plus specialised pathways.

## Phase F — Globalisation and educational review

Human-reviewed translations, terminology glossaries reviewed by mathematicians, regional adaptation of examples and the first periodic geographic-representation audit.

## Phase G — Research pathways

Reading literature, mathematical writing, formalising published results, computational reproducibility, open-problem evaluation, research ethics. Optional directions include quiver representations, path algebras and derived categories.
