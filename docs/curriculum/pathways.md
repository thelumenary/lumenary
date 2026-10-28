# Learning pathways

<!-- Tables in this document were generated from content/math/graph/graph.json and pathways.json when it was written. Update them whenever the graph changes. -->

Pathways are ordered selections of milestones through the knowledge graph, defined in `content/math/graph/pathways.json`. They support learners with different starting points and goals without changing the graph itself.

## How pathways work

- **Milestones are waypoints, not a complete syllabus.** A milestone's required prerequisites must still be met, even when they are not listed as milestones; the site can compute them from the graph. Two pathways can share milestones.
- **Order respects prerequisites.** No milestone is a (transitive) prerequisite of an earlier milestone. Equivalently, the milestone order is a linear extension of the prerequisite order restricted to the milestones (see `taxonomy.md`). Other orders that respect the prerequisites are equally valid.
- **Pathways never make optional material compulsory.** Wonder Trails and discovery edges remain optional on every pathway.
- **Programmes differ.** School systems, universities and graduate programmes order and weight topics differently. In particular, graduate programmes vary widely in what they require of a first-year student. The graduate and research pathways are therefore offered as adaptable examples, and learners and teachers are encouraged to substitute topics to suit their programme or specialisation.

| Id | Title | Milestones |
|---|---|---|
| `k12-conventional` | Conventional K–12 progression | 20 |
| `accelerated-secondary` | Accelerated secondary progression | 18 |
| `adult-beginner` | Adult beginner pathway | 15 |
| `math-major` | Undergraduate mathematics major | 20 |
| `cs-formal-methods` | Computer science and formal methods | 18 |
| `applied-math` | Applied mathematics | 16 |
| `graduate-prep` | Graduate preparation | 18 |
| `research-prep` | Research preparation | 13 |

## Conventional K–12 progression (`k12-conventional`)

**Audience:** School learners from kindergarten to the end of secondary school, and the teachers and families supporting them.

A steady route through school mathematics: counting and collections, arithmetic and fractions, sets and integers, functions and algebra, geometry and trigonometry, probability, and introductory calculus. Optional Wonder Trails branch off at every stage but are never required.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | K–2 | `math.found.collections` | Collections | Foundations |
| 2 | K–2 | `math.number.counting` | Counting | Number |
| 3 | K–2 | `math.number.addition-subtraction` | Addition, subtraction and place value to 100 | Number |
| 4 | K–2 | `math.geom.shapes` | Shapes | Geometry & Topology |
| 5 | 3–5 | `math.found.sets` | Sets | Foundations |
| 6 | 3–5 | `math.number.whole-number-arithmetic` | Whole-number arithmetic | Number |
| 7 | 3–5 | `math.number.fractions` | Fractions and decimals | Number |
| 8 | 3–5 | `math.geom.area-angles` | Area, perimeter and angles | Geometry & Topology |
| 9 | 6–8 | `math.number.integers` | Integers | Number |
| 10 | 6–8 | `math.number.rational-numbers` | Rational numbers | Number |
| 11 | 6–8 | `math.found.functions` | Functions | Foundations |
| 12 | 6–8 | `math.algebra.linear-relationships` | Linear relationships and simultaneous equations | Algebra |
| 13 | 6–8 | `math.prob.probability-intro` | Probability | Probability & Statistics |
| 14 | 6–8 | `math.geom.pythagorean-theorem` | The Pythagorean theorem | Geometry & Topology |
| 15 | 9–12 | `math.algebra.quadratics` | Quadratic equations and functions | Algebra |
| 16 | 9–12 | `math.geom.euclidean-geometry` | Euclidean geometry and proof | Geometry & Topology |
| 17 | 9–12 | `math.geom.trigonometry` | Trigonometry | Geometry & Topology |
| 18 | 9–12 | `math.analysis.functions-and-graphs` | Functions and their graphs (precalculus) | Analysis |
| 19 | 9–12 | `math.prob.probability-rules` | Conditional probability and independence | Probability & Statistics |
| 20 | 9–12 | `math.analysis.intro-calculus` | Introductory calculus | Analysis |

## Accelerated secondary progression (`accelerated-secondary`)

**Audience:** Secondary-school learners who are ready to move faster and further, including those preparing for olympiads or early university study.

Builds proof and structure early: logic and proof, countability and Cantor's diagonal argument, composition and structure-preserving maps, a first universal property, then calculus, linear algebra and algebraic structures. Acceleration should deepen understanding, not merely cover topics sooner.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | 6–8 | `math.number.integers` | Integers | Number |
| 2 | 6–8 | `math.found.functions` | Functions | Foundations |
| 3 | 6–8 | `math.found.equivalence-relations` | Relations, equivalence relations and partitions | Foundations |
| 4 | 9–12 | `math.found.propositional-logic` | Propositional logic and truth tables | Foundations |
| 5 | 9–12 | `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | Foundations |
| 6 | 9–12 | `math.number.real-numbers` | Real numbers and irrationality | Number |
| 7 | 9–12 | `math.algebra.quadratics` | Quadratic equations and functions | Algebra |
| 8 | 9–12 | `math.cat.composition` | Composition | Category Theory |
| 9 | 9–12 | `math.found.countability` | Countability and Cantor's diagonal argument | Foundations |
| 10 | 9–12 | `math.discrete.combinatorics` | Combinatorics | Discrete Mathematics |
| 11 | 9–12 | `math.geom.trigonometry` | Trigonometry | Geometry & Topology |
| 12 | 9–12 | `math.analysis.functions-and-graphs` | Functions and their graphs (precalculus) | Analysis |
| 13 | 9–12 | `math.analysis.intro-calculus` | Introductory calculus | Analysis |
| 14 | 9–12 | `math.cat.structure-preserving-maps` | Structure-preserving maps: homomorphisms and isomorphisms | Category Theory |
| 15 | 9–12 | `math.cat.intro-universal-properties` | Products by maps: a first universal property | Category Theory |
| 16 | UG 1 | `math.analysis.single-variable-calculus` | Calculus of one variable | Analysis |
| 17 | UG 1 | `math.algebra.linear-algebra` | Linear algebra | Algebra |
| 18 | UG 1 | `math.algebra.algebraic-structures` | Algebraic structures: monoids, groups and rings | Algebra |

## Adult beginner pathway (`adult-beginner`)

**Audience:** Adults returning to mathematics, or meeting it properly for the first time, at any age and with any prior experience.

Starts from whole-number arithmetic without assuming school knowledge is fresh, and moves at an adult pace through fractions, integers, sets and logic, functions and equations, everyday statistics and probability, and a first experience of proof and composition. No timed work and no prerequisite shame: revisit any topic as often as needed.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | 3–5 | `math.number.whole-number-arithmetic` | Whole-number arithmetic | Number |
| 2 | 3–5 | `math.number.fractions` | Fractions and decimals | Number |
| 3 | 6–8 | `math.number.integers` | Integers | Number |
| 4 | 6–8 | `math.number.rational-numbers` | Rational numbers | Number |
| 5 | 6–8 | `math.number.ratios-proportions` | Ratios, rates and proportional reasoning | Number |
| 6 | 3–5 | `math.found.sets` | Sets | Foundations |
| 7 | 3–5 | `math.found.logic-statements` | True, false, and, or, not | Foundations |
| 8 | 6–8 | `math.found.functions` | Functions | Foundations |
| 9 | 6–8 | `math.algebra.variables-expressions` | Variables and algebraic expressions | Algebra |
| 10 | 6–8 | `math.algebra.linear-equations` | Linear equations and inequalities | Algebra |
| 11 | 6–8 | `math.prob.statistics-intro` | Statistics: centre, spread and distributions | Probability & Statistics |
| 12 | 6–8 | `math.prob.probability-intro` | Probability | Probability & Statistics |
| 13 | 9–12 | `math.found.propositional-logic` | Propositional logic and truth tables | Foundations |
| 14 | 9–12 | `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | Foundations |
| 15 | 9–12 | `math.cat.composition` | Composition | Category Theory |

## Undergraduate mathematics major (`math-major`)

**Audience:** Undergraduates studying mathematics as a main subject, and independent learners following an equivalent programme.

A typical core for a mathematics degree: proof, calculus, linear algebra, real and complex analysis, abstract algebra with quotients and Galois theory, topology, number theory, graph theory, a first course in categories and functors, and mathematical writing. Degree programmes differ in order and emphasis; this is one coherent ordering, not the only one.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | 9–12 | `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | Foundations |
| 2 | 9–12 | `math.found.countability` | Countability and Cantor's diagonal argument | Foundations |
| 3 | UG 1 | `math.analysis.single-variable-calculus` | Calculus of one variable | Analysis |
| 4 | UG 1 | `math.algebra.linear-algebra` | Linear algebra | Algebra |
| 5 | UG 1 | `math.algebra.algebraic-structures` | Algebraic structures: monoids, groups and rings | Algebra |
| 6 | UG 1 | `math.analysis.multivariable-calculus` | Multivariable and vector calculus | Analysis |
| 7 | UG 1 | `math.found.order-theory` | Orders, lattices and well-orders | Foundations |
| 8 | UG 1 | `math.cat.categories` | Categories | Category Theory |
| 9 | UG 2 | `math.analysis.real-analysis` | Real analysis | Analysis |
| 10 | UG 2 | `math.algebra.groups` | Groups | Algebra |
| 11 | UG 2 | `math.algebra.rings` | Rings, ideals and fields | Algebra |
| 12 | UG 2 | `math.algebra.quotients` | Quotient groups and quotient rings | Algebra |
| 13 | UG 2 | `math.geom.point-set-topology` | Metric spaces and point-set topology | Geometry & Topology |
| 14 | UG 2 | `math.analysis.complex-analysis` | Complex analysis | Analysis |
| 15 | UG 2 | `math.algebra.fields-galois` | Fields and Galois theory | Algebra |
| 16 | UG 2 | `math.number.elementary-number-theory` | Number theory | Number |
| 17 | UG 1 | `math.cat.functors` | Functors | Category Theory |
| 18 | UG 2 | `math.geom.curves-surfaces` | Differential geometry of curves and surfaces | Geometry & Topology |
| 19 | UG 2 | `math.discrete.graph-theory` | Graph theory | Discrete Mathematics |
| 20 | UG 2 | `math.found.mathematical-writing` | Mathematical writing | Foundations |

## Computer science and formal methods (`cs-formal-methods`)

**Audience:** Learners heading towards theoretical computer science, programming-language theory, verification or proof engineering.

Logic and proof alongside programming, then algorithms, discrete mathematics, Lean, computability and complexity, the λ-calculus and type theory, a categorical view of structure, and formal methods. Formal proofs are introduced gradually, and a machine-checked proof is only claimed when it has actually been checked.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | 3–5 | `math.found.logic-statements` | True, false, and, or, not | Foundations |
| 2 | 6–8 | `math.comp.programming-intro` | Programming for mathematics | Computation |
| 3 | 9–12 | `math.found.propositional-logic` | Propositional logic and truth tables | Foundations |
| 4 | 9–12 | `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | Foundations |
| 5 | 9–12 | `math.comp.algorithms-and-efficiency` | Algorithms, correctness and efficiency | Computation |
| 6 | 9–12 | `math.comp.intro-lean` | First steps in Lean | Computation |
| 7 | UG 1 | `math.found.first-order-logic` | First-order logic | Foundations |
| 8 | 9–12 | `math.discrete.combinatorics` | Combinatorics | Discrete Mathematics |
| 9 | 9–12 | `math.discrete.graph-basics` | Graphs | Discrete Mathematics |
| 10 | UG 1 | `math.comp.algorithm-design` | Algorithm design and analysis | Computation |
| 11 | UG 1 | `math.comp.formal-proof-lean` | Formalising mathematics in Lean and Mathlib | Computation |
| 12 | UG 2 | `math.comp.computability` | Computability | Computation |
| 13 | UG 2 | `math.comp.lambda-calculus` | The λ-calculus | Computation |
| 14 | UG 2 | `math.comp.complexity-theory` | Computational complexity | Computation |
| 15 | UG 2 | `math.found.type-theory` | Type theory and propositions as types | Foundations |
| 16 | UG 1 | `math.algebra.algebraic-structures` | Algebraic structures: monoids, groups and rings | Algebra |
| 17 | UG 1 | `math.cat.categories` | Categories | Category Theory |
| 18 | Grad | `math.comp.formal-methods` | Formal methods | Computation |

## Applied mathematics (`applied-math`)

**Audience:** Learners aiming at science, engineering, data, economics, biology or computation, who want mathematics they can use and trust.

Functions and calculus, linear algebra and differential equations, probability and statistics, numerical methods and analysis, partial differential equations, optimisation, mechanics, information theory and mathematical biology. Emphasises modelling assumptions and the difference between exact results, numerical approximations and statistical evidence.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | 9–12 | `math.analysis.functions-and-graphs` | Functions and their graphs (precalculus) | Analysis |
| 2 | 9–12 | `math.analysis.exponential-logarithmic-functions` | Exponential and logarithmic functions | Analysis |
| 3 | 9–12 | `math.analysis.intro-calculus` | Introductory calculus | Analysis |
| 4 | UG 1 | `math.analysis.single-variable-calculus` | Calculus of one variable | Analysis |
| 5 | UG 1 | `math.algebra.linear-algebra` | Linear algebra | Algebra |
| 6 | UG 1 | `math.analysis.multivariable-calculus` | Multivariable and vector calculus | Analysis |
| 7 | UG 1 | `math.analysis.ordinary-differential-equations` | Ordinary differential equations | Analysis |
| 8 | UG 1 | `math.applied.classical-mechanics` | Classical mechanics | Applied Mathematics |
| 9 | UG 1 | `math.prob.probability-theory` | Probability theory | Probability & Statistics |
| 10 | UG 1 | `math.comp.numerical-methods` | Numerical methods | Computation |
| 11 | UG 1 | `math.prob.statistics` | Statistical inference | Probability & Statistics |
| 12 | UG 2 | `math.analysis.pde-intro` | Partial differential equations and Fourier series | Analysis |
| 13 | UG 2 | `math.applied.optimisation` | Optimisation | Applied Mathematics |
| 14 | UG 2 | `math.comp.numerical-analysis` | Numerical analysis | Computation |
| 15 | UG 2 | `math.applied.mathematical-biology` | Mathematical biology | Applied Mathematics |
| 16 | UG 2 | `math.applied.information-theory` | Information theory | Applied Mathematics |

## Graduate preparation (`graduate-prep`)

**Audience:** Advanced undergraduates and others preparing for a first year of graduate study in mathematics.

Consolidates the foundations most first-year graduate programmes assume (analysis, algebra, topology and category theory) and then samples the standard first-year courses: measure theory, functional analysis, modules and commutative algebra, representation theory, algebraic topology and smooth manifolds. Graduate programmes differ considerably, so learners should adapt the selection to the programmes and specialisations they are considering.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | UG 2 | `math.analysis.real-analysis` | Real analysis | Analysis |
| 2 | UG 2 | `math.algebra.groups` | Groups | Algebra |
| 3 | UG 2 | `math.algebra.rings` | Rings, ideals and fields | Algebra |
| 4 | UG 2 | `math.algebra.quotients` | Quotient groups and quotient rings | Algebra |
| 5 | UG 2 | `math.geom.point-set-topology` | Metric spaces and point-set topology | Geometry & Topology |
| 6 | UG 2 | `math.algebra.advanced-linear-algebra` | Advanced linear algebra | Algebra |
| 7 | UG 2 | `math.analysis.complex-analysis` | Complex analysis | Analysis |
| 8 | UG 2 | `math.algebra.fields-galois` | Fields and Galois theory | Algebra |
| 9 | UG 2 | `math.cat.natural-transformations` | Natural transformations | Category Theory |
| 10 | UG 2 | `math.cat.adjunctions` | Adjunctions | Category Theory |
| 11 | UG 2 | `math.geom.fundamental-group` | Homotopy and the fundamental group | Geometry & Topology |
| 12 | Grad | `math.analysis.measure-theory` | Measure theory and integration | Analysis |
| 13 | Grad | `math.algebra.modules` | Modules | Algebra |
| 14 | Grad | `math.analysis.functional-analysis` | Functional analysis | Analysis |
| 15 | Grad | `math.algebra.representation-theory` | Representation theory of finite groups | Algebra |
| 16 | Grad | `math.algebra.commutative-algebra` | Commutative algebra | Algebra |
| 17 | Grad | `math.geom.algebraic-topology` | Algebraic topology | Geometry & Topology |
| 18 | Grad | `math.geom.smooth-manifolds` | Smooth manifolds | Geometry & Topology |

## Research preparation (`research-prep`)

**Audience:** Graduate students and advanced independent learners preparing to read, write, check and contribute to research mathematics.

Research skills (writing, reading the literature, reproducible computation, experimental mathematics, formalisation and research ethics) together with one illustrative specialisation: from the Yoneda lemma and homological algebra through quivers and path algebras to derived categories and quiver representations. Research directions vary widely, so the specialisation is an example to adapt, and established results are always distinguished from open questions.

| # | Level | Milestone | Title | Subject |
|---|---|---|---|---|
| 1 | UG 2 | `math.found.mathematical-writing` | Mathematical writing | Foundations |
| 2 | Grad | `math.found.reading-literature` | Reading the mathematical literature | Foundations |
| 3 | UG 2 | `math.cat.yoneda` | The Yoneda lemma | Category Theory |
| 4 | Grad | `math.algebra.homological-algebra` | Homological algebra | Algebra |
| 5 | Grad | `math.cat.abelian-categories` | Abelian categories | Category Theory |
| 6 | Grad | `math.comp.computational-reproducibility` | Computational reproducibility | Computation |
| 7 | Grad | `math.comp.experimental-mathematics` | Experimental mathematics: conjectures and counterexamples | Computation |
| 8 | Grad | `math.algebra.representation-theory` | Representation theory of finite groups | Algebra |
| 9 | Grad | `math.algebra.path-algebras` | Quivers and path algebras | Algebra |
| 10 | Research | `math.cat.derived-categories` | Derived categories | Category Theory |
| 11 | Research | `math.algebra.quiver-representations` | Quiver representations | Algebra |
| 12 | Research | `math.comp.formalising-published-mathematics` | Formalising published mathematics | Computation |
| 13 | Research | `math.found.research-ethics` | Research ethics and attribution | Foundations |
