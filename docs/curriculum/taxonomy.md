# Lumenary Math taxonomy

<!-- Tables in this document were generated from content/math/graph/graph.json and pathways.json when it was written. Update them whenever the graph changes. -->

This document describes how the mathematics knowledge graph in `content/math/graph/graph.json` is organised: its levels, subjects, topic identifiers, statuses and edges, and the invariants every change must preserve. The graph is validated against `GraphFile` in `src/lib/schema.ts`.

At the time of writing the graph has **169 topics**, **306 required prerequisite edges** and **232 optional discovery edges** (42 of them walked by a named Wonder Trail). 5 topics are implemented as lessons; the rest are planned.

## Levels

Levels are ordered. The order below is the order used by every invariant in this document.

| Id | Short | Title | Ages | Description |
|---|---|---|---|---|
| k2 | K–2 | Kindergarten to Grade 2 | about 5–8 | Playful, concrete mathematics: collections, counting, shapes, patterns and simple actions that can be done and undone. Ideas are met through objects, pictures and talk, never through formal notation. |
| g3-5 | 3–5 | Grades 3 to 5 | about 8–11 | Whole-number arithmetic, fractions, measurement and the first language of sets. Learners begin to explain why a method works, not only how to use it. |
| g6-8 | 6–8 | Grades 6 to 8 | about 11–14 | Integers, rational numbers, functions as mappings, equations and proportional reasoning. Set notation, quantifiers and equivalence relations prepare the ground for proof. |
| g9-12 | 9–12 | Grades 9 to 12 | about 14–18 | Algebra, geometry, trigonometry, logic and proof, countability and introductory calculus. Composition, structure-preserving maps and a first universal property preview the language of higher mathematics. |
| ug1 | UG 1 | Early undergraduate | about 18–20 (or any age) | Calculus I–III, linear algebra, differential equations, probability and statistics, first-order logic and a first course in algebraic structures and categories. |
| ug2 | UG 2 | Advanced undergraduate | about 20–22 (or any age) | Real and complex analysis, abstract algebra, topology, number theory, axiomatic set theory, computability and core category theory through the Yoneda lemma. |
| grad | Grad | First-year graduate | adult | Measure theory, functional analysis, graduate algebra and topology, logic and category theory. Graduate programmes differ, so this level is organised as specialisation pathways rather than a single required syllabus. |
| research | Research | Research pathways | adult | Optional advanced directions and research skills: higher and derived categories, homotopy type theory, quiver representations, large cardinals, formalising published mathematics and research ethics. Established results are distinguished from open questions. |

Ages are typical, not requirements. Adults can enter at any level, and nobody is penalised for moving faster or slower than the ages suggest.

## Subjects

| Id | Short | Title | Description |
|---|---|---|---|
| foundations | Found. | Foundations | Collections, sets, logic and proof, growing into axiomatic set theory, model theory, proof theory and type theory. This lane is where mathematics examines its own language and assumptions. |
| number | Number | Number | From counting and place value through integers, rationals, reals and complex numbers to congruences and number theory. |
| algebra | Algebra | Algebra | School algebra, then linear algebra and abstract algebra (groups, rings, fields, modules), leading to homological algebra and representation theory. |
| geometry | Geometry | Geometry & Topology | Shapes, measurement, transformations and Euclidean geometry, trigonometry, then topology, differential geometry and algebraic geometry. |
| analysis | Analysis | Analysis | Approximation, rates of change and functions of a real variable, then calculus, real and complex analysis, differential equations, measure theory and functional analysis. |
| discrete | Discrete | Discrete Mathematics | Systematic counting, combinatorics, recurrences and graph theory, from puzzles with dots and lines to the probabilistic method. |
| probability | Prob. | Probability & Statistics | Data, chance and variability, then probability theory, statistical inference, Markov chains and measure-theoretic stochastic processes. |
| category | Category | Category Theory | Early precursors (doing, undoing and chaining actions), then composition, structure-preserving maps, universal properties, categories, functors, adjunctions and Yoneda, reaching monoidal, abelian, higher and derived categories. |
| computation | Comp. | Computation | Algorithms, programming for mathematics, numerical methods, computability and complexity, lambda calculus, formal methods and machine-checked proof in Lean. |
| applied | Applied | Applied Mathematics | Mathematics in use: codes and cryptography, modelling, mechanics and mathematical physics, information theory, optimisation and mathematical biology. |

The site draws a map with one lane per subject and one column per level. Current topic counts per cell:

| Subject | K–2 | 3–5 | 6–8 | 9–12 | UG 1 | UG 2 | Grad | Research | Total |
|---|---|---|---|---|---|---|---|---|---|
| Foundations | 1 | 2 | 3 | 4 | 2 | 6 | 7 | 3 | 28 |
| Number | 2 | 3 | 4 | 3 | 2 | 1 | 1 | · | 16 |
| Algebra | 1 | 1 | 3 | 2 | 2 | 5 | 5 | 1 | 20 |
| Geometry & Topology | 2 | 2 | 3 | 2 | 1 | 3 | 4 | · | 17 |
| Analysis | · | 1 | 1 | 4 | 3 | 3 | 2 | · | 14 |
| Discrete Mathematics | · | 2 | 1 | 2 | 1 | 2 | 1 | · | 9 |
| Probability & Statistics | 1 | 1 | 2 | 2 | 2 | 1 | 2 | · | 11 |
| Category Theory | 1 | 1 | 2 | 3 | 3 | 6 | 7 | 6 | 29 |
| Computation | 1 | 1 | 1 | 2 | 3 | 4 | 3 | 1 | 16 |
| Applied Mathematics | · | 1 | 1 | 1 | 2 | 3 | 1 | · | 9 |
| **Total** | 9 | 15 | 21 | 25 | 21 | 34 | 33 | 11 | 169 |

Empty cells are deliberate. For example, there is no kindergarten analysis topic, because forcing one would mean inventing content rather than describing a real precursor. The research column is intentionally light: it lists optional directions, not a syllabus.

## Topic identifiers

Every topic has a stable identifier of the form `math.<area>.<kebab-name>`, matching the `TopicId` pattern in the schema. Area prefixes in use:

| Prefix | Subject at creation |
|---|---|
| `math.found.…` | Foundations |
| `math.number.…` | Number |
| `math.algebra.…` | Algebra |
| `math.geom.…` | Geometry & Topology |
| `math.prob.…` | Probability & Statistics |
| `math.cat.…` | Category Theory |
| `math.comp.…` | Computation |
| `math.analysis.…` | Analysis |
| `math.discrete.…` | Discrete Mathematics |
| `math.applied.…` | Applied Mathematics |

Rules:

- Identifiers are **join keys**: lessons, translations, progress records, Wonder Trails and pathways refer to topics by id. Once published, an id is never renamed or reused. If a topic is split or retired, keep the old id and record the change instead of deleting it silently.
- The `subject` field is authoritative. The area prefix records where a topic started; a topic can later be reassigned to another subject without changing its id.
- Titles, summaries and objectives can be improved freely; ids cannot.

## Topic fields

Each topic records a title, subject, level and summary; required `prerequisites`; optional `discoveries`; 2–4 concrete `objectives`; `definitions`, `keyResults` and `misconceptions`; an optional `lesson` slug; the Wonder Trails (`trails`) that start from or pass through it; `references`; a `status`; and `tags`.

Definitions, key results and misconceptions are given for every topic from K–2 to Grades 9–12 and for every foundations and category-theory topic, and for most others. References are restricted to well-known published texts; a URL is given only for stable official locations.

Tags in use:

| Tag | Topics |
|---|---|
| `category-applications` | 1 |
| `category-progression` | 31 |
| `foundations-relationships` | 18 |
| `lean` | 4 |
| `research-direction` | 8 |
| `research-skills` | 6 |
| `set-theory-progression` | 18 |

- `set-theory-progression`, `category-progression` and `foundations-relationships` drive the tables in the progression documents.
- `research-skills` marks research-readiness topics; `research-direction` marks optional specialised directions; `category-applications` marks topics where category theory is applied; `lean` marks topics centred on the Lean proof assistant.

## Statuses

- `implemented`: a lesson exists under `content/math/lessons/<lesson>` and the topic's `lesson` field names it.
- `draft`: a lesson is being written but is not yet ready for learners.
- `planned`: the topic is part of the curriculum design; no lesson exists yet.

Status describes the existence of content, not its verification. Verification labels such as `formally-verified` or `mathematically-reviewed` belong to lessons and are derived from build reports or named reviewer records. A topic's presence in the graph is not a claim that its content has been reviewed.

## Edges

### Required prerequisite edges

`prerequisites` lists the topics that are **genuinely necessary** for understanding the topic. An edge p → t means a learner who has not met p cannot reasonably be expected to understand t. Helpful, motivating or historically related topics are not required edges; they are discovery edges.

Required edges are kept small: when p is needed only through another prerequisite q, the edge p → t is usually omitted, because the closure (below) already records it.

### Optional discovery edges

`discoveries` lists optional connections. A discovery edge t ⇢ u says that a learner at t may enjoy glimpsing u, and its `note` states precisely what the connection is. A discovery edge:

- never affects progression, grades or mastery;
- may point to a topic at any level, usually a later one (a glimpse ahead), sometimes across subjects;
- may name the Wonder Trail that walks it (`trail`);
- must not duplicate a required edge between the same two topics, in either direction;
- must say when it is an analogy rather than a formal construction.

## Invariants

The following are checked whenever the graph changes:

1. **Referential integrity.** Every prerequisite, discovery target and pathway milestone is an existing topic id. Ids are unique.
2. **No self-loops.** No topic requires itself or lists itself as a discovery.
3. **Acyclicity.** The required edges form a directed acyclic graph (DAG).
4. **Level monotonicity.** If p is a prerequisite of t, then the level of p is not later than the level of t.
5. **No duplicated edges.** No discovery edge duplicates a required edge.
6. **Pathway order.** In every pathway, no milestone is a (transitive) prerequisite of an earlier milestone.

### A precise categorical remark

Let T be the set of topics and write p → t for a required edge. Define p ≤ t when there is a directed path of required edges from p to t, including the empty path (so t ≤ t). This is the reflexive–transitive closure of the required-edge relation.

- ≤ is reflexive and transitive by construction.
- ≤ is antisymmetric because the required edges form a DAG: if p ≤ t and t ≤ p with p ≠ t, the two paths would combine into a directed cycle.

So (T, ≤) is a partially ordered set. Any poset can be regarded as a category with the elements as objects and exactly one morphism p → t whenever p ≤ t; composition is transitivity and identities are reflexivity. Such a category, with at most one morphism between any two objects, is called **thin**. The required-prerequisite structure is therefore a thin category. (It is also the thin quotient of the free category on the directed graph of required edges, in which morphisms are paths.)

Invariant 6 says that the order of a pathway's milestones is a linear extension of ≤ restricted to those milestones.

That is all the structure we claim. Discovery edges are not part of this order, and nothing here asserts that learning is functorial or that the graph carries any further categorical structure. Statements of that kind would need precise definitions first.

## Topic index

### Kindergarten to Grade 2 (K–2)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.patterns` | Patterns | Algebra | planned |
| `math.cat.actions-and-undoing` | Doing and undoing | Category Theory | planned |
| `math.comp.following-instructions` | Following and giving precise instructions | Computation | planned |
| `math.found.collections` | Collections | Foundations | implemented |
| `math.geom.measurement` | Measuring length and time | Geometry & Topology | planned |
| `math.geom.shapes` | Shapes | Geometry & Topology | planned |
| `math.number.addition-subtraction` | Addition, subtraction and place value to 100 | Number | planned |
| `math.number.counting` | Counting | Number | planned |
| `math.prob.data-and-tallies` | Data, tallies and picture graphs | Probability & Statistics | planned |
### Grades 3 to 5 (3–5)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.expressions-and-unknowns` | Expressions, unknowns and rules | Algebra | planned |
| `math.analysis.estimation` | Estimation and rounding | Analysis | planned |
| `math.applied.secret-codes` | Secret codes | Applied Mathematics | planned |
| `math.cat.chaining-actions` | One thing after another | Category Theory | planned |
| `math.comp.loops-and-conditions` | Repetition and decisions | Computation | planned |
| `math.discrete.networks-puzzles` | Dots and lines: networks and puzzles | Discrete Mathematics | planned |
| `math.discrete.systematic-listing` | Systematic listing and counting | Discrete Mathematics | planned |
| `math.found.logic-statements` | True, false, and, or, not | Foundations | planned |
| `math.found.sets` | Sets | Foundations | implemented |
| `math.geom.area-angles` | Area, perimeter and angles | Geometry & Topology | planned |
| `math.geom.symmetry-transformations` | Symmetry: slides, turns and flips | Geometry & Topology | planned |
| `math.number.factors-primes` | Factors, multiples and primes | Number | planned |
| `math.number.fractions` | Fractions and decimals | Number | planned |
| `math.number.whole-number-arithmetic` | Whole-number arithmetic | Number | planned |
| `math.prob.data-displays` | Data displays and the mean as a fair share | Probability & Statistics | planned |
### Grades 6 to 8 (6–8)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.linear-equations` | Linear equations and inequalities | Algebra | planned |
| `math.algebra.linear-relationships` | Linear relationships and simultaneous equations | Algebra | planned |
| `math.algebra.variables-expressions` | Variables and algebraic expressions | Algebra | planned |
| `math.analysis.graphs-of-change` | Graphs of change | Analysis | planned |
| `math.applied.check-digits` | Check digits and error detection | Applied Mathematics | planned |
| `math.cat.chaining-functions` | Function machines in sequence | Category Theory | planned |
| `math.cat.commutative-diagrams-intro` | Diagrams where paths agree | Category Theory | planned |
| `math.comp.programming-intro` | Programming for mathematics | Computation | planned |
| `math.discrete.counting-principles` | Counting principles | Discrete Mathematics | planned |
| `math.found.equivalence-relations` | Relations, equivalence relations and partitions | Foundations | planned |
| `math.found.functions` | Functions | Foundations | implemented |
| `math.found.quantifiers` | Set-builder notation, quantifiers and infinite sets | Foundations | planned |
| `math.geom.coordinate-plane` | The coordinate plane | Geometry & Topology | planned |
| `math.geom.pythagorean-theorem` | The Pythagorean theorem | Geometry & Topology | planned |
| `math.geom.rigid-motions-similarity` | Rigid motions, congruence and similarity | Geometry & Topology | planned |
| `math.number.integers` | Integers | Number | implemented |
| `math.number.modular-arithmetic` | Clock arithmetic: remainders and modular arithmetic | Number | planned |
| `math.number.rational-numbers` | Rational numbers | Number | planned |
| `math.number.ratios-proportions` | Ratios, rates and proportional reasoning | Number | planned |
| `math.prob.probability-intro` | Probability | Probability & Statistics | planned |
| `math.prob.statistics-intro` | Statistics: centre, spread and distributions | Probability & Statistics | planned |
### Grades 9 to 12 (9–12)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.polynomials` | Polynomials | Algebra | planned |
| `math.algebra.quadratics` | Quadratic equations and functions | Algebra | planned |
| `math.analysis.exponential-logarithmic-functions` | Exponential and logarithmic functions | Analysis | planned |
| `math.analysis.functions-and-graphs` | Functions and their graphs (precalculus) | Analysis | planned |
| `math.analysis.intro-calculus` | Introductory calculus | Analysis | planned |
| `math.analysis.sequences-series` | Sequences and series | Analysis | planned |
| `math.applied.modelling-with-functions` | Mathematical modelling with functions | Applied Mathematics | planned |
| `math.cat.composition` | Composition | Category Theory | implemented |
| `math.cat.intro-universal-properties` | Products by maps: a first universal property | Category Theory | planned |
| `math.cat.structure-preserving-maps` | Structure-preserving maps: homomorphisms and isomorphisms | Category Theory | planned |
| `math.comp.algorithms-and-efficiency` | Algorithms, correctness and efficiency | Computation | planned |
| `math.comp.intro-lean` | First steps in Lean | Computation | planned |
| `math.discrete.combinatorics` | Combinatorics | Discrete Mathematics | planned |
| `math.discrete.graph-basics` | Graphs | Discrete Mathematics | planned |
| `math.found.countability` | Countability and Cantor's diagonal argument | Foundations | planned |
| `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | Foundations | planned |
| `math.found.propositional-logic` | Propositional logic and truth tables | Foundations | planned |
| `math.found.russell-paradox` | Russell's paradox and why sets need axioms | Foundations | planned |
| `math.geom.euclidean-geometry` | Euclidean geometry and proof | Geometry & Topology | planned |
| `math.geom.trigonometry` | Trigonometry | Geometry & Topology | planned |
| `math.number.complex-numbers` | Complex numbers | Number | planned |
| `math.number.divisibility-gcd` | Divisibility, Euclid's algorithm and unique factorisation | Number | planned |
| `math.number.real-numbers` | Real numbers and irrationality | Number | planned |
| `math.prob.probability-rules` | Conditional probability and independence | Probability & Statistics | planned |
| `math.prob.statistical-inference-intro` | Sampling and statistical reasoning | Probability & Statistics | planned |
### Early undergraduate (UG 1)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.algebraic-structures` | Algebraic structures: monoids, groups and rings | Algebra | planned |
| `math.algebra.linear-algebra` | Linear algebra | Algebra | planned |
| `math.analysis.multivariable-calculus` | Multivariable and vector calculus | Analysis | planned |
| `math.analysis.ordinary-differential-equations` | Ordinary differential equations | Analysis | planned |
| `math.analysis.single-variable-calculus` | Calculus of one variable | Analysis | planned |
| `math.applied.classical-mechanics` | Classical mechanics | Applied Mathematics | planned |
| `math.applied.cryptography` | Cryptography | Applied Mathematics | planned |
| `math.cat.categories` | Categories | Category Theory | planned |
| `math.cat.functors` | Functors | Category Theory | planned |
| `math.cat.universal-properties` | Universal properties | Category Theory | planned |
| `math.comp.algorithm-design` | Algorithm design and analysis | Computation | planned |
| `math.comp.formal-proof-lean` | Formalising mathematics in Lean and Mathlib | Computation | planned |
| `math.comp.numerical-methods` | Numerical methods | Computation | planned |
| `math.discrete.recurrences-generating-functions` | Recurrences and generating functions | Discrete Mathematics | planned |
| `math.found.first-order-logic` | First-order logic | Foundations | planned |
| `math.found.order-theory` | Orders, lattices and well-orders | Foundations | planned |
| `math.geom.transformation-geometry` | Transformation geometry and the Erlangen programme | Geometry & Topology | planned |
| `math.number.congruences` | Congruences | Number | planned |
| `math.number.number-system-constructions` | Constructing ℤ, ℚ and ℝ | Number | planned |
| `math.prob.probability-theory` | Probability theory | Probability & Statistics | planned |
| `math.prob.statistics` | Statistical inference | Probability & Statistics | planned |
### Advanced undergraduate (UG 2)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.advanced-linear-algebra` | Advanced linear algebra | Algebra | planned |
| `math.algebra.fields-galois` | Fields and Galois theory | Algebra | planned |
| `math.algebra.groups` | Groups | Algebra | planned |
| `math.algebra.quotients` | Quotient groups and quotient rings | Algebra | planned |
| `math.algebra.rings` | Rings, ideals and fields | Algebra | planned |
| `math.analysis.complex-analysis` | Complex analysis | Analysis | planned |
| `math.analysis.pde-intro` | Partial differential equations and Fourier series | Analysis | planned |
| `math.analysis.real-analysis` | Real analysis | Analysis | planned |
| `math.applied.information-theory` | Information theory | Applied Mathematics | planned |
| `math.applied.mathematical-biology` | Mathematical biology | Applied Mathematics | planned |
| `math.applied.optimisation` | Optimisation | Applied Mathematics | planned |
| `math.cat.adjunctions` | Adjunctions | Category Theory | planned |
| `math.cat.limits-colimits` | Limits and colimits | Category Theory | planned |
| `math.cat.natural-transformations` | Natural transformations | Category Theory | planned |
| `math.cat.products-coproducts` | Products, coproducts, initial and terminal objects | Category Theory | planned |
| `math.cat.representable-functors` | Representable functors | Category Theory | planned |
| `math.cat.yoneda` | The Yoneda lemma | Category Theory | planned |
| `math.comp.complexity-theory` | Computational complexity | Computation | planned |
| `math.comp.computability` | Computability | Computation | planned |
| `math.comp.lambda-calculus` | The λ-calculus | Computation | planned |
| `math.comp.numerical-analysis` | Numerical analysis | Computation | planned |
| `math.discrete.enumerative-combinatorics` | Enumerative combinatorics | Discrete Mathematics | planned |
| `math.discrete.graph-theory` | Graph theory | Discrete Mathematics | planned |
| `math.found.axiom-of-choice` | The axiom of choice and its equivalents | Foundations | planned |
| `math.found.cardinals` | Ordinals and cardinals | Foundations | planned |
| `math.found.completeness-theorem` | Completeness, compactness and Löwenheim–Skolem | Foundations | planned |
| `math.found.mathematical-writing` | Mathematical writing | Foundations | planned |
| `math.found.type-theory` | Type theory and propositions as types | Foundations | planned |
| `math.found.zfc` | ZFC: axiomatic set theory | Foundations | planned |
| `math.geom.curves-surfaces` | Differential geometry of curves and surfaces | Geometry & Topology | planned |
| `math.geom.fundamental-group` | Homotopy and the fundamental group | Geometry & Topology | planned |
| `math.geom.point-set-topology` | Metric spaces and point-set topology | Geometry & Topology | planned |
| `math.number.elementary-number-theory` | Number theory | Number | planned |
| `math.prob.markov-chains` | Markov chains | Probability & Statistics | planned |
### First-year graduate (Grad)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.commutative-algebra` | Commutative algebra | Algebra | planned |
| `math.algebra.homological-algebra` | Homological algebra | Algebra | planned |
| `math.algebra.modules` | Modules | Algebra | planned |
| `math.algebra.path-algebras` | Quivers and path algebras | Algebra | planned |
| `math.algebra.representation-theory` | Representation theory of finite groups | Algebra | planned |
| `math.analysis.functional-analysis` | Functional analysis | Analysis | planned |
| `math.analysis.measure-theory` | Measure theory and integration | Analysis | planned |
| `math.applied.quantum-mechanics` | Mathematical foundations of quantum mechanics | Applied Mathematics | planned |
| `math.cat.abelian-categories` | Abelian categories | Category Theory | planned |
| `math.cat.categorical-logic` | Categorical logic | Category Theory | planned |
| `math.cat.elementary-topoi` | Elementary topos theory | Category Theory | planned |
| `math.cat.enriched-categories` | Enriched categories | Category Theory | planned |
| `math.cat.kan-extensions` | Kan extensions | Category Theory | planned |
| `math.cat.monads` | Monads | Category Theory | planned |
| `math.cat.monoidal-categories` | Monoidal categories | Category Theory | planned |
| `math.comp.computational-reproducibility` | Computational reproducibility | Computation | planned |
| `math.comp.experimental-mathematics` | Experimental mathematics: conjectures and counterexamples | Computation | planned |
| `math.comp.formal-methods` | Formal methods | Computation | planned |
| `math.discrete.probabilistic-method` | The probabilistic method | Discrete Mathematics | planned |
| `math.found.axiomatic-set-theory` | Axiomatic set theory: hierarchy, cardinal arithmetic and L | Foundations | planned |
| `math.found.descriptive-set-theory` | Descriptive set theory | Foundations | planned |
| `math.found.forcing` | Forcing and independence | Foundations | planned |
| `math.found.incompleteness` | Gödel's incompleteness theorems | Foundations | planned |
| `math.found.model-theory` | Model theory | Foundations | planned |
| `math.found.proof-theory` | Proof theory | Foundations | planned |
| `math.found.reading-literature` | Reading the mathematical literature | Foundations | planned |
| `math.geom.algebraic-geometry` | Algebraic geometry | Geometry & Topology | planned |
| `math.geom.algebraic-topology` | Algebraic topology | Geometry & Topology | planned |
| `math.geom.sheaves` | Sheaves | Geometry & Topology | planned |
| `math.geom.smooth-manifolds` | Smooth manifolds | Geometry & Topology | planned |
| `math.number.algebraic-number-theory` | Algebraic number theory | Number | planned |
| `math.prob.measure-theoretic-probability` | Measure-theoretic probability | Probability & Statistics | planned |
| `math.prob.stochastic-processes` | Stochastic processes | Probability & Statistics | planned |
### Research pathways (Research)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.quiver-representations` | Quiver representations | Algebra | planned |
| `math.cat.categorical-representation-theory` | Categorical representation theory | Category Theory | planned |
| `math.cat.derived-categories` | Derived categories | Category Theory | planned |
| `math.cat.higher-categories` | Higher categories | Category Theory | planned |
| `math.cat.infinity-categories` | ∞-categories | Category Theory | planned |
| `math.cat.stable-infinity-categories` | Stable ∞-categories | Category Theory | planned |
| `math.cat.triangulated-categories` | Triangulated categories | Category Theory | planned |
| `math.comp.formalising-published-mathematics` | Formalising published mathematics | Computation | planned |
| `math.found.homotopy-type-theory` | Homotopy type theory | Foundations | planned |
| `math.found.large-cardinals` | Large cardinals | Foundations | planned |
| `math.found.research-ethics` | Research ethics and attribution | Foundations | planned |
