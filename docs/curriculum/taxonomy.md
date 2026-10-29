# Lumenary Math taxonomy

<!-- The marked sections are generated from content/math/graph/graph.json by `npm run docs:curriculum`; do not edit them by hand. -->

This document describes how the mathematics knowledge graph in `content/math/graph/graph.json` is organised: its levels, subjects, topic identifiers, statuses and edges, and the invariants every change must preserve. The graph is validated against `GraphFile` in `src/lib/schema.ts`.

<!-- generated:summary -->
The graph has **200 topics**, **387 required prerequisite edges** and **317 optional discovery edges** (54 of them walked by a named Wonder Trail). 200 topics are implemented as lessons — every topic in the graph; there are 19 Wonder Trails.
<!-- /generated:summary -->

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

<!-- generated:counts -->
| Subject | K–2 | 3–5 | 6–8 | 9–12 | UG 1 | UG 2 | Grad | Research | Total |
|---|---|---|---|---|---|---|---|---|---|
| Foundations | 1 | 2 | 3 | 4 | 2 | 6 | 7 | 3 | 28 |
| Number | 2 | 3 | 4 | 3 | 2 | 1 | 2 | 2 | 19 |
| Algebra | 1 | 1 | 3 | 2 | 2 | 5 | 5 | 1 | 20 |
| Geometry & Topology | 2 | 2 | 3 | 4 | 3 | 7 | 10 | 5 | 36 |
| Analysis | · | 1 | 1 | 4 | 3 | 4 | 5 | 1 | 19 |
| Discrete Mathematics | · | 2 | 1 | 2 | 1 | 2 | 1 | 1 | 10 |
| Probability & Statistics | 1 | 1 | 2 | 2 | 2 | 1 | 2 | 1 | 12 |
| Category Theory | 1 | 1 | 2 | 3 | 3 | 6 | 7 | 6 | 29 |
| Computation | 1 | 1 | 1 | 2 | 3 | 4 | 3 | 1 | 16 |
| Applied Mathematics | · | 1 | 1 | 1 | 2 | 3 | 2 | 1 | 11 |
| **Total** | 9 | 15 | 21 | 27 | 23 | 39 | 44 | 22 | 200 |
<!-- /generated:counts -->

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

<!-- generated:tags -->
| Tag | Topics |
|---|---|
| `category-applications` | 1 |
| `category-progression` | 31 |
| `foundations-relationships` | 18 |
| `geometry-topology-progression` | 39 |
| `lean` | 4 |
| `research-direction` | 19 |
| `research-skills` | 6 |
| `set-theory-progression` | 18 |
<!-- /generated:tags -->

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

<!-- generated:index -->
### Kindergarten to Grade 2 (K–2)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.patterns` | Patterns | Algebra | implemented (`patterns`) |
| `math.cat.actions-and-undoing` | Doing and undoing | Category Theory | implemented (`actions-and-undoing`) |
| `math.comp.following-instructions` | Following and giving precise instructions | Computation | implemented (`following-instructions`) |
| `math.found.collections` | Collections | Foundations | implemented (`collections`) |
| `math.geom.measurement` | Measuring length and time | Geometry & Topology | implemented (`measurement`) |
| `math.geom.shapes` | Shapes | Geometry & Topology | implemented (`shapes`) |
| `math.number.addition-subtraction` | Addition, subtraction and place value to 100 | Number | implemented (`addition-subtraction`) |
| `math.number.counting` | Counting | Number | implemented (`counting`) |
| `math.prob.data-and-tallies` | Data, tallies and picture graphs | Probability & Statistics | implemented (`data-and-tallies`) |

### Grades 3 to 5 (3–5)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.expressions-and-unknowns` | Expressions, unknowns and rules | Algebra | implemented (`expressions-and-unknowns`) |
| `math.analysis.estimation` | Estimation and rounding | Analysis | implemented (`estimation`) |
| `math.applied.secret-codes` | Secret codes | Applied Mathematics | implemented (`secret-codes`) |
| `math.cat.chaining-actions` | One thing after another | Category Theory | implemented (`chaining-actions`) |
| `math.comp.loops-and-conditions` | Repetition and decisions | Computation | implemented (`loops-and-conditions`) |
| `math.discrete.networks-puzzles` | Dots and lines: networks and puzzles | Discrete Mathematics | implemented (`networks-puzzles`) |
| `math.discrete.systematic-listing` | Systematic listing and counting | Discrete Mathematics | implemented (`systematic-listing`) |
| `math.found.logic-statements` | True, false, and, or, not | Foundations | implemented (`logic-statements`) |
| `math.found.sets` | Sets | Foundations | implemented (`sets`) |
| `math.geom.area-angles` | Area, perimeter and angles | Geometry & Topology | implemented (`area-angles`) |
| `math.geom.symmetry-transformations` | Symmetry: slides, turns and flips | Geometry & Topology | implemented (`symmetry-transformations`) |
| `math.number.factors-primes` | Factors, multiples and primes | Number | implemented (`factors-primes`) |
| `math.number.fractions` | Fractions and decimals | Number | implemented (`fractions`) |
| `math.number.whole-number-arithmetic` | Whole-number arithmetic | Number | implemented (`whole-number-arithmetic`) |
| `math.prob.data-displays` | Data displays and the mean as a fair share | Probability & Statistics | implemented (`data-displays`) |

### Grades 6 to 8 (6–8)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.linear-equations` | Linear equations and inequalities | Algebra | implemented (`linear-equations`) |
| `math.algebra.linear-relationships` | Linear relationships and simultaneous equations | Algebra | implemented (`linear-relationships`) |
| `math.algebra.variables-expressions` | Variables and algebraic expressions | Algebra | implemented (`variables-expressions`) |
| `math.analysis.graphs-of-change` | Graphs of change | Analysis | implemented (`graphs-of-change`) |
| `math.applied.check-digits` | Check digits and error detection | Applied Mathematics | implemented (`check-digits`) |
| `math.cat.chaining-functions` | Function machines in sequence | Category Theory | implemented (`chaining-functions`) |
| `math.cat.commutative-diagrams-intro` | Diagrams where paths agree | Category Theory | implemented (`commutative-diagrams-intro`) |
| `math.comp.programming-intro` | Programming for mathematics | Computation | implemented (`programming-intro`) |
| `math.discrete.counting-principles` | Counting principles | Discrete Mathematics | implemented (`counting-principles`) |
| `math.found.equivalence-relations` | Relations, equivalence relations and partitions | Foundations | implemented (`equivalence-relations`) |
| `math.found.functions` | Functions | Foundations | implemented (`functions`) |
| `math.found.quantifiers` | Set-builder notation, quantifiers and infinite sets | Foundations | implemented (`quantifiers`) |
| `math.geom.coordinate-plane` | The coordinate plane | Geometry & Topology | implemented (`coordinate-plane`) |
| `math.geom.pythagorean-theorem` | The Pythagorean theorem | Geometry & Topology | implemented (`pythagorean-theorem`) |
| `math.geom.rigid-motions-similarity` | Rigid motions, congruence and similarity | Geometry & Topology | implemented (`rigid-motions-similarity`) |
| `math.number.integers` | Integers | Number | implemented (`integers`) |
| `math.number.modular-arithmetic` | Clock arithmetic: remainders and modular arithmetic | Number | implemented (`modular-arithmetic`) |
| `math.number.rational-numbers` | Rational numbers | Number | implemented (`rational-numbers`) |
| `math.number.ratios-proportions` | Ratios, rates and proportional reasoning | Number | implemented (`ratios-proportions`) |
| `math.prob.probability-intro` | Probability | Probability & Statistics | implemented (`probability-intro`) |
| `math.prob.statistics-intro` | Statistics: centre, spread and distributions | Probability & Statistics | implemented (`statistics-intro`) |

### Grades 9 to 12 (9–12)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.polynomials` | Polynomials | Algebra | implemented (`polynomials`) |
| `math.algebra.quadratics` | Quadratic equations and functions | Algebra | implemented (`quadratics`) |
| `math.analysis.exponential-logarithmic-functions` | Exponential and logarithmic functions | Analysis | implemented (`exponential-logarithmic-functions`) |
| `math.analysis.functions-and-graphs` | Functions and their graphs (precalculus) | Analysis | implemented (`functions-and-graphs`) |
| `math.analysis.intro-calculus` | Introductory calculus | Analysis | implemented (`intro-calculus`) |
| `math.analysis.sequences-series` | Sequences and series | Analysis | implemented (`sequences-series`) |
| `math.applied.modelling-with-functions` | Mathematical modelling with functions | Applied Mathematics | implemented (`modelling-with-functions`) |
| `math.cat.composition` | Composition | Category Theory | implemented (`composition`) |
| `math.cat.intro-universal-properties` | Products by maps: a first universal property | Category Theory | implemented (`intro-universal-properties`) |
| `math.cat.structure-preserving-maps` | Structure-preserving maps: homomorphisms and isomorphisms | Category Theory | implemented (`structure-preserving-maps`) |
| `math.comp.algorithms-and-efficiency` | Algorithms, correctness and efficiency | Computation | implemented (`algorithms-and-efficiency`) |
| `math.comp.intro-lean` | First steps in Lean | Computation | implemented (`intro-lean`) |
| `math.discrete.combinatorics` | Combinatorics | Discrete Mathematics | implemented (`combinatorics`) |
| `math.discrete.graph-basics` | Graphs | Discrete Mathematics | implemented (`graph-basics`) |
| `math.found.countability` | Countability and Cantor's diagonal argument | Foundations | implemented (`countability`) |
| `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | Foundations | implemented (`proof-techniques`) |
| `math.found.propositional-logic` | Propositional logic and truth tables | Foundations | implemented (`propositional-logic`) |
| `math.found.russell-paradox` | Russell's paradox and why sets need axioms | Foundations | implemented (`russell-paradox`) |
| `math.geom.conic-sections` | Conic sections | Geometry & Topology | implemented (`conic-sections`) |
| `math.geom.euclidean-geometry` | Euclidean geometry and proof | Geometry & Topology | implemented (`euclidean-geometry`) |
| `math.geom.trigonometry` | Trigonometry | Geometry & Topology | implemented (`trigonometry`) |
| `math.geom.vectors` | Vectors and coordinate geometry | Geometry & Topology | implemented (`vectors`) |
| `math.number.complex-numbers` | Complex numbers | Number | implemented (`complex-numbers`) |
| `math.number.divisibility-gcd` | Divisibility, Euclid's algorithm and unique factorisation | Number | implemented (`divisibility-gcd`) |
| `math.number.real-numbers` | Real numbers and irrationality | Number | implemented (`real-numbers`) |
| `math.prob.probability-rules` | Conditional probability and independence | Probability & Statistics | implemented (`probability-rules`) |
| `math.prob.statistical-inference-intro` | Sampling and statistical reasoning | Probability & Statistics | implemented (`statistical-inference-intro`) |

### Early undergraduate (UG 1)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.algebraic-structures` | Algebraic structures: monoids, groups and rings | Algebra | implemented (`algebraic-structures`) |
| `math.algebra.linear-algebra` | Linear algebra | Algebra | implemented (`linear-algebra`) |
| `math.analysis.multivariable-calculus` | Multivariable and vector calculus | Analysis | implemented (`multivariable-calculus`) |
| `math.analysis.ordinary-differential-equations` | Ordinary differential equations | Analysis | implemented (`ordinary-differential-equations`) |
| `math.analysis.single-variable-calculus` | Calculus of one variable | Analysis | implemented (`single-variable-calculus`) |
| `math.applied.classical-mechanics` | Classical mechanics | Applied Mathematics | implemented (`classical-mechanics`) |
| `math.applied.cryptography` | Cryptography | Applied Mathematics | implemented (`cryptography`) |
| `math.cat.categories` | Categories | Category Theory | implemented (`categories`) |
| `math.cat.functors` | Functors | Category Theory | implemented (`functors`) |
| `math.cat.universal-properties` | Universal properties | Category Theory | implemented (`universal-properties`) |
| `math.comp.algorithm-design` | Algorithm design and analysis | Computation | implemented (`algorithm-design`) |
| `math.comp.formal-proof-lean` | Formalising mathematics in Lean and Mathlib | Computation | implemented (`formal-proof-lean`) |
| `math.comp.numerical-methods` | Numerical methods | Computation | implemented (`numerical-methods`) |
| `math.discrete.recurrences-generating-functions` | Recurrences and generating functions | Discrete Mathematics | implemented (`recurrences-generating-functions`) |
| `math.found.first-order-logic` | First-order logic | Foundations | implemented (`first-order-logic`) |
| `math.found.order-theory` | Orders, lattices and well-orders | Foundations | implemented (`order-theory`) |
| `math.geom.non-euclidean-geometry` | Non-Euclidean geometry: spherical and hyperbolic | Geometry & Topology | implemented (`non-euclidean-geometry`) |
| `math.geom.surfaces-euler-characteristic` | Surfaces, polyhedra and the Euler characteristic | Geometry & Topology | implemented (`surfaces-euler-characteristic`) |
| `math.geom.transformation-geometry` | Transformation geometry and the Erlangen programme | Geometry & Topology | implemented (`transformation-geometry`) |
| `math.number.congruences` | Congruences | Number | implemented (`congruences`) |
| `math.number.number-system-constructions` | Constructing ℤ, ℚ and ℝ | Number | implemented (`number-system-constructions`) |
| `math.prob.probability-theory` | Probability theory | Probability & Statistics | implemented (`probability-theory`) |
| `math.prob.statistics` | Statistical inference | Probability & Statistics | implemented (`statistics`) |

### Advanced undergraduate (UG 2)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.advanced-linear-algebra` | Advanced linear algebra | Algebra | implemented (`advanced-linear-algebra`) |
| `math.algebra.fields-galois` | Fields and Galois theory | Algebra | implemented (`fields-galois`) |
| `math.algebra.groups` | Groups | Algebra | implemented (`groups`) |
| `math.algebra.quotients` | Quotient groups and quotient rings | Algebra | implemented (`quotients`) |
| `math.algebra.rings` | Rings, ideals and fields | Algebra | implemented (`rings`) |
| `math.analysis.complex-analysis` | Complex analysis | Analysis | implemented (`complex-analysis`) |
| `math.analysis.dynamical-systems` | Dynamical systems and chaos | Analysis | implemented (`dynamical-systems`) |
| `math.analysis.pde-intro` | Partial differential equations and Fourier series | Analysis | implemented (`pde-intro`) |
| `math.analysis.real-analysis` | Real analysis | Analysis | implemented (`real-analysis`) |
| `math.applied.information-theory` | Information theory | Applied Mathematics | implemented (`information-theory`) |
| `math.applied.mathematical-biology` | Mathematical biology | Applied Mathematics | implemented (`mathematical-biology`) |
| `math.applied.optimisation` | Optimisation | Applied Mathematics | implemented (`optimisation`) |
| `math.cat.adjunctions` | Adjunctions | Category Theory | implemented (`adjunctions`) |
| `math.cat.limits-colimits` | Limits and colimits | Category Theory | implemented (`limits-colimits`) |
| `math.cat.natural-transformations` | Natural transformations | Category Theory | implemented (`natural-transformations`) |
| `math.cat.products-coproducts` | Products, coproducts, initial and terminal objects | Category Theory | implemented (`products-coproducts`) |
| `math.cat.representable-functors` | Representable functors | Category Theory | implemented (`representable-functors`) |
| `math.cat.yoneda` | The Yoneda lemma | Category Theory | implemented (`yoneda`) |
| `math.comp.complexity-theory` | Computational complexity | Computation | implemented (`complexity-theory`) |
| `math.comp.computability` | Computability | Computation | implemented (`computability`) |
| `math.comp.lambda-calculus` | The λ-calculus | Computation | implemented (`lambda-calculus`) |
| `math.comp.numerical-analysis` | Numerical analysis | Computation | implemented (`numerical-analysis`) |
| `math.discrete.enumerative-combinatorics` | Enumerative combinatorics | Discrete Mathematics | implemented (`enumerative-combinatorics`) |
| `math.discrete.graph-theory` | Graph theory | Discrete Mathematics | implemented (`graph-theory`) |
| `math.found.axiom-of-choice` | The axiom of choice and its equivalents | Foundations | implemented (`axiom-of-choice`) |
| `math.found.cardinals` | Ordinals and cardinals | Foundations | implemented (`cardinals`) |
| `math.found.completeness-theorem` | Completeness, compactness and Löwenheim–Skolem | Foundations | implemented (`completeness-theorem`) |
| `math.found.mathematical-writing` | Mathematical writing | Foundations | implemented (`mathematical-writing`) |
| `math.found.type-theory` | Type theory and propositions as types | Foundations | implemented (`type-theory`) |
| `math.found.zfc` | ZFC: axiomatic set theory | Foundations | implemented (`zfc`) |
| `math.geom.curves-surfaces` | Differential geometry of curves and surfaces | Geometry & Topology | implemented (`curves-surfaces`) |
| `math.geom.differential-forms` | Differential forms and Stokes' theorem | Geometry & Topology | implemented (`differential-forms`) |
| `math.geom.fundamental-group` | Homotopy and the fundamental group | Geometry & Topology | implemented (`fundamental-group`) |
| `math.geom.knot-theory` | Knot theory | Geometry & Topology | implemented (`knot-theory`) |
| `math.geom.matrix-groups` | Matrix groups and continuous symmetry | Geometry & Topology | implemented (`matrix-groups`) |
| `math.geom.point-set-topology` | Metric spaces and point-set topology | Geometry & Topology | implemented (`point-set-topology`) |
| `math.geom.projective-geometry` | Projective geometry | Geometry & Topology | implemented (`projective-geometry`) |
| `math.number.elementary-number-theory` | Number theory | Number | implemented (`elementary-number-theory`) |
| `math.prob.markov-chains` | Markov chains | Probability & Statistics | implemented (`markov-chains`) |

### First-year graduate (Grad)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.commutative-algebra` | Commutative algebra | Algebra | implemented (`commutative-algebra`) |
| `math.algebra.homological-algebra` | Homological algebra | Algebra | implemented (`homological-algebra`) |
| `math.algebra.modules` | Modules | Algebra | implemented (`modules`) |
| `math.algebra.path-algebras` | Quivers and path algebras | Algebra | implemented (`path-algebras`) |
| `math.algebra.representation-theory` | Representation theory of finite groups | Algebra | implemented (`representation-theory`) |
| `math.analysis.ergodic-theory` | Ergodic theory | Analysis | implemented (`ergodic-theory`) |
| `math.analysis.functional-analysis` | Functional analysis | Analysis | implemented (`functional-analysis`) |
| `math.analysis.harmonic-analysis` | Fourier and harmonic analysis | Analysis | implemented (`harmonic-analysis`) |
| `math.analysis.measure-theory` | Measure theory and integration | Analysis | implemented (`measure-theory`) |
| `math.analysis.pde-theory` | Partial differential equations: modern theory | Analysis | implemented (`pde-theory`) |
| `math.applied.quantum-mechanics` | Mathematical foundations of quantum mechanics | Applied Mathematics | implemented (`quantum-mechanics`) |
| `math.applied.relativity` | The geometry of spacetime: special and general relativity | Applied Mathematics | implemented (`relativity`) |
| `math.cat.abelian-categories` | Abelian categories | Category Theory | implemented (`abelian-categories`) |
| `math.cat.categorical-logic` | Categorical logic | Category Theory | implemented (`categorical-logic`) |
| `math.cat.elementary-topoi` | Elementary topos theory | Category Theory | implemented (`elementary-topoi`) |
| `math.cat.enriched-categories` | Enriched categories | Category Theory | implemented (`enriched-categories`) |
| `math.cat.kan-extensions` | Kan extensions | Category Theory | implemented (`kan-extensions`) |
| `math.cat.monads` | Monads | Category Theory | implemented (`monads`) |
| `math.cat.monoidal-categories` | Monoidal categories | Category Theory | implemented (`monoidal-categories`) |
| `math.comp.computational-reproducibility` | Computational reproducibility | Computation | implemented (`computational-reproducibility`) |
| `math.comp.experimental-mathematics` | Experimental mathematics: conjectures and counterexamples | Computation | implemented (`experimental-mathematics`) |
| `math.comp.formal-methods` | Formal methods | Computation | implemented (`formal-methods`) |
| `math.discrete.probabilistic-method` | The probabilistic method | Discrete Mathematics | implemented (`probabilistic-method`) |
| `math.found.axiomatic-set-theory` | Axiomatic set theory: hierarchy, cardinal arithmetic and L | Foundations | implemented (`axiomatic-set-theory`) |
| `math.found.descriptive-set-theory` | Descriptive set theory | Foundations | implemented (`descriptive-set-theory`) |
| `math.found.forcing` | Forcing and independence | Foundations | implemented (`forcing`) |
| `math.found.incompleteness` | Gödel's incompleteness theorems | Foundations | implemented (`incompleteness`) |
| `math.found.model-theory` | Model theory | Foundations | implemented (`model-theory`) |
| `math.found.proof-theory` | Proof theory | Foundations | implemented (`proof-theory`) |
| `math.found.reading-literature` | Reading the mathematical literature | Foundations | implemented (`reading-literature`) |
| `math.geom.algebraic-geometry` | Algebraic geometry | Geometry & Topology | implemented (`algebraic-geometry`) |
| `math.geom.algebraic-topology` | Algebraic topology | Geometry & Topology | implemented (`algebraic-topology`) |
| `math.geom.differential-topology` | Differential topology | Geometry & Topology | implemented (`differential-topology`) |
| `math.geom.homotopy-theory` | Homotopy theory | Geometry & Topology | implemented (`homotopy-theory`) |
| `math.geom.lie-groups` | Lie groups and Lie algebras | Geometry & Topology | implemented (`lie-groups`) |
| `math.geom.riemann-surfaces` | Riemann surfaces | Geometry & Topology | implemented (`riemann-surfaces`) |
| `math.geom.riemannian-geometry` | Riemannian geometry | Geometry & Topology | implemented (`riemannian-geometry`) |
| `math.geom.sheaves` | Sheaves | Geometry & Topology | implemented (`sheaves`) |
| `math.geom.smooth-manifolds` | Smooth manifolds | Geometry & Topology | implemented (`smooth-manifolds`) |
| `math.geom.vector-bundles-characteristic-classes` | Vector bundles and characteristic classes | Geometry & Topology | implemented (`vector-bundles-characteristic-classes`) |
| `math.number.algebraic-number-theory` | Algebraic number theory | Number | implemented (`algebraic-number-theory`) |
| `math.number.analytic-number-theory` | Analytic number theory | Number | implemented (`analytic-number-theory`) |
| `math.prob.measure-theoretic-probability` | Measure-theoretic probability | Probability & Statistics | implemented (`measure-theoretic-probability`) |
| `math.prob.stochastic-processes` | Stochastic processes | Probability & Statistics | implemented (`stochastic-processes`) |

### Research pathways (Research)

| Id | Title | Subject | Status |
|---|---|---|---|
| `math.algebra.quiver-representations` | Quiver representations | Algebra | implemented (`quiver-representations`) |
| `math.analysis.geometric-analysis` | Geometric analysis | Analysis | implemented (`geometric-analysis`) |
| `math.applied.gauge-theory` | Gauge theory and the geometry of physics | Applied Mathematics | implemented (`gauge-theory`) |
| `math.cat.categorical-representation-theory` | Categorical representation theory | Category Theory | implemented (`categorical-representation-theory`) |
| `math.cat.derived-categories` | Derived categories | Category Theory | implemented (`derived-categories`) |
| `math.cat.higher-categories` | Higher categories | Category Theory | implemented (`higher-categories`) |
| `math.cat.infinity-categories` | ∞-categories | Category Theory | implemented (`infinity-categories`) |
| `math.cat.stable-infinity-categories` | Stable ∞-categories | Category Theory | implemented (`stable-infinity-categories`) |
| `math.cat.triangulated-categories` | Triangulated categories | Category Theory | implemented (`triangulated-categories`) |
| `math.comp.formalising-published-mathematics` | Formalising published mathematics | Computation | implemented (`formalising-published-mathematics`) |
| `math.discrete.additive-extremal-combinatorics` | Extremal and additive combinatorics | Discrete Mathematics | implemented (`additive-extremal-combinatorics`) |
| `math.found.homotopy-type-theory` | Homotopy type theory | Foundations | implemented (`homotopy-type-theory`) |
| `math.found.large-cardinals` | Large cardinals | Foundations | implemented (`large-cardinals`) |
| `math.found.research-ethics` | Research ethics and attribution | Foundations | implemented (`research-ethics`) |
| `math.geom.complex-kahler-geometry` | Complex and Kähler geometry; Hodge theory | Geometry & Topology | implemented (`complex-kahler-geometry`) |
| `math.geom.geometric-group-theory` | Geometric group theory | Geometry & Topology | implemented (`geometric-group-theory`) |
| `math.geom.low-dimensional-topology` | Low-dimensional topology: 3- and 4-manifolds | Geometry & Topology | implemented (`low-dimensional-topology`) |
| `math.geom.stable-homotopy-theory` | Stable homotopy theory and generalised cohomology | Geometry & Topology | implemented (`stable-homotopy-theory`) |
| `math.geom.symplectic-geometry` | Symplectic geometry and topology | Geometry & Topology | implemented (`symplectic-geometry`) |
| `math.number.arithmetic-geometry` | Arithmetic geometry and elliptic curves | Number | implemented (`arithmetic-geometry`) |
| `math.number.langlands-programme` | The Langlands programme: an orientation | Number | implemented (`langlands-programme`) |
| `math.prob.random-geometry` | Random structures: walks, percolation and random geometry | Probability & Statistics | implemented (`random-geometry`) |
<!-- /generated:index -->
