# Wonder Trails

<!-- Tables in this document were generated from content/math/graph/graph.json and pathways.json when it was written. Update them whenever the graph changes. -->

Wonder Trails are optional invitations to explore mathematics beyond the immediate lesson. They encourage curiosity without introducing compulsory prerequisites. The guiding rule is: **master the present, glimpse the future, never require the future to understand the present.**

## The Wonder Trail schema

Every trail has six parts. Each corresponds to a field of `TrailFrontmatter` in `src/lib/schema.ts` or to the trail's body.

| Part | Purpose | Where it lives |
|---|---|---|
| 1. Inviting question | A concrete, answerable-feeling question that sparks curiosity, phrased for the learner's level. | `question` |
| 2. Progressive hints | Optional hints, each revealing a little more, so learners can experiment before being told. | `hints` (at least one) |
| 3. Experiment, diagram or example | Something to try: a table to fill, a picture to draw, a computation to run. | `experiment` (and optionally `compute` or `lean` ids) |
| 4. Concise explanation | A short, correct explanation of what the experiment shows, with terminology introduced only after the experience. | trail body |
| 5. Link to deeper mathematics | The graph topics where the idea continues. | `deeper` (topic ids) |
| 6. Return to the lesson | A simple way back to where the learner started. | `from` (`lesson` and `label`) |

Two further fields keep trails honest:

- `kind` classifies the trail (algebraic, modular, quotient, category, set-theory, logic, analysis or history).
- `analogyNote` must be filled in whenever the trail uses an intuitive analogy rather than a formal construction, saying exactly where the analogy stops.

## Rules

- **Never graded, never required.** Trails do not affect grades, mastery, progress or access to any lesson. A learner who never opens a trail loses nothing, and the site does not nag, reward streaks or rank anyone.
- **Experience before terminology.** Learners experiment first; names come afterwards. Elementary trails do not require terms such as 'quotient ring', 'group' or 'category'.
- **Mathematically accurate at every level.** A simplified statement must still be true. When a trail compares an idea to a more advanced one, it says whether the connection is a theorem, a construction or an analogy.
- **Evidence is not proof.** Trails that use computation say whether a result is exact, numerical, experimental or proved.
- **Linked to the graph.** Each `deeper` topic should be the target of a discovery edge in `graph.json` that names the trail. Discovery edges are optional by definition: they never become required edges.

## Trails and their chains

Each trail walks a chain of discovery edges, from an implemented lesson towards graduate or research mathematics. The tables below are generated from the discovery edges that name each trail.

### `boxes-in-boxes`

- **Inviting question (example):** Can a box hold a box that holds nothing? Is that box empty?
- **Starts from:** `math.found.collections` (Collections)
- **Arc:** Collections can contain collections; {∅} ≠ ∅; nesting leads to Russell's paradox, ZFC, the cumulative hierarchy and large cardinals.
- **Topics on the trail:** `found.collections`, `found.sets`, `found.russell-paradox`, `found.zfc`, `found.axiomatic-set-theory`, `found.large-cardinals`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.collections | K–2 | found.russell-paradox | 9–12 | A collection can itself be a member of another collection, like a box inside a box. Pushing this to 'the collection of all collections that are not members of themselves' leads to Russell's paradox. |
| found.sets | 3–5 | found.russell-paradox | 9–12 | Sets can have sets as elements, and {∅} ≠ ∅. Allowing every property to define a set leads to Russell's paradox. |
| found.sets | 3–5 | found.zfc | UG 2 | Nesting alone builds numbers: von Neumann's construction 0 = ∅, 1 = {∅}, 2 = {∅, {∅}}, … defines the natural numbers inside axiomatic set theory. |
| found.russell-paradox | 9–12 | found.zfc | UG 2 | Zermelo proposed axioms avoiding the paradox in 1908; with the axiom of replacement (Fraenkel, Skolem) and the axiom of choice these became ZFC. |
| found.zfc | UG 2 | found.axiomatic-set-theory | Grad | Iterating 'sets of sets' transfinitely builds the cumulative hierarchy V_α; with the axiom of foundation, every set appears at some stage. |
| found.zfc | UG 2 | found.large-cardinals | Research | If ZFC is consistent, it cannot prove that an inaccessible cardinal exists; at an inaccessible κ, the stage V_κ of the hierarchy is itself a model of ZFC. |

### `how-many-infinities`

- **Inviting question (example):** Are there more whole numbers than even numbers? Are some infinities bigger than others?
- **Starts from:** `math.found.sets` (Sets)
- **Arc:** One-to-one matching, countability, Cantor's diagonal argument, cardinals, the continuum hypothesis and large cardinals.
- **Topics on the trail:** `found.sets`, `found.countability`, `found.cardinals`, `found.forcing`, `found.large-cardinals`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.sets | 3–5 | found.countability | 9–12 | Matching elements one-to-one compares the sizes of finite sets; the same idea applied to infinite sets shows that some infinite sets are strictly larger than others. |
| found.sets | 3–5 | found.cardinals | UG 2 | Cardinal numbers extend 'number of elements' from finite sets to all sets. |
| found.countability | 9–12 | found.forcing | Grad | Is there a set strictly larger than ℕ but smaller than ℝ? This is the continuum hypothesis; Gödel (1940) and Cohen (1963) showed that, if ZFC is consistent, it can be neither proved nor refuted in ZFC. |
| found.cardinals | UG 2 | found.forcing | Grad | ZFC does not decide the value of 2^ℵ₀: Cohen's forcing shows that, if ZFC is consistent, so is ZFC + 2^ℵ₀ = ℵ₂, and many other values are possible. |
| found.cardinals | UG 2 | found.large-cardinals | Research | Beyond the alephs lie inaccessible, measurable and larger cardinals whose existence ZFC cannot prove. |

### `inverses-and-structure`

- **Inviting question (example):** Every integer has a partner that adds to zero. Why does almost no integer have a partner that multiplies to one?
- **Starts from:** `math.number.integers` (Integers)
- **Arc:** Inverses, monoids, groups, rings and fields, then monads and commutative algebra.
- **Topics on the trail:** `number.integers`, `algebra.algebraic-structures`, `algebra.groups`, `algebra.rings`, `algebra.commutative-algebra`, `cat.monads`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| number.integers | 6–8 | algebra.algebraic-structures | UG 1 | Under addition the integers have an identity (0) and every element has an inverse: they form a group. Under multiplication only 1 and −1 have inverses, so ℤ is a ring but not a field. |
| number.integers | 6–8 | algebra.groups | UG 2 | (ℤ, +) is the infinite cyclic group, generated by 1. |
| number.integers | 6–8 | algebra.rings | UG 2 | (ℤ, +, ×) is the prototype of a commutative ring with identity; enlarging it to ℚ gives every non-zero element a multiplicative inverse. |
| algebra.algebraic-structures | UG 1 | cat.monads | Grad | A monad is a monoid in a category of endofunctors, with composition as the product: the monoid idea reappears one level up. |
| algebra.rings | UG 2 | algebra.commutative-algebra | Grad | Ideals of polynomial rings correspond to geometric shapes cut out by equations, the starting point of commutative algebra and algebraic geometry. |

### `clock-arithmetic`

- **Inviting question (example):** What time will it be 100 hours from now?
- **Starts from:** `math.number.integers` (Integers)
- **Arc:** Remainders, modular arithmetic, congruences, ℤ/nℤ, cyclic groups, finite rings and fields, and ideals in rings of integers.
- **Topics on the trail:** `number.integers`, `number.modular-arithmetic`, `number.congruences`, `algebra.fields-galois`, `algebra.groups`, `algebra.quotients`, `algebra.rings`, `number.algebraic-number-theory`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| number.integers | 6–8 | number.modular-arithmetic | 6–8 | On a clock, adding 12 hours changes nothing: arithmetic with remainders wraps the infinite line of integers into a finite circle. |
| number.integers | 6–8 | number.congruences | UG 1 | a ≡ b (mod n) means that n divides a − b; congruence respects addition and multiplication. |
| number.modular-arithmetic | 6–8 | number.congruences | UG 1 | Clock arithmetic becomes the theory of congruences: a ≡ b (mod n) when n divides a − b, an equivalence relation that respects + and ×. |
| number.modular-arithmetic | 6–8 | algebra.groups | UG 2 | The hours of a 12-hour clock under addition form a cyclic group of order 12. |
| number.congruences | UG 1 | algebra.quotients | UG 2 | The congruence classes modulo n are the elements of the quotient ring ℤ/nℤ, and reduction mod n is the quotient homomorphism ℤ → ℤ/nℤ. |
| number.congruences | UG 1 | algebra.groups | UG 2 | (ℤ/nℤ, +) is the cyclic group of order n, and the invertible classes form the group of units of order φ(n); Euler's theorem then follows from Lagrange's theorem. |
| number.congruences | UG 1 | algebra.rings | UG 2 | ℤ/nℤ is a finite commutative ring, and it is a field exactly when n is prime. |
| number.congruences | UG 1 | algebra.fields-galois | UG 2 | For p prime, ℤ/pℤ is the field 𝔽_p; every finite field has prime-power order pⁿ, and there is exactly one of each such order up to isomorphism. |
| number.congruences | UG 1 | number.algebraic-number-theory | Grad | In rings of integers of number fields one works modulo ideals rather than numbers; Kummer's ideal numbers and Dedekind's ideals grew out of attempts to restore unique factorisation. |

### `remainder-families`

- **Inviting question (example):** If we group the integers by their remainder on division by 3, how many families are there, and do they add and multiply sensibly?
- **Starts from:** `math.number.integers` (Integers)
- **Arc:** Equivalence relations, partitions, quotient sets with their universal property, quotient groups and rings, and quotients as colimits.
- **Topics on the trail:** `found.equivalence-relations`, `number.integers`, `cat.universal-properties`, `number.number-system-constructions`, `algebra.quotients`, `cat.limits-colimits`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.equivalence-relations | 6–8 | algebra.quotients | UG 2 | Collapsing each class to a single point gives a quotient set; when the relation respects an operation, the quotient inherits it, giving quotient groups and rings such as ℤ/nℤ. |
| found.equivalence-relations | 6–8 | cat.universal-properties | UG 1 | The quotient map A → A/~ is universal: every function out of A that is constant on equivalence classes factors through it in exactly one way. |
| number.integers | 6–8 | found.equivalence-relations | 6–8 | Grouping integers by their remainder on division by n splits ℤ into n families, the classes of an equivalence relation. |
| number.integers | 6–8 | number.number-system-constructions | UG 1 | The integers can be constructed from the natural numbers as equivalence classes of pairs (a, b), thought of as a − b. |
| algebra.quotients | UG 2 | cat.limits-colimits | UG 2 | The quotient G → G/N is a coequaliser in the category of groups (of the inclusion N → G and the trivial homomorphism); quotients in general are colimits. |

### `arrows-that-compose`

- **Inviting question (example):** What happens when we follow one arrow and then another? What does an arrow that does nothing do?
- **Starts from:** `math.cat.composition` (Composition)
- **Arc:** Composition and identities, categories, functors, natural transformations, 2-categories and ∞-categories.
- **Topics on the trail:** `cat.composition`, `cat.categories`, `cat.functors`, `cat.natural-transformations`, `cat.higher-categories`, `cat.infinity-categories`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| cat.composition | 9–12 | cat.categories | UG 1 | Sets and functions, with composition and identity functions, are the motivating example of a category: the category Set. |
| cat.composition | 9–12 | cat.functors | UG 1 | A functor sends objects to objects and arrows to arrows, preserving composition and identities. |
| cat.composition | 9–12 | cat.infinity-categories | Research | In an ∞-category, composites exist and are unique only up to a contractible space of choices, so associativity holds up to coherent homotopy rather than strictly. |
| cat.categories | UG 1 | cat.natural-transformations | UG 2 | Once there are maps between categories (functors), one can ask for maps between functors: natural transformations. |
| cat.categories | UG 1 | cat.higher-categories | Research | Categories themselves, with functors and natural transformations, form a 2-category, the starting point of higher category theory. |

### `products-by-maps`

- **Inviting question (example):** Can a Cartesian product be described entirely by how other things map into it?
- **Starts from:** `math.found.functions` (Functions)
- **Arc:** Pairing maps, a first universal property, products in any category, limits, adjunctions, the Yoneda lemma and Kan extensions.
- **Topics on the trail:** `found.functions`, `cat.composition`, `cat.intro-universal-properties`, `cat.universal-properties`, `cat.adjunctions`, `cat.limits-colimits`, `cat.products-coproducts`, `cat.yoneda`, `cat.kan-extensions`

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.functions | 6–8 | cat.intro-universal-properties | 9–12 | A function into a Cartesian product A × B is exactly a pair of functions, one into A and one into B: the first example of a universal property. |
| cat.composition | 9–12 | cat.universal-properties | UG 1 | Universal properties describe objects by how arrows compose with them; for example, a product is characterised by the maps into it. |
| cat.intro-universal-properties | 9–12 | cat.products-coproducts | UG 2 | In any category, a product of A and B is defined by exactly this property; for groups it is the direct product, for topological spaces the product topology. |
| cat.universal-properties | UG 1 | cat.limits-colimits | UG 2 | Products, equalisers, pullbacks and their duals are all limits or colimits: one universal property covering many constructions. |
| cat.universal-properties | UG 1 | cat.kan-extensions | Grad | Limits and colimits are themselves special Kan extensions, along the functor to the category with one object and one morphism. |
| cat.adjunctions | UG 2 | cat.yoneda | UG 2 | A functor G : D → C has a left adjoint if and only if, for each object A of C, the functor Hom_C(A, G(−)) : D → Set is representable; the Yoneda lemma then assembles the representing objects into a functor. |
| cat.limits-colimits | UG 2 | cat.adjunctions | UG 2 | Limits are right adjoints: taking limits of J-shaped diagrams is right adjoint to the diagonal functor C → [J, C], and right adjoints preserve all limits. |

## Untrailed discovery edges

The graph also contains 190 discovery edges that no trail walks yet, across number theory and algebra, topology and category theory, logic and computability, analysis and probability, and more. Each one is a candidate for a future Wonder Trail. Its `note` records the precise connection, and it must be checked again before a trail is written from it.
