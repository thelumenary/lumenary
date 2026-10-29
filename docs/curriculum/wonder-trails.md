# Wonder Trails

<!-- The section between the generated:trails markers is produced from content/math/trails/*/en.mdx and graph.json by `npm run docs:curriculum`; do not edit it by hand. -->

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

- `kind` classifies the trail (algebraic, modular, quotient, category, set-theory, logic, analysis, history, topology, geometry, number-theory, probability, computability or physics).
- `analogyNote` must be filled in whenever the trail uses an intuitive analogy rather than a formal construction, saying exactly where the analogy stops.

## Rules

- **Never graded, never required.** Trails do not affect grades, mastery, progress or access to any lesson. A learner who never opens a trail loses nothing, and the site does not nag, reward streaks or rank anyone.
- **Experience before terminology.** Learners experiment first; names come afterwards. Elementary trails do not require terms such as 'quotient ring', 'group' or 'category'.
- **Mathematically accurate at every level.** A simplified statement must still be true. When a trail compares an idea to a more advanced one, it says whether the connection is a theorem, a construction or an analogy.
- **Evidence is not proof.** Trails that use computation say whether a result is exact, numerical, experimental or proved.
- **Linked to the graph.** Each `deeper` topic should be the target of a discovery edge in `graph.json` that names the trail. Discovery edges are optional by definition: they never become required edges.

## Trails and their chains

Each trail walks a chain of discovery edges, from an implemented lesson towards graduate or research mathematics. The tables below are generated from the discovery edges that name each trail.

<!-- generated:trails -->
### `arrows-that-compose` — Arrows that compose

- **Kind:** category
- **Inviting question:** What do functions between sets, maps between groups and continuous maps between shapes have in common? What if we studied only the arrows?
- **Starts from:** `math.cat.composition` (Composition)
- **Leads to:** Categories (`cat.categories`), Functors (`cat.functors`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| cat.composition | 9–12 | cat.categories | UG 1 | Sets and functions, with composition and identity functions, are the motivating example of a category: the category Set. |
| cat.composition | 9–12 | cat.functors | UG 1 | A functor sends objects to objects and arrows to arrows, preserving composition and identities. |
| cat.composition | 9–12 | cat.infinity-categories | Research | In an ∞-category, composites exist and are unique only up to a contractible space of choices, so associativity holds up to coherent homotopy rather than strictly. |
| cat.categories | UG 1 | cat.natural-transformations | UG 2 | Once there are maps between categories (functors), one can ask for maps between functors: natural transformations. |
| cat.categories | UG 1 | cat.higher-categories | Research | Categories themselves, with functors and natural transformations, form a 2-category, the starting point of higher category theory. |

### `bending-roads` — How sharply does a road bend?

- **Kind:** geometry
- **Inviting question:** Driving along a winding road, how sharply does it bend at each point? Is there a circle that fits the road best at each point — and what is its radius?
- **Starts from:** `math.analysis.intro-calculus` (Introductory calculus)
- **Leads to:** Differential geometry of curves and surfaces (`geom.curves-surfaces`), Riemannian geometry (`geom.riemannian-geometry`), The geometry of spacetime: special and general relativity (`applied.relativity`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| analysis.intro-calculus | 9–12 | geom.curves-surfaces | UG 2 | Driving along a winding road, how sharply does it bend at each point? Is there a circle that fits the road best at each point — and what is its radius? |

### `boxes-in-boxes` — Boxes inside boxes

- **Kind:** set-theory
- **Inviting question:** What is inside a box that contains only an empty box? Is it empty? And can every description you can think of make a collection?
- **Starts from:** `math.found.collections` (Collections)
- **Leads to:** Sets (`found.sets`), Russell's paradox and why sets need axioms (`found.russell-paradox`), ZFC: axiomatic set theory (`found.zfc`)
- **Analogy note:** Boxes are a picture of sets; a set is determined only by its elements, while real boxes have sizes and colours.

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.collections | K–2 | found.russell-paradox | 9–12 | A collection can itself be a member of another collection, like a box inside a box. Pushing this to 'the collection of all collections that are not members of themselves' leads to Russell's paradox. |
| found.sets | 3–5 | found.russell-paradox | 9–12 | Sets can have sets as elements, and {∅} ≠ ∅. Allowing every property to define a set leads to Russell's paradox. |
| found.sets | 3–5 | found.zfc | UG 2 | Nesting alone builds numbers: von Neumann's construction 0 = ∅, 1 = {∅}, 2 = {∅, {∅}}, … defines the natural numbers inside axiomatic set theory. |
| found.russell-paradox | 9–12 | found.zfc | UG 2 | Zermelo proposed axioms avoiding the paradox in 1908; with the axiom of replacement (Fraenkel, Skolem) and the axiom of choice these became ZFC. |
| found.zfc | UG 2 | found.axiomatic-set-theory | Grad | Iterating 'sets of sets' transfinitely builds the cumulative hierarchy V_α; with the axiom of foundation, every set appears at some stage. |
| found.zfc | UG 2 | found.large-cardinals | Research | If ZFC is consistent, it cannot prove that an inaccessible cardinal exists; at an inaccessible κ, the stage V_κ of the hierarchy is itself a model of ZFC. |

### `can-a-computer-decide` — Can a computer decide?

- **Kind:** computability
- **Inviting question:** Some programs stop and some loop forever. Could someone write one clever program that looks at any program, together with its input, and always correctly says whether it will stop?
- **Starts from:** `math.comp.loops-and-conditions` (Repetition and decisions)
- **Leads to:** Computability (`comp.computability`), Gödel's incompleteness theorems (`found.incompleteness`), Computational complexity (`comp.complexity-theory`)
- **Analogy note:** The experiment shows Cantor's diagonal argument for 0–1 sequences. The halting proof below uses the same diagonal idea, applied to programs; the experiment is an illustration of the idea, not the halting proof itself.

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| comp.loops-and-conditions | 3–5 | comp.computability | UG 2 | Can we always tell whether a program will stop? No algorithm can decide this for every program: the halting problem is undecidable. |

### `clock-arithmetic` — Clock arithmetic

- **Kind:** modular
- **Inviting question:** It's 9 o'clock. What time will it be in 5 hours — and in 29 hours? Can a clock teach us a whole new kind of arithmetic?
- **Starts from:** `math.number.integers` (Integers)
- **Leads to:** Clock arithmetic: remainders and modular arithmetic (`number.modular-arithmetic`), Congruences (`number.congruences`), Quotient groups and quotient rings (`algebra.quotients`)

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

### `corners-edges-faces` — Corners, edges and faces

- **Kind:** topology
- **Inviting question:** Count the corners, edges and faces of a cube, then work out corners − edges + faces. Try a pyramid and a tetrahedron too. Why do you keep getting the same number — and can you find a shape that gives a different one?
- **Starts from:** `math.geom.shapes` (Shapes)
- **Leads to:** Surfaces, polyhedra and the Euler characteristic (`geom.surfaces-euler-characteristic`), Algebraic topology (`geom.algebraic-topology`), Riemannian geometry (`geom.riemannian-geometry`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| geom.shapes | K–2 | geom.surfaces-euler-characteristic | UG 1 | Counting the corners, edges and faces of solid shapes leads to Euler's formula V − E + F = 2, one of the founding results of topology. |

### `halfway-to-the-wall` — Halfway to the wall

- **Kind:** analysis
- **Inviting question:** Walk halfway to a wall. Then walk half of what is left, then half of that, and so on, forever. Do you ever reach the wall? How can infinitely many steps add up to a finite distance?
- **Starts from:** `math.number.fractions` (Fractions and decimals)
- **Leads to:** Sequences and series (`analysis.sequences-series`), Real analysis (`analysis.real-analysis`), Measure theory and integration (`analysis.measure-theory`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| number.fractions | 3–5 | analysis.sequences-series | 9–12 | Walk halfway to a wall. Then walk half of what is left, then half of that, and so on, forever. Do you ever reach the wall? How can infinitely many steps add up to a finite distance? |

### `how-many-infinities` — How many infinities?

- **Kind:** set-theory
- **Inviting question:** There are infinitely many counting numbers and infinitely many infinite 0–1 sequences. Are these two infinities the same size?
- **Starts from:** `math.found.sets` (Sets)
- **Leads to:** Countability and Cantor's diagonal argument (`found.countability`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.sets | 3–5 | found.countability | 9–12 | Matching elements one-to-one compares the sizes of finite sets; the same idea applied to infinite sets shows that some infinite sets are strictly larger than others. |
| found.sets | 3–5 | found.cardinals | UG 2 | Cardinal numbers extend 'number of elements' from finite sets to all sets. |
| found.countability | 9–12 | found.forcing | Grad | Is there a set strictly larger than ℕ but smaller than ℝ? This is the continuum hypothesis; Gödel (1940) and Cohen (1963) showed that, if ZFC is consistent, it can be neither proved nor refuted in ZFC. |
| found.cardinals | UG 2 | found.forcing | Grad | ZFC does not decide the value of 2^ℵ₀: Cohen's forcing shows that, if ZFC is consistent, so is ZFC + 2^ℵ₀ = ℵ₂, and many other values are possible. |
| found.cardinals | UG 2 | found.large-cardinals | Research | Beyond the alephs lie inaccessible, measurable and larger cardinals whose existence ZFC cannot prove. |

### `inverses-and-structure` — Inverses and structure

- **Kind:** algebraic
- **Inviting question:** Every integer can be added to another integer to get $0$. So why can almost no integer be multiplied by another integer to get <!-- generated:trails -->
$?
- **Starts from:** `math.number.integers` (Integers)
- **Leads to:** Algebraic structures: monoids, groups and rings (`algebra.algebraic-structures`), Groups (`algebra.groups`), Rings, ideals and fields (`algebra.rings`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| number.integers | 6–8 | algebra.algebraic-structures | UG 1 | Under addition the integers have an identity (0) and every element has an inverse: they form a group. Under multiplication only 1 and −1 have inverses, so ℤ is a ring but not a field. |
| number.integers | 6–8 | algebra.groups | UG 2 | (ℤ, +) is the infinite cyclic group, generated by 1. |
| number.integers | 6–8 | algebra.rings | UG 2 | (ℤ, +, ×) is the prototype of a commutative ring with identity; enlarging it to ℚ gives every non-zero element a multiplicative inverse. |
| algebra.algebraic-structures | UG 1 | cat.monads | Grad | A monad is a monoid in a category of endofunctors, with composition as the product: the monoid idea reappears one level up. |
| algebra.rings | UG 2 | algebra.commutative-algebra | Grad | Ideals of polynomial rings correspond to geometric shapes cut out by equations, the starting point of commutative algebra and algebraic geometry. |

### `knots-and-colours` — Knots and colours

- **Kind:** topology
- **Inviting question:** Tie a knot in a piece of string and glue the two ends together. How could you prove that it really is knotted — that no amount of wiggling, without cutting, will turn it into a plain loop?
- **Starts from:** `math.discrete.networks-puzzles` (Dots and lines: networks and puzzles)
- **Leads to:** Knot theory (`geom.knot-theory`), Low-dimensional topology: 3- and 4-manifolds (`geom.low-dimensional-topology`), Categorical representation theory (`cat.categorical-representation-theory`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| discrete.networks-puzzles | 3–5 | geom.knot-theory | UG 2 | Tie a knot in a piece of string and glue the two ends together. How could you prove that it really is knotted — that no amount of wiggling, without cutting, will turn it into a plain loop? |

### `life-on-a-torus` — Life on a torus

- **Kind:** topology
- **Inviting question:** In some video games, walking off the right edge of the screen brings you back on the left, and walking off the top brings you back at the bottom. If that world were a real surface, what shape would it be?
- **Starts from:** `math.geom.coordinate-plane` (The coordinate plane)
- **Leads to:** Surfaces, polyhedra and the Euler characteristic (`geom.surfaces-euler-characteristic`), Homotopy and the fundamental group (`geom.fundamental-group`), Low-dimensional topology: 3- and 4-manifolds (`geom.low-dimensional-topology`)
- **Analogy note:** The game screen is a flat rectangle with a rule for its edges; a doughnut in space is curved. They have the same topology but not the same geometry, so 'the screen is a doughnut' is a statement about shape up to stretching, not a picture of the game.

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| geom.coordinate-plane | 6–8 | geom.surfaces-euler-characteristic | UG 1 | In some video games, walking off the right edge of the screen brings you back on the left, and walking off the top brings you back at the bottom. If that world were a real surface, what shape would it be? |

### `loops-around-a-hole` — Loops around a hole

- **Kind:** topology
- **Inviting question:** Walk around a tree and come back to where you started. How many times did you go around it? Can you change that number by wandering differently — without ever walking through the tree?
- **Starts from:** `math.number.complex-numbers` (Complex numbers)
- **Leads to:** Homotopy and the fundamental group (`geom.fundamental-group`), Complex analysis (`analysis.complex-analysis`), Algebraic topology (`geom.algebraic-topology`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| number.complex-numbers | 9–12 | geom.fundamental-group | UG 2 | Walk around a tree and come back to where you started. How many times did you go around it? Can you change that number by wandering differently — without ever walking through the tree? |

### `primes-forever` — Primes forever

- **Kind:** number-theory
- **Inviting question:** 2, 3, 5, 7, 11, 13, … The primes get rarer as the numbers grow. Do they ever run out? And how rare do they get?
- **Starts from:** `math.number.factors-primes` (Factors, multiples and primes)
- **Leads to:** Divisibility, Euclid's algorithm and unique factorisation (`number.divisibility-gcd`), Number theory (`number.elementary-number-theory`), Analytic number theory (`number.analytic-number-theory`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| number.factors-primes | 3–5 | number.divisibility-gcd | 9–12 | 2, 3, 5, 7, 11, 13, … The primes get rarer as the numbers grow. Do they ever run out? And how rare do they get? |

### `products-by-maps` — The product, by its maps

- **Kind:** category
- **Inviting question:** Can you describe the set of pairs $A \times B$ without ever looking inside it — only by how functions go into it?
- **Starts from:** `math.found.functions` (Functions)
- **Leads to:** Universal properties (`cat.universal-properties`), Limits and colimits (`cat.limits-colimits`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.functions | 6–8 | cat.intro-universal-properties | 9–12 | A function into a Cartesian product A × B is exactly a pair of functions, one into A and one into B: the first example of a universal property. |
| cat.composition | 9–12 | cat.universal-properties | UG 1 | Universal properties describe objects by how arrows compose with them; for example, a product is characterised by the maps into it. |
| cat.intro-universal-properties | 9–12 | cat.products-coproducts | UG 2 | In any category, a product of A and B is defined by exactly this property; for groups it is the direct product, for topological spaces the product topology. |
| cat.universal-properties | UG 1 | cat.limits-colimits | UG 2 | Products, equalisers, pullbacks and their duals are all limits or colimits: one universal property covering many constructions. |
| cat.universal-properties | UG 1 | cat.kan-extensions | Grad | Limits and colimits are themselves special Kan extensions, along the functor to the category with one object and one morphism. |
| cat.limits-colimits | UG 2 | cat.adjunctions | UG 2 | Limits are right adjoints: taking limits of J-shaped diagrams is right adjoint to the diagonal functor C → [J, C], and right adjoints preserve all limits. |
| cat.adjunctions | UG 2 | cat.yoneda | UG 2 | A functor G : D → C has a left adjoint if and only if, for each object A of C, the functor Hom_C(A, G(−)) : D → Set is representable; the Yoneda lemma then assembles the representing objects into a functor. |

### `remainder-families` — Remainder families

- **Kind:** quotient
- **Inviting question:** Sort every integer — positive, negative and zero — into families by its remainder after dividing by 3. If you add a member of one family to a member of another, does the family of the answer depend on which members you chose?
- **Starts from:** `math.number.integers` (Integers)
- **Leads to:** Relations, equivalence relations and partitions (`found.equivalence-relations`), Congruences (`number.congruences`), Quotient groups and quotient rings (`algebra.quotients`)
- **Analogy note:** Colouring is a picture of the partition; the mathematical object is the set of residue classes itself.

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| found.equivalence-relations | 6–8 | algebra.quotients | UG 2 | Collapsing each class to a single point gives a quotient set; when the relation respects an operation, the quotient inherits it, giving quotient groups and rings such as ℤ/nℤ. |
| found.equivalence-relations | 6–8 | cat.universal-properties | UG 1 | The quotient map A → A/~ is universal: every function out of A that is constant on equivalence classes factors through it in exactly one way. |
| number.integers | 6–8 | found.equivalence-relations | 6–8 | Grouping integers by their remainder on division by n splits ℤ into n families, the classes of an equivalence relation. |
| number.integers | 6–8 | number.number-system-constructions | UG 1 | The integers can be constructed from the natural numbers as equivalence classes of pairs (a, b), thought of as a − b. |
| algebra.quotients | UG 2 | cat.limits-colimits | UG 2 | The quotient G → G/N is a coequaliser in the category of groups (of the inclusion N → G and the trivial homomorphism); quotients in general are colimits. |

### `symmetry-makes-groups` — Symmetry makes groups

- **Kind:** algebraic
- **Inviting question:** A square can be turned or flipped and still fit exactly into its outline. How many different moves like that are there? And what do you get if you do one move and then another?
- **Starts from:** `math.geom.symmetry-transformations` (Symmetry: slides, turns and flips)
- **Leads to:** Groups (`algebra.groups`), Matrix groups and continuous symmetry (`geom.matrix-groups`), Lie groups and Lie algebras (`geom.lie-groups`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| geom.symmetry-transformations | 3–5 | algebra.groups | UG 2 | The symmetries of a shape can be combined and undone; together they form a group, such as the 8-element dihedral group of a square. |

### `triangles-on-a-ball` — Triangles on a ball

- **Kind:** geometry
- **Inviting question:** On flat paper the angles of every triangle add up to 180°, and a² + b² = c² in every right triangle. Draw a triangle on a ball instead. Is either rule still true?
- **Starts from:** `math.geom.pythagorean-theorem` (The Pythagorean theorem)
- **Leads to:** Non-Euclidean geometry: spherical and hyperbolic (`geom.non-euclidean-geometry`), Differential geometry of curves and surfaces (`geom.curves-surfaces`), Riemannian geometry (`geom.riemannian-geometry`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| geom.pythagorean-theorem | 6–8 | geom.non-euclidean-geometry | UG 1 | On a sphere a² + b² = c² fails for right triangles; for small triangles it holds approximately, and the error measures the curvature. |

### `why-ellipses` — Why do planets move on ellipses?

- **Kind:** physics
- **Inviting question:** Planets move around the Sun on ellipses, with the Sun at one focus. Why ellipses — and not circles, egg shapes or spirals?
- **Starts from:** `math.geom.conic-sections` (Conic sections)
- **Leads to:** Classical mechanics (`applied.classical-mechanics`), The geometry of spacetime: special and general relativity (`applied.relativity`), Symplectic geometry and topology (`geom.symplectic-geometry`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| geom.conic-sections | 9–12 | applied.classical-mechanics | UG 1 | Kepler's first law says planets move on ellipses with the Sun at a focus; Newton derived it from the inverse-square law of gravitation. |

### `will-the-walker-return` — Will the walker return?

- **Kind:** probability
- **Inviting question:** A walker tosses a fair coin every minute: heads, one step east; tails, one step west. Is she certain to come back to where she started? What if she can also step north and south — or up and down in space?
- **Starts from:** `math.prob.probability-intro` (Probability)
- **Leads to:** Markov chains (`prob.markov-chains`), Stochastic processes (`prob.stochastic-processes`), Random structures: walks, percolation and random geometry (`prob.random-geometry`)

| From | Level | To | Level | Connection |
|---|---|---|---|---|
| prob.probability-intro | 6–8 | prob.markov-chains | UG 2 | A walker tosses a fair coin every minute: heads, one step east; tails, one step west. Is she certain to come back to where she started? What if she can also step north and south — or up and down in space? |
<!-- /generated:trails -->
