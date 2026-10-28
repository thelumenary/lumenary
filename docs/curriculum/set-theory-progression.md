# Set-theory progression

<!-- Tables in this document were generated from content/math/graph/graph.json and pathways.json when it was written. Update them whenever the graph changes. -->

Set theory is the main foundational language of school mathematics and of most undergraduate mathematics in Lumenary Math. This document shows how it develops from sorting toys to forcing and large cardinals, and which topics in the knowledge graph carry each stage. Category theory develops alongside it (see `category-theory-progression.md`); neither replaces the other.

## Principles

- **Naive before axiomatic, and clearly labelled.** Learners use sets informally for years. Axioms are introduced only when there is a reason to need them, beginning with Russell's paradox, and the difference between naive and axiomatic set theory is stated explicitly.
- **No formal axioms for young learners.** At K–2 and Grades 3–5 the words are 'collection', 'member', 'inside', 'same members'. Brace notation appears in Grades 3–5; set-builder notation and quantifiers in Grades 6–8; axioms not before Grades 9–12.
- **Paradoxes explained accurately.** Russell's paradox shows that unrestricted comprehension is inconsistent; it does not show that mathematics is inconsistent. ZF avoids it through the separation schema (and proves x ∉ x through the separate axiom of foundation).
- **Independence is not vagueness.** The continuum hypothesis is neither provable nor refutable in ZFC (if ZFC is consistent); this is a theorem about ZFC, not a sign that the question is meaningless.

## Stage by stage

### Kindergarten–Grade 2

Collections, membership, sorting, classification, equality of collections ('same members'), the empty collection, counting, elementary inclusion and pictures of collections: **Collections** (`math.found.collections`, K–2), with counting developed in **Counting** (`math.number.counting`, K–2). A box containing an empty box is not an empty box; this is the seed of the `boxes-in-boxes` Wonder Trail.

### Grades 3–5

Finite sets, subsets, unions, intersections, complements, the empty set, Venn diagrams, ordered pairs, Cartesian products and elementary cardinality: **Sets** (`math.found.sets`, 3–5). Relations and functions appear informally as input–output rules (**Expressions, unknowns and rules** (`math.algebra.expressions-and-unknowns`, 3–5)) and arrow pictures (**One thing after another** (`math.cat.chaining-actions`, 3–5)); they are defined precisely in Grades 6–8.

### Grades 6–8

Set-builder notation, quantifiers and the first infinite sets: **Set-builder notation, quantifiers and infinite sets** (`math.found.quantifiers`, 6–8). Domains, codomains, injective, surjective and bijective functions: **Functions** (`math.found.functions`, 6–8). Relations, equivalence relations and partitions: **Relations, equivalence relations and partitions** (`math.found.equivalence-relations`, 6–8).

### Grades 9–12

- Rigorous functions: composition, inverses and how injectivity and surjectivity behave under composition, in **Composition** (`math.cat.composition`, 9–12).
- Countability, power sets and Cantor's diagonal argument: **Countability and Cantor's diagonal argument** (`math.found.countability`, 9–12).
- Elementary axiomatic set theory, motivated by paradox: **Russell's paradox and why sets need axioms** (`math.found.russell-paradox`, 9–12).
- Foundations of algebra and analysis: irrationality and completeness in **Real numbers and irrationality** (`math.number.real-numbers`, 9–12), and logic and proof in **Propositional logic and truth tables** (`math.found.propositional-logic`, 9–12) and **Proof: direct, contrapositive, contradiction and induction** (`math.found.proof-techniques`, 9–12).

### Undergraduate

- Order theory, well-orders and Zorn's lemma as a statement: **Orders, lattices and well-orders** (`math.found.order-theory`, UG 1).
- Set-theoretic foundations of the number systems: **Constructing ℤ, ℚ and ℝ** (`math.number.number-system-constructions`, UG 1).
- ZFC: **ZFC: axiomatic set theory** (`math.found.zfc`, UG 2), which requires **First-order logic** (`math.found.first-order-logic`, UG 1) because ZFC is a first-order theory.
- Ordinals, cardinals, transfinite induction and recursion: **Ordinals and cardinals** (`math.found.cardinals`, UG 2).
- Choice principles: **The axiom of choice and its equivalents** (`math.found.axiom-of-choice`, UG 2).

### Graduate and advanced pathways

- Axiomatic set theory, the cumulative hierarchy, cardinal arithmetic and Gödel's L: **Axiomatic set theory: hierarchy, cardinal arithmetic and L** (`math.found.axiomatic-set-theory`, Grad).
- Model-theoretic connections: **Completeness, compactness and Löwenheim–Skolem** (`math.found.completeness-theorem`, UG 2) and **Model theory** (`math.found.model-theory`, Grad).
- Independence and forcing: **Forcing and independence** (`math.found.forcing`, Grad).
- Descriptive set theory: **Descriptive set theory** (`math.found.descriptive-set-theory`, Grad).
- Large cardinals, as optional research-level material: **Large cardinals** (`math.found.large-cardinals`, Research).

## Topics in the progression

| Level | Id | Title | Required prerequisites |
|---|---|---|---|
| K–2 | `math.found.collections` | Collections | — |
| 3–5 | `math.found.sets` | Sets | `found.collections` |
| 6–8 | `math.found.equivalence-relations` | Relations, equivalence relations and partitions | `found.sets` |
| 6–8 | `math.found.functions` | Functions | `found.sets`, `number.integers` |
| 6–8 | `math.found.quantifiers` | Set-builder notation, quantifiers and infinite sets | `found.sets`, `found.logic-statements` |
| 9–12 | `math.cat.composition` | Composition | `found.functions` |
| 9–12 | `math.found.countability` | Countability and Cantor's diagonal argument | `found.functions`, `found.proof-techniques`, `number.real-numbers` |
| 9–12 | `math.found.russell-paradox` | Russell's paradox and why sets need axioms | `found.quantifiers`, `found.proof-techniques` |
| UG 1 | `math.found.order-theory` | Orders, lattices and well-orders | `found.equivalence-relations`, `found.proof-techniques` |
| UG 1 | `math.number.number-system-constructions` | Constructing ℤ, ℚ and ℝ | `found.equivalence-relations`, `found.order-theory`, `number.real-numbers`, `algebra.algebraic-structures` |
| UG 2 | `math.found.axiom-of-choice` | The axiom of choice and its equivalents | `found.cardinals` |
| UG 2 | `math.found.cardinals` | Ordinals and cardinals | `found.zfc`, `found.order-theory`, `found.countability` |
| UG 2 | `math.found.zfc` | ZFC: axiomatic set theory | `found.first-order-logic` |
| Grad | `math.found.axiomatic-set-theory` | Axiomatic set theory: hierarchy, cardinal arithmetic and L | `found.axiom-of-choice`, `found.completeness-theorem` |
| Grad | `math.found.descriptive-set-theory` | Descriptive set theory | `found.cardinals`, `geom.point-set-topology` |
| Grad | `math.found.forcing` | Forcing and independence | `found.axiomatic-set-theory` |
| Grad | `math.found.model-theory` | Model theory | `found.completeness-theorem` |
| Research | `math.found.large-cardinals` | Large cardinals | `found.forcing` |

## Wonder Trails along the progression

Two Wonder Trails follow this progression. They are optional and never affect progression or mastery.

| From | To | Trail | Connection |
|---|---|---|---|
| found.collections | found.russell-paradox | boxes-in-boxes | A collection can itself be a member of another collection, like a box inside a box. Pushing this to 'the collection of all collections that are not members of themselves' leads to Russell's paradox. |
| found.sets | found.russell-paradox | boxes-in-boxes | Sets can have sets as elements, and {∅} ≠ ∅. Allowing every property to define a set leads to Russell's paradox. |
| found.sets | found.zfc | boxes-in-boxes | Nesting alone builds numbers: von Neumann's construction 0 = ∅, 1 = {∅}, 2 = {∅, {∅}}, … defines the natural numbers inside axiomatic set theory. |
| found.sets | found.countability | how-many-infinities | Matching elements one-to-one compares the sizes of finite sets; the same idea applied to infinite sets shows that some infinite sets are strictly larger than others. |
| found.sets | found.cardinals | how-many-infinities | Cardinal numbers extend 'number of elements' from finite sets to all sets. |
| found.countability | found.forcing | how-many-infinities | Is there a set strictly larger than ℕ but smaller than ℝ? This is the continuum hypothesis; Gödel (1940) and Cohen (1963) showed that, if ZFC is consistent, it can be neither proved nor refuted in ZFC. |
| found.russell-paradox | found.zfc | boxes-in-boxes | Zermelo proposed axioms avoiding the paradox in 1908; with the axiom of replacement (Fraenkel, Skolem) and the axiom of choice these became ZFC. |
| found.zfc | found.axiomatic-set-theory | boxes-in-boxes | Iterating 'sets of sets' transfinitely builds the cumulative hierarchy V_α; with the axiom of foundation, every set appears at some stage. |
| found.zfc | found.large-cardinals | boxes-in-boxes | If ZFC is consistent, it cannot prove that an inaccessible cardinal exists; at an inaccessible κ, the stage V_κ of the hierarchy is itself a model of ZFC. |
| found.cardinals | found.forcing | how-many-infinities | ZFC does not decide the value of 2^ℵ₀: Cohen's forcing shows that, if ZFC is consistent, so is ZFC + 2^ℵ₀ = ℵ₂, and many other values are possible. |
| found.cardinals | found.large-cardinals | how-many-infinities | Beyond the alephs lie inaccessible, measurable and larger cardinals whose existence ZFC cannot prove. |

## Relationship to other foundations

Set theory is one framework among several. Its relationship to category theory, type theory and logic, and the reasons these frameworks are not interchangeable, are set out in `foundations-relationships.md`.
