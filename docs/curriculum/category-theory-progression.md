# Category-theory progression

<!-- Tables in this document were generated from content/math/graph/graph.json and pathways.json when it was written. Update them whenever the graph changes. -->

Category theory is a major structural language of higher mathematics in Lumenary Math, not a graduate appendix. It begins with precursors that young children can play with, becomes explicit at the end of secondary school, and reaches higher and derived categories in the optional research pathways. Set theory develops alongside it (see `set-theory-progression.md`).

## Principles

- **Precursors without terminology.** At K–2 and Grades 3–5 learners do, undo and chain actions, and draw arrows between things. Words such as 'category', 'morphism' and 'functor' are not used. These activities prepare for composition and identities; they are not presented as category theory.
- **Analogy is labelled as analogy.** Where a lesson or Wonder Trail compares something to a categorical idea without a formal construction, it says so (the trail schema has an `analogyNote` field for this). A connection is called a construction only when it is one: for example, a monoid really is a one-object category, and a preorder really is a thin category.
- **Rigorous prerequisites.** Each topic's required prerequisites are listed below. Graduate and research topics also require substantial algebra and topology, because their examples come from there.
- **Category theory alongside sets, not instead of them.** School and undergraduate mathematics are built on sets. Category theory is introduced as a language for structure that sits alongside set theory; `foundations-relationships.md` explains how the two relate.

## Stage by stage

### Elementary school (K–5): precursors

- Transformations, processes, identity operations and reversible operations: **Doing and undoing** (`math.cat.actions-and-undoing`, K–2).
- Composition and relationships between objects: **One thing after another** (`math.cat.chaining-actions`, 3–5), including the socks-and-shoes rule for undoing a chain.
- Related precursors in other lanes: slides, turns and flips in **Symmetry: slides, turns and flips** (`math.geom.symmetry-transformations`, 3–5), and step-by-step instructions in **Following and giving precise instructions** (`math.comp.following-instructions`, K–2).

### Middle school (Grades 6–8)

- Functions as mappings: **Functions** (`math.found.functions`, 6–8).
- Function composition and identity functions: **Function machines in sequence** (`math.cat.chaining-functions`, 6–8).
- Simple commutative diagrams and structure-preserving transformations: **Diagrams where paths agree** (`math.cat.commutative-diagrams-intro`, 6–8), where 'f preserves addition' is shown as a square whose two paths agree; also **Rigid motions, congruence and similarity** (`math.geom.rigid-motions-similarity`, 6–8).

### High school (Grades 9–12)

- Composition and associativity, with the identity laws proved: **Composition** (`math.cat.composition`, 9–12).
- Isomorphisms, concrete homomorphisms and structural similarity: **Structure-preserving maps: homomorphisms and isomorphisms** (`math.cat.structure-preserving-maps`, 9–12).
- An introductory universal property: **Products by maps: a first universal property** (`math.cat.intro-universal-properties`, 9–12), which characterises the Cartesian product by maps into it.

### Early undergraduate

- Categories, objects and morphisms, identity morphisms and associative composition; the categories of sets, groups, vector spaces and posets; opposite categories: **Categories** (`math.cat.categories`, UG 1).
- Functors: **Functors** (`math.cat.functors`, UG 1).
- Basic universal properties: **Universal properties** (`math.cat.universal-properties`, UG 1).

### Advanced undergraduate

- Natural transformations: **Natural transformations** (`math.cat.natural-transformations`, UG 2).
- Products and coproducts, initial and terminal objects: **Products, coproducts, initial and terminal objects** (`math.cat.products-coproducts`, UG 2).
- Limits and colimits: **Limits and colimits** (`math.cat.limits-colimits`, UG 2).
- Adjunctions: **Adjunctions** (`math.cat.adjunctions`, UG 2).
- Representable functors: **Representable functors** (`math.cat.representable-functors`, UG 2).
- The Yoneda lemma: **The Yoneda lemma** (`math.cat.yoneda`, UG 2).

### First-year graduate

- Monads: **Monads** (`math.cat.monads`, Grad).
- Monoidal categories: **Monoidal categories** (`math.cat.monoidal-categories`, Grad).
- Abelian categories: **Abelian categories** (`math.cat.abelian-categories`, Grad).
- Enriched categories: **Enriched categories** (`math.cat.enriched-categories`, Grad).
- Categorical logic: **Categorical logic** (`math.cat.categorical-logic`, Grad).
- Elementary topos theory: **Elementary topos theory** (`math.cat.elementary-topoi`, Grad).
- Advanced universal constructions: **Kan extensions** (`math.cat.kan-extensions`, Grad).
- Applications to algebra, topology, geometry and representation theory, through **Homological algebra** (`math.algebra.homological-algebra`, Grad), **Sheaves** (`math.geom.sheaves`, Grad), **Algebraic topology** (`math.geom.algebraic-topology`, Grad) and **Representation theory of finite groups** (`math.algebra.representation-theory`, Grad).

### Optional research pathways

- Higher category theory: **Higher categories** (`math.cat.higher-categories`, Research).
- ∞-categories: **∞-categories** (`math.cat.infinity-categories`, Research).
- Homotopy type theory: **Homotopy type theory** (`math.found.homotopy-type-theory`, Research). It is placed in the Foundations lane because it is a type theory, and tagged as part of this progression.
- Derived categories: **Derived categories** (`math.cat.derived-categories`, Research).
- Triangulated categories: **Triangulated categories** (`math.cat.triangulated-categories`, Research).
- Stable ∞-categories: **Stable ∞-categories** (`math.cat.stable-infinity-categories`, Research).
- Categorical representation theory: **Categorical representation theory** (`math.cat.categorical-representation-theory`, Research).

## Topics in the progression

| Level | Id | Title | Required prerequisites |
|---|---|---|---|
| K–2 | `math.cat.actions-and-undoing` | Doing and undoing | — |
| 3–5 | `math.cat.chaining-actions` | One thing after another | `cat.actions-and-undoing` |
| 6–8 | `math.cat.chaining-functions` | Function machines in sequence | `found.functions`, `cat.chaining-actions` |
| 6–8 | `math.cat.commutative-diagrams-intro` | Diagrams where paths agree | `cat.chaining-functions` |
| 6–8 | `math.found.functions` | Functions | `found.sets`, `number.integers` |
| 9–12 | `math.cat.composition` | Composition | `found.functions` |
| 9–12 | `math.cat.intro-universal-properties` | Products by maps: a first universal property | `cat.composition` |
| 9–12 | `math.cat.structure-preserving-maps` | Structure-preserving maps: homomorphisms and isomorphisms | `cat.composition` |
| UG 1 | `math.cat.categories` | Categories | `cat.structure-preserving-maps`, `algebra.algebraic-structures` |
| UG 1 | `math.cat.functors` | Functors | `cat.categories` |
| UG 1 | `math.cat.universal-properties` | Universal properties | `cat.categories`, `cat.intro-universal-properties` |
| UG 2 | `math.cat.adjunctions` | Adjunctions | `cat.natural-transformations`, `cat.universal-properties` |
| UG 2 | `math.cat.limits-colimits` | Limits and colimits | `cat.products-coproducts`, `cat.natural-transformations` |
| UG 2 | `math.cat.natural-transformations` | Natural transformations | `cat.functors` |
| UG 2 | `math.cat.products-coproducts` | Products, coproducts, initial and terminal objects | `cat.universal-properties` |
| UG 2 | `math.cat.representable-functors` | Representable functors | `cat.natural-transformations` |
| UG 2 | `math.cat.yoneda` | The Yoneda lemma | `cat.representable-functors` |
| Grad | `math.cat.abelian-categories` | Abelian categories | `cat.limits-colimits`, `algebra.modules` |
| Grad | `math.cat.categorical-logic` | Categorical logic | `cat.adjunctions`, `cat.products-coproducts`, `found.type-theory` |
| Grad | `math.cat.elementary-topoi` | Elementary topos theory | `cat.categorical-logic`, `cat.limits-colimits`, `cat.yoneda` |
| Grad | `math.cat.enriched-categories` | Enriched categories | `cat.monoidal-categories` |
| Grad | `math.cat.kan-extensions` | Kan extensions | `cat.adjunctions`, `cat.limits-colimits`, `cat.yoneda` |
| Grad | `math.cat.monads` | Monads | `cat.adjunctions` |
| Grad | `math.cat.monoidal-categories` | Monoidal categories | `cat.natural-transformations`, `cat.products-coproducts` |
| Research | `math.cat.categorical-representation-theory` | Categorical representation theory | `cat.higher-categories`, `cat.abelian-categories`, `algebra.representation-theory` |
| Research | `math.cat.derived-categories` | Derived categories | `cat.abelian-categories`, `algebra.homological-algebra` |
| Research | `math.cat.higher-categories` | Higher categories | `cat.monoidal-categories` |
| Research | `math.cat.infinity-categories` | ∞-categories | `cat.higher-categories`, `geom.algebraic-topology` |
| Research | `math.cat.stable-infinity-categories` | Stable ∞-categories | `cat.infinity-categories`, `cat.triangulated-categories` |
| Research | `math.cat.triangulated-categories` | Triangulated categories | `cat.derived-categories` |
| Research | `math.found.homotopy-type-theory` | Homotopy type theory | `found.type-theory`, `geom.algebraic-topology` |

## Wonder Trails along the progression

Category theory is one of the principal destinations of Wonder Trails. Two trails follow this progression directly:

| From | To | Trail | Connection |
|---|---|---|---|
| found.functions | cat.intro-universal-properties | products-by-maps | A function into a Cartesian product A × B is exactly a pair of functions, one into A and one into B: the first example of a universal property. |
| cat.composition | cat.categories | arrows-that-compose | Sets and functions, with composition and identity functions, are the motivating example of a category: the category Set. |
| cat.composition | cat.functors | arrows-that-compose | A functor sends objects to objects and arrows to arrows, preserving composition and identities. |
| cat.composition | cat.infinity-categories | arrows-that-compose | In an ∞-category, composites exist and are unique only up to a contractible space of choices, so associativity holds up to coherent homotopy rather than strictly. |
| cat.composition | cat.universal-properties | products-by-maps | Universal properties describe objects by how arrows compose with them; for example, a product is characterised by the maps into it. |
| cat.intro-universal-properties | cat.products-coproducts | products-by-maps | In any category, a product of A and B is defined by exactly this property; for groups it is the direct product, for topological spaces the product topology. |
| cat.categories | cat.natural-transformations | arrows-that-compose | Once there are maps between categories (functors), one can ask for maps between functors: natural transformations. |
| cat.categories | cat.higher-categories | arrows-that-compose | Categories themselves, with functors and natural transformations, form a 2-category, the starting point of higher category theory. |
| cat.universal-properties | cat.limits-colimits | products-by-maps | Products, equalisers, pullbacks and their duals are all limits or colimits: one universal property covering many constructions. |
| cat.universal-properties | cat.kan-extensions | products-by-maps | Limits and colimits are themselves special Kan extensions, along the functor to the category with one object and one morphism. |
| cat.limits-colimits | cat.adjunctions | products-by-maps | Limits are right adjoints: taking limits of J-shaped diagrams is right adjoint to the diagonal functor C → [J, C], and right adjoints preserve all limits. |
| cat.adjunctions | cat.yoneda | products-by-maps | A functor G : D → C has a left adjoint if and only if, for each object A of C, the functor Hom_C(A, G(−)) : D → Set is representable; the Yoneda lemma then assembles the representing objects into a functor. |

## Discovery edges into category theory from other subjects

These optional edges show where categorical ideas appear in other lanes. None of them is required.

| From | Subject | To | Connection |
|---|---|---|---|
| comp.following-instructions | Computation | cat.chaining-actions | A list of instructions is a chain of actions carried out one after another. |
| number.addition-subtraction | Number | cat.actions-and-undoing | 'Add 3' and 'take away 3' are actions that undo each other. |
| algebra.expressions-and-unknowns | Algebra | cat.chaining-actions | 'Multiply by 3, then add 1' is a chain of actions; to undo it, subtract 1 first and then divide by 3. |
| found.sets | Foundations | cat.intro-universal-properties | The Cartesian product, met here as a set of ordered pairs, can also be characterised by how functions into it behave. |
| geom.symmetry-transformations | Geometry & Topology | cat.chaining-actions | Doing one move after another, and undoing a move, are early examples of composing and reversing actions. |
| algebra.linear-relationships | Algebra | cat.chaining-functions | Composing two linear functions gives another: applying x ↦ m₂x + b₂ and then x ↦ m₁x + b₁ gives x ↦ m₁m₂x + (m₁b₂ + b₁). |
| found.equivalence-relations | Foundations | cat.universal-properties | The quotient map A → A/~ is universal: every function out of A that is constant on equivalence classes factors through it in exactly one way. |
| found.functions | Foundations | cat.intro-universal-properties | A function into a Cartesian product A × B is exactly a pair of functions, one into A and one into B: the first example of a universal property. |
| geom.rigid-motions-similarity | Geometry & Topology | cat.structure-preserving-maps | Isometries are the structure-preserving maps of the plane with its distances: composites and inverses of isometries are again isometries. |
| analysis.exponential-logarithmic-functions | Analysis | cat.structure-preserving-maps | exp is an isomorphism from (ℝ, +) to (ℝ>0, ×), with inverse ln: it translates one structure exactly into the other. |
| analysis.functions-and-graphs | Analysis | cat.composition | Composition of functions is associative and has identities, the first axioms of a category. |
| discrete.graph-basics | Discrete Mathematics | cat.structure-preserving-maps | A graph isomorphism is a structure-preserving bijection whose inverse also preserves structure. |
| algebra.algebraic-structures | Algebra | cat.functors | A monoid can be viewed as a category with one object, and a monoid homomorphism is then exactly a functor between such categories. |
| algebra.algebraic-structures | Algebra | cat.monads | A monad is a monoid in a category of endofunctors, with composition as the product: the monoid idea reappears one level up. |
| algebra.linear-algebra | Algebra | cat.categories | Vector spaces and linear maps form a category: composites of linear maps are linear and identity maps are linear. |
| analysis.multivariable-calculus | Analysis | cat.functors | The chain rule says that taking derivatives respects composition; in categorical language, differentiation at a point is functorial. |
| found.first-order-logic | Foundations | cat.categorical-logic | Categorical logic interprets first-order theories in categories other than the category of sets, such as toposes; models in sets are one special case. |
| found.order-theory | Foundations | cat.categories | A preorder is exactly a category with at most one morphism between any two objects; order-preserving maps between preorders are then exactly functors. |
| geom.transformation-geometry | Geometry & Topology | cat.categories | Klein's idea can be recast categorically: a group is a one-object category in which every morphism is invertible, and a geometry studies what such morphisms preserve. |
| number.number-system-constructions | Number | cat.universal-properties | The field of fractions has a universal property: every injective ring homomorphism from an integral domain into a field extends uniquely to its field of fractions. |
| algebra.advanced-linear-algebra | Algebra | cat.natural-transformations | The isomorphism V → V** is natural in V while V ≅ V* is not; making this distinction precise was a motivation for Eilenberg and Mac Lane's definition of natural transformation. |
| algebra.advanced-linear-algebra | Algebra | cat.monoidal-categories | Vector spaces with the tensor product form a symmetric monoidal category. |
| algebra.fields-galois | Algebra | cat.adjunctions | The Galois correspondence is an instance of a Galois connection, which is an adjunction between partially ordered sets (one taken with the opposite order). |
| algebra.groups | Algebra | cat.functors | An action of G on a set X is the same thing as a functor from the one-object category BG to the category of sets. |
| algebra.quotients | Algebra | cat.limits-colimits | The quotient G → G/N is a coequaliser in the category of groups (of the inclusion N → G and the trivial homomorphism); quotients in general are colimits. |
| comp.lambda-calculus | Computation | cat.categorical-logic | The simply typed λ-calculus with products is an internal language for cartesian closed categories (Lambek). |
| found.zfc | Foundations | cat.elementary-topoi | Lawvere's Elementary Theory of the Category of Sets (ETCS) axiomatises sets through functions instead of membership; without an added replacement axiom it is strictly weaker than ZFC. |
| geom.point-set-topology | Geometry & Topology | cat.universal-properties | Product and quotient topologies are characterised by universal properties: they are the coarsest, respectively finest, topologies making the relevant maps continuous. |
| algebra.homological-algebra | Algebra | cat.abelian-categories | Abelian categories axiomatise the setting in which homological algebra works; Grothendieck's Tôhoku paper (1957) developed derived functors in that generality. |
| algebra.modules | Algebra | cat.adjunctions | The tensor–hom adjunction Hom(M ⊗ N, P) ≅ Hom(M, Hom(N, P)), natural in all three variables, is a basic example of an adjunction. |
| algebra.path-algebras | Algebra | cat.categories | The paths in a quiver form the free category generated by that quiver, and the path algebra is its linearisation. |
| algebra.representation-theory | Algebra | cat.functors | A representation of G is a functor from the one-object category BG to the category of vector spaces, and intertwining maps are natural transformations between such functors. |
| found.forcing | Foundations | cat.elementary-topoi | Cohen's construction can be presented as passing to a topos of sheaves on a poset of conditions, as in Mac Lane and Moerdijk's treatment of the independence of CH. |
| found.proof-theory | Foundations | cat.categorical-logic | Proofs modulo normalisation can be organised into categories: proofs in the conjunction–implication fragment of intuitionistic logic correspond to morphisms of free cartesian closed categories. |
| geom.algebraic-geometry | Geometry & Topology | cat.derived-categories | Derived categories arose in Grothendieck and Verdier's work on duality theory in algebraic geometry. |
| geom.sheaves | Geometry & Topology | cat.elementary-topoi | Sheaves on a space form a Grothendieck topos, a central example of an elementary topos. |
| geom.smooth-manifolds | Geometry & Topology | cat.functors | The tangent construction is a functor from smooth manifolds to vector bundles, and the chain rule is precisely the statement that it preserves composition. |
| algebra.quiver-representations | Algebra | cat.categorical-representation-theory | Lusztig used the geometry of spaces of quiver representations to construct canonical bases of quantum groups, an important source of categorification. |
| found.homotopy-type-theory | Foundations | cat.infinity-categories | Shulman (2019) showed that every Grothendieck (∞,1)-topos gives a model of homotopy type theory with univalent universes. |
| found.large-cardinals | Foundations | cat.higher-categories | Grothendieck universes, which correspond to inaccessible cardinals, are a common way of handling size issues in category theory. |

## Discovery edges from category theory to other subjects

| From | To | Subject | Connection |
|---|---|---|---|
| cat.actions-and-undoing | algebra.groups | Algebra | Collections of actions that can be combined and that can all be undone are studied in group theory. |
| cat.chaining-actions | algebra.groups | Algebra | The socks-and-shoes rule (gh)⁻¹ = h⁻¹g⁻¹ holds in every group. |
| cat.composition | algebra.algebraic-structures | Algebra | The functions from a set to itself form a monoid under composition, and the bijections form a group. |
| cat.structure-preserving-maps | algebra.groups | Algebra | The first isomorphism theorem identifies the image of any group homomorphism with a quotient of its domain. |
| cat.structure-preserving-maps | found.model-theory | Foundations | Isomorphic structures satisfy the same first-order sentences, but structures satisfying the same sentences need not be isomorphic. |
| cat.functors | geom.fundamental-group | Geometry & Topology | π₁ is a functor, and functoriality gives a short proof of the Brouwer fixed-point theorem for the disc. |
| cat.adjunctions | comp.lambda-calculus | Computation | Currying, the adjunction − × B ⊣ (−)^B, is the basis of function types in the typed λ-calculus. |
| cat.natural-transformations | geom.algebraic-topology | Geometry & Topology | Eilenberg and Mac Lane introduced categories, functors and natural transformations (1945) to make precise the naturality of constructions in algebraic topology, such as homology. |
| cat.products-coproducts | comp.lambda-calculus | Computation | Product and sum types in programming languages correspond to products and coproducts. |
| cat.representable-functors | geom.algebraic-geometry | Geometry & Topology | Grothendieck's functor of points views a scheme X through the functor Hom(−, X); many moduli problems ask whether a given functor is representable. |
| cat.yoneda | found.homotopy-type-theory | Foundations | In homotopy type theory, path induction can be seen as a type-theoretic analogue of the Yoneda lemma for identity types. |
| cat.abelian-categories | geom.sheaves | Geometry & Topology | Sheaves of abelian groups form an abelian category, the setting for sheaf cohomology. |
| cat.categorical-logic | found.homotopy-type-theory | Foundations | Dependent type theories with identity types have models in homotopical and higher-categorical structures, which led to homotopy type theory. |
| cat.monads | comp.formal-methods | Computation | Moggi (1991) showed that monads structure the semantics of computational effects; they are central in languages such as Haskell. |
| cat.monoidal-categories | applied.quantum-mechanics | Applied Mathematics | Symmetric monoidal categories with duals, such as finite-dimensional Hilbert spaces, are the setting of categorical quantum mechanics (Abramsky and Coecke). |
| cat.derived-categories | algebra.quiver-representations | Algebra | Happel described the bounded derived category of the path algebra of a Dynkin quiver Q in terms of the repetitive quiver ℤQ. |
| cat.higher-categories | found.homotopy-type-theory | Foundations | Higher-dimensional structure also appears in type theory: the iterated identity types of a type form a weak ∞-groupoid (Lumsdaine; van den Berg and Garner). |
