# Foundational relationships

<!-- Tables in this document were generated from content/math/graph/graph.json and pathways.json when it was written. Update them whenever the graph changes. -->

Lumenary Math teaches several foundational frameworks, each with its own topics in the graph: set theory, category theory, type theory, mathematical logic, computability, proof theory and model theory. This document explains how they connect and how they differ. **They are not interchangeable.** Each can be studied inside or alongside the others, and there are precise translations between some of them, but they have different primitive notions, different notions of sameness, and different questions that make sense to ask.

## The frameworks in brief

| Framework | Primitive notions | Typical question | Where it starts in the graph |
|---|---|---|---|
| Axiomatic set theory (ZFC) | sets and membership ∈ | Which sets exist, and how large are they? | **Sets** (`math.found.sets`), then **ZFC: axiomatic set theory** (`math.found.zfc`) |
| Category theory | objects, morphisms, composition | How do structures relate, and what is preserved? | **Composition** (`math.cat.composition`), then **Categories** (`math.cat.categories`) |
| Type theory | terms, types, typing judgements | What can be constructed, and what does a proof compute? | **Type theory and propositions as types** (`math.found.type-theory`) |
| First-order logic | formulas, structures, proofs | What follows from what? | **Propositional logic and truth tables** (`math.found.propositional-logic`), **First-order logic** (`math.found.first-order-logic`) |
| Model theory | structures satisfying theories | What do the models of a theory look like? | **Model theory** (`math.found.model-theory`) |
| Proof theory | derivations as objects | What do proofs contain, and how strong is a theory? | **Proof theory** (`math.found.proof-theory`) |
| Computability | algorithms, Turing machines | What can be computed or decided at all? | **Computability** (`math.comp.computability`) |

## How they connect

- **Logic frames set theory.** ZFC is a first-order theory, so understanding it as a formal theory requires first-order logic; in the graph, **ZFC: axiomatic set theory** (`math.found.zfc`) requires **First-order logic** (`math.found.first-order-logic`).
- **Completeness bridges proof and truth.** Gödel's completeness theorem says that a first-order sentence is provable from a theory exactly when it is true in every model of the theory. It links proof theory (⊢) to model theory (⊨): **Completeness, compactness and Löwenheim–Skolem** (`math.found.completeness-theorem`).
- **Computability is needed for incompleteness.** 'Effectively axiomatised' is a notion from computability theory, and the first incompleteness theorem applies to consistent, recursively axiomatised theories that interpret enough arithmetic: **Gödel's incompleteness theorems** (`math.found.incompleteness`) requires **Computability** (`math.comp.computability`).
- **Set theory and model theory meet in independence.** Gödel's constructible universe and Cohen's forcing build models of ZFC to show that statements such as the continuum hypothesis are independent of ZFC: **Axiomatic set theory: hierarchy, cardinal arithmetic and L** (`math.found.axiomatic-set-theory`), **Forcing and independence** (`math.found.forcing`).
- **Proofs, programs and categories.** The Curry–Howard correspondence identifies propositions with types and proofs with programs; Lambek extended it to cartesian closed categories. Proof normalisation corresponds to evaluation of typed λ-terms: **The λ-calculus** (`math.comp.lambda-calculus`), **Type theory and propositions as types** (`math.found.type-theory`), **Categorical logic** (`math.cat.categorical-logic`).
- **Toposes generalise the category of sets.** An elementary topos is a category that behaves enough like Set to interpret (intuitionistic) higher-order logic. Lawvere's ETCS axiomatises Set categorically; without an added replacement axiom it is strictly weaker than ZFC: **Elementary topos theory** (`math.cat.elementary-topoi`).
- **Types as spaces.** Homotopy type theory interprets types as ∞-groupoids and identifications as paths, connecting type theory with homotopy theory and ∞-categories: **Homotopy type theory** (`math.found.homotopy-type-theory`).

## Distinctions that must not be blurred

### Elements versus morphisms

In set theory a set is determined by its elements (extensionality), and membership x ∈ A is a basic relation between any two sets. In category theory an object has no elements a priori; it is known through the morphisms into and out of it.

In Set, elements of A correspond exactly to functions from a one-element set to A, so elements can be recovered from morphisms. In other categories this fails: in the category of groups, every homomorphism from the trivial group is trivial, and it is homomorphisms from ℤ that pick out elements, because ℤ represents the forgetful functor. The Yoneda lemma makes precise the sense in which an object is determined by the morphisms into it from all objects (**The Yoneda lemma** (`math.cat.yoneda`)). That is a theorem about categories, not a claim that objects 'are' sets of elements.

### Equality versus isomorphism

In ZFC, A = B means A and B have the same elements. The sets {0, 1} and {a, b} (with a ≠ b) are different but isomorphic in Set. Category theory deliberately treats isomorphic objects alike: universal constructions are determined only up to unique isomorphism, and a well-formed categorical property is invariant under isomorphism.

Type theories take further positions. In Lean, equality is a proposition satisfying uniqueness of identity proofs, and isomorphic types are not thereby equal. In homotopy type theory, Voevodsky's univalence axiom makes equality of types equivalent to equivalence of types. Univalence is incompatible with uniqueness of identity proofs for the universe, so it cannot be added to Lean's built-in equality without inconsistency. 'Equal' therefore means different things in different frameworks, and lessons always say which framework they are using.

### Functions versus functors

A function assigns to each element of its domain one element of its codomain. A functor assigns to each object an object and to each morphism a morphism, preserving composition and identities. Some special functors are essentially functions (a function between sets is a functor between discrete categories, and a monotone map between posets is a functor between the corresponding thin categories). In general, however, a functor carries more information than a function on objects, and functors between large categories, such as the forgetful functor Grp → Set, are not functions between sets in ZFC at all, because their domains are proper classes. Size issues are handled with classes or with Grothendieck universes, which correspond to inaccessible cardinals (**Large cardinals** (`math.found.large-cardinals`)).

### Set-theoretic constructions versus universal properties

The ordered pair (a, b) can be encoded in ZFC as the Kuratowski pair {{a}, {a, b}}, and A × B as a set of such pairs. This is a construction: it proves that products of sets exist. The encoding also has incidental features ('junk theorems', such as {a} ∈ (a, b)) that no mathematician uses.

The universal property of the product, that maps X → A × B correspond to pairs of maps X → A and X → B, characterises A × B up to unique isomorphism, makes sense in any category, and says nothing about incidental features. Constructions establish existence; universal properties identify what matters and give uniqueness. Both are needed, and they are not the same thing: **Products by maps: a first universal property** (`math.cat.intro-universal-properties`), **Universal properties** (`math.cat.universal-properties`).

### Formal type theory versus axiomatic set theory

ZFC is a first-order theory with one sort (sets) and one relation (∈). Every mathematical object is encoded as a set, so a question such as 'is 0 ∈ 3?' is well-formed, and with von Neumann numerals its answer is yes. Dependent type theories such as Lean's take terms and types as primitive. Every term has a type, so that question is not well-typed. Proofs are themselves terms, and classical principles such as excluded middle and choice are added as explicit axioms.

Each framework can interpret the other under suitable assumptions. For example, set-theoretic models of type-theoretic universes typically use inaccessible cardinals, and sets can be modelled inside type theory. These interpretations are mathematical theorems with hypotheses, not a statement that the frameworks are the same. A result formalised in Lean is a theorem of Lean's type theory, and transferring it to ZFC needs such an interpretation.

## What 'not interchangeable' means in practice

- Lessons state which framework they work in. School and undergraduate lessons work in naive set theory, with ZFC as the background axiomatic theory unless stated otherwise. Lean exercises work in Lean's type theory.
- Translations between frameworks are taught as theorems with hypotheses, not as renaming.
- Category theory is taught as a language that can be developed on top of set theory (with size conventions). Its use as an alternative foundation (ETCS, topos theory) is taught as a separate, optional topic with its own strengths and limits.
- No lesson claims that one framework is 'the true foundation'. Comparing foundations is itself a mathematical subject, with established results and open questions.

## Topics tagged as foundational relationships

| Level | Id | Title | Required prerequisites |
|---|---|---|---|
| 3–5 | `math.found.logic-statements` | True, false, and, or, not | — |
| 6–8 | `math.found.quantifiers` | Set-builder notation, quantifiers and infinite sets | `found.sets`, `found.logic-statements` |
| 9–12 | `math.found.proof-techniques` | Proof: direct, contrapositive, contradiction and induction | `found.propositional-logic`, `number.integers` |
| 9–12 | `math.found.propositional-logic` | Propositional logic and truth tables | `found.logic-statements`, `found.quantifiers` |
| 9–12 | `math.found.russell-paradox` | Russell's paradox and why sets need axioms | `found.quantifiers`, `found.proof-techniques` |
| UG 1 | `math.found.first-order-logic` | First-order logic | `found.propositional-logic` |
| UG 2 | `math.comp.computability` | Computability | `comp.algorithms-and-efficiency`, `found.countability` |
| UG 2 | `math.comp.lambda-calculus` | The λ-calculus | `comp.programming-intro`, `found.proof-techniques` |
| UG 2 | `math.found.completeness-theorem` | Completeness, compactness and Löwenheim–Skolem | `found.first-order-logic`, `found.countability` |
| UG 2 | `math.found.type-theory` | Type theory and propositions as types | `found.first-order-logic`, `comp.lambda-calculus` |
| UG 2 | `math.found.zfc` | ZFC: axiomatic set theory | `found.first-order-logic` |
| Grad | `math.cat.categorical-logic` | Categorical logic | `cat.adjunctions`, `cat.products-coproducts`, `found.type-theory` |
| Grad | `math.cat.elementary-topoi` | Elementary topos theory | `cat.categorical-logic`, `cat.limits-colimits`, `cat.yoneda` |
| Grad | `math.found.forcing` | Forcing and independence | `found.axiomatic-set-theory` |
| Grad | `math.found.incompleteness` | Gödel's incompleteness theorems | `found.completeness-theorem`, `comp.computability` |
| Grad | `math.found.model-theory` | Model theory | `found.completeness-theorem` |
| Grad | `math.found.proof-theory` | Proof theory | `found.incompleteness`, `found.cardinals` |
| Research | `math.found.homotopy-type-theory` | Homotopy type theory | `found.type-theory`, `geom.algebraic-topology` |

## Discovery edges among these topics

| From | To | Connection |
|---|---|---|
| found.logic-statements | found.incompleteness | Is every true statement about whole numbers provable? Gödel showed that any consistent, effectively axiomatised theory containing enough arithmetic leaves some true arithmetic statements unprovable. |
| found.quantifiers | found.first-order-logic | Quantifiers become part of a precise formal language with explicit rules of inference. |
| found.proof-techniques | found.proof-theory | Proofs can themselves be studied as mathematical objects; Gentzen's cut-elimination theorem is a central example. |
| found.propositional-logic | found.type-theory | In constructive logic and type theory, a proof of P → Q is a method turning proofs of P into proofs of Q, and P ∨ ¬P is not assumed as a law. |
| found.russell-paradox | found.zfc | Zermelo proposed axioms avoiding the paradox in 1908; with the axiom of replacement (Fraenkel, Skolem) and the axiom of choice these became ZFC. |
| found.russell-paradox | found.type-theory | Russell's own response was a theory of types, which stratifies objects by type; modern type theories descend in part from this idea. |
| found.first-order-logic | comp.computability | Church and Turing (1936) showed that no algorithm decides first-order validity, answering Hilbert's Entscheidungsproblem negatively. |
| found.first-order-logic | cat.categorical-logic | Categorical logic interprets first-order theories in categories other than the category of sets, such as toposes; models in sets are one special case. |
| comp.computability | comp.lambda-calculus | Church's λ-calculus computes exactly the same functions as Turing machines. |
| comp.lambda-calculus | cat.categorical-logic | The simply typed λ-calculus with products is an internal language for cartesian closed categories (Lambek). |
| found.type-theory | found.proof-theory | Normalisation of typed λ-terms corresponds to removing detours in natural-deduction proofs, a central theme of proof theory. |
| found.zfc | cat.elementary-topoi | Lawvere's Elementary Theory of the Category of Sets (ETCS) axiomatises sets through functions instead of membership; without an added replacement axiom it is strictly weaker than ZFC. |
| found.zfc | found.type-theory | Lean is founded not on ZFC but on a dependent type theory. Each foundation can model the other given suitable assumptions, but they are not interchangeable. |
| cat.categorical-logic | found.homotopy-type-theory | Dependent type theories with identity types have models in homotopical and higher-categorical structures, which led to homotopy type theory. |
| found.forcing | cat.elementary-topoi | Cohen's construction can be presented as passing to a topos of sheaves on a poset of conditions, as in Mac Lane and Moerdijk's treatment of the independence of CH. |
| found.model-theory | found.forcing | Forcing builds new models of ZFC from old ones, a model-theoretic method at the heart of independence proofs. |
| found.proof-theory | cat.categorical-logic | Proofs modulo normalisation can be organised into categories: proofs in the conjunction–implication fragment of intuitionistic logic correspond to morphisms of free cartesian closed categories. |
