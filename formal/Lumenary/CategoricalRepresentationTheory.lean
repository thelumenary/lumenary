/-
The Lumenary — formal mathematics
Categorical representation theory: categorification and decategorification, Grothendieck
groups, and the tensor category of representations of a group.

Mathlib has finite types and their cardinalities, finite-dimensional linear algebra, and the
category `FDRep k G` of finite-dimensional representations of a group `G` with its monoidal,
symmetric and (right) rigid structures, together with characters. Here we prove the
decategorification statements of the lesson: cardinality turns `⊕` and `×` of finite sets
(and the distributivity bijection) into `+` and `·`; dimension is additive on short exact
sequences, which is what makes it factor through the Grothendieck group `K₀`; the Euler
characteristic of a two-term complex equals the Euler characteristic of its homology; and the
character turns `⊗` into `·`. Finally, the Fibonacci fusion rule `τ ⊗ τ = 1 ⊕ τ` admits no
integer-valued dimension, so it is not the Grothendieck ring of any `Rep(G)`. Not formalised
here (and largely not in Mathlib at this version): fusion categories in general, module
categories, categorical actions, Khovanov homology.
-/
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.IntervalCases

open CategoryTheory MonoidalCategory

namespace Lumenary.CategoricalRepresentationTheory

universe u

/-! ### Finite sets categorify the natural numbers -/

-- @region categorical_representation_theory.card_sum
-- @provenance library
/-- Decategorifying the disjoint union: `|A ⊔ B| = |A| + |B|`. This applies Mathlib's
`Fintype.card_sum`. -/
theorem card_sum (A B : Type*) [Fintype A] [Fintype B] :
    Fintype.card (A ⊕ B) = Fintype.card A + Fintype.card B :=
  Fintype.card_sum
-- @endregion

-- @region categorical_representation_theory.card_prod
-- @provenance library
/-- Decategorifying the product: `|A × B| = |A| · |B|`. This applies Mathlib's
`Fintype.card_prod`. -/
theorem card_prod (A B : Type*) [Fintype A] [Fintype B] :
    Fintype.card (A × B) = Fintype.card A * Fintype.card B :=
  Fintype.card_prod A B
-- @endregion

-- @region categorical_representation_theory.card_distrib
-- @provenance independent
/-- The distributive law `a(b + c) = ab + ac` is the shadow of a *bijection*
`A × (B ⊔ C) ≃ (A × B) ⊔ (A × C)` (Mathlib's `Equiv.prodSumDistrib`). Categorified, an equation
between numbers becomes an isomorphism between sets — extra information that the numbers forget
(which bijection?). -/
theorem card_distrib (A B C : Type*) [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A × (B ⊕ C)) = Fintype.card (A × B) + Fintype.card (A × C) := by
  rw [Fintype.card_congr (Equiv.prodSumDistrib A B C), Fintype.card_sum]
-- @endregion

/-! ### Dimension, Grothendieck groups and Euler characteristics -/

section Linear

variable {k : Type*} [Field k] {A B C V₁ V₀ : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₀] [Module k V₀]

-- @region categorical_representation_theory.finrank_additive
-- @provenance independent
/-- Dimension is additive on short exact sequences `0 → A --f--> B --g--> C → 0`:
`dim B = dim A + dim C`. Proof by rank–nullity for `g`: `dim B = dim im g + dim ker g`, where
`im g = C` (surjectivity) and `ker g = im f ≅ A` (exactness and injectivity). This is exactly
the relation `[B] = [A] + [C]` defining the Grothendieck group, so `dim` induces a homomorphism
`K₀(vect_k) → ℤ` (in fact an isomorphism). -/
theorem finrank_additive [FiniteDimensional k B] (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : LinearMap.range f = LinearMap.ker g) :
    Module.finrank k B = Module.finrank k A + Module.finrank k C := by
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hA : Module.finrank k (LinearMap.range f) = Module.finrank k A :=
    LinearMap.finrank_range_of_inj hf
  have hC : Module.finrank k (LinearMap.range g) = Module.finrank k C := by
    rw [LinearMap.range_eq_top.mpr hg, finrank_top]
  rw [← hexact, hA, hC] at hrn
  omega
-- @endregion

-- @region categorical_representation_theory.euler_characteristic_two_term
-- @provenance independent
/-- For a two-term complex `V₁ --d--> V₀` of finite-dimensional spaces, the Euler
characteristic of the complex equals that of its homology:
`dim V₀ - dim V₁ = dim H₀ - dim H₁`, where `H₀ = coker d = V₀ / im d` and `H₁ = ker d`.
Homology *categorifies* the Euler characteristic: it replaces a number by graded vector spaces
whose alternating dimension recovers it. Proof: rank–nullity for `d`, and
`dim (V₀ / im d) + dim im d = dim V₀`. -/
theorem euler_characteristic_two_term [FiniteDimensional k V₁] [FiniteDimensional k V₀]
    (d : V₁ →ₗ[k] V₀) :
    (Module.finrank k V₀ : ℤ) - Module.finrank k V₁ =
      (Module.finrank k (V₀ ⧸ LinearMap.range d) : ℤ) - Module.finrank k (LinearMap.ker d) := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker d
  have h₀ := Submodule.finrank_quotient_add_finrank (LinearMap.range d)
  omega
-- @endregion

end Linear

/-! ### The tensor category `Rep(G)` -/

section Rep

variable (k : Type u) [Field k] (G : Type u) [Group G]

-- @region categorical_representation_theory.fdrep_symmetric
-- @provenance library
/-- Finite-dimensional representations form a symmetric monoidal category under `⊗` (with `g`
acting diagonally): the swap `β : V ⊗ W ≅ W ⊗ V` squares to the identity. This applies
Mathlib's instance `SymmetricCategory (FDRep k G)` and the axiom `SymmetricCategory.symmetry`.
(In a merely *braided* category, such as the representations of a quantum group, this fails.) -/
theorem fdrep_symmetric (V W : FDRep k G) : (β_ V W).hom ≫ (β_ W V).hom = 𝟙 (V ⊗ W) :=
  SymmetricCategory.symmetry V W
-- @endregion

-- @region categorical_representation_theory.fdrep_zigzag
-- @provenance library
/-- Every finite-dimensional representation `V` has a dual `Vᘁ` with coevaluation
`η : 𝟙 → V ⊗ Vᘁ` and evaluation `ε : Vᘁ ⊗ V → 𝟙` satisfying the zig-zag identity
`(V ◁ ε) ∘ α ∘ (η ▷ V) = ρ⁻¹ ∘ λ`: `FDRep k G` is rigid. This applies Mathlib's instance
`RightRigidCategory (FDRep k G)` (inherited from `FGModuleCat k`) and
`ExactPairing.evaluation_coevaluation`. -/
theorem fdrep_zigzag (V : FDRep k G) :
    η_ V Vᘁ ▷ V ≫ (α_ _ _ _).hom ≫ V ◁ ε_ V Vᘁ = (λ_ V).hom ≫ (ρ_ V).inv :=
  ExactPairing.evaluation_coevaluation V Vᘁ
-- @endregion

-- @region categorical_representation_theory.char_tensor
-- @provenance library
/-- Decategorifying `⊗`: the character of `V ⊗ W` is the product of the characters. Since
characters are additive on direct sums and depend only on the isomorphism class (`char_iso`),
the character is a ring homomorphism from the Grothendieck ring of `Rep(G)` to class
functions. This applies Mathlib's `FDRep.char_tensor`. -/
theorem char_tensor (V W : FDRep k G) : (V ⊗ W).character = V.character * W.character :=
  FDRep.char_tensor V W
-- @endregion

-- @region categorical_representation_theory.char_iso
-- @provenance library
/-- Isomorphic representations have equal characters, so the character only sees the class
`[V]` in the Grothendieck group. This applies Mathlib's `FDRep.char_iso`. -/
theorem char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character :=
  FDRep.char_iso i
-- @endregion

-- @region categorical_representation_theory.char_one
-- @provenance library
/-- Evaluating the character at the identity gives the dimension: `χ_V(1) = dim V`. So
`dim : K₀(Rep G) → ℤ` is a ring homomorphism with positive values on non-zero
representations. This applies Mathlib's `FDRep.char_one`. -/
theorem char_one (V : FDRep k G) : V.character 1 = Module.finrank k V :=
  FDRep.char_one V
-- @endregion

end Rep

/-! ### The Fibonacci fusion rule -/

-- @region categorical_representation_theory.fibonacci_no_integer_dimension
-- @provenance independent
/-- The Fibonacci fusion ring has basis `1, τ` with `τ ⊗ τ = 1 ⊕ τ`. A ring homomorphism to `ℤ`
would send `τ` to an integer `n` with `n² = 1 + n`, and there is none. Since `dim` is a ring
homomorphism `K₀(Rep G) → ℤ` (`char_one`, `char_tensor`), the Fibonacci fusion category is
not `Rep(G)` for any finite group `G`. (Its Frobenius–Perron dimension is the golden ratio.) -/
theorem fibonacci_no_integer_dimension : ¬ ∃ n : ℤ, n ^ 2 = 1 + n := by
  rintro ⟨n, hn⟩
  have h₁ : n ≤ 2 := by nlinarith
  have h₂ : -1 ≤ n := by nlinarith
  interval_cases n <;> omega
-- @endregion

end Lumenary.CategoricalRepresentationTheory
