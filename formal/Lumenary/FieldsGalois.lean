/-
The Lumenary — formal mathematics
Fields and Galois theory: degrees and the tower law, minimal polynomials, the impossibility of
doubling the cube, finite fields, the Galois correspondence, and solvability by radicals.

What is proved here and what Mathlib provides. Proved independently: ring homomorphisms out of a
field are injective; `ℤ/p²ℤ` is not a field; `X² − 2` and `X³ − 2` are irreducible over `ℚ`, so
`[ℚ(√2) : ℚ] = 2`; no extension of `ℚ` of degree `2ᵏ` contains a cube root of `2` (the algebraic
heart of "the cube cannot be doubled"); the two maps of the Galois correspondence reverse
inclusions and form a Galois connection; and `|Aut(E/F)| ≤ [E : F]`. Cited from Mathlib: the
tower law, the characteristic-`p` binomial theorem, the size, existence and uniqueness of finite
fields and the cyclicity of their unit groups, Artin's theorem `[E : E^H] = |H|`, the equality
`|Gal(E/F)| = [E : F]` and the fundamental theorem of Galois theory, one direction of
Abel–Ruffini, and the non-solvability of `S₅`.
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Analysis.Real.Sqrt

namespace Lumenary.FieldsGalois

open Polynomial Module IntermediateField

/-! ### Degrees and the tower law -/

-- @region fields_galois.tower_law
-- @provenance library
/-- **Tower law**: for fields `F ⊆ K ⊆ L`, `[L : F] = [L : K] · [K : F]`. If `(kᵢ)` is a basis
of `K` over `F` and `(lⱼ)` a basis of `L` over `K`, the products `kᵢ lⱼ` form a basis of `L`
over `F`. This is Mathlib's `Module.finrank_mul_finrank`. -/
theorem tower_law (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] :
    finrank F K * finrank K L = finrank F L :=
  Module.finrank_mul_finrank F K L
-- @endregion

-- @region fields_galois.field_hom_injective
-- @provenance independent
/-- Every ring homomorphism from a field to a non-zero ring is injective. If `f x = 0` with
`x ≠ 0`, then `1 = f (x * x⁻¹) = f x * f x⁻¹ = 0`, impossible in a non-zero ring. So the kernel
is `0`, and `f a = f b` gives `f (a - b) = 0`, hence `a = b`. This is why a field extension
`K → L` can be viewed as an inclusion. -/
theorem field_hom_injective {K R : Type*} [Field K] [Ring R] [Nontrivial R] (f : K →+* R) :
    Function.Injective f := by
  have hker : ∀ x : K, f x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    apply one_ne_zero (α := R)
    calc (1 : R) = f (x * x⁻¹) := by rw [mul_inv_cancel₀ hx0, map_one]
      _ = 0 := by rw [map_mul, hx, zero_mul]
  intro a b hab
  have := hker (a - b) (by rw [map_sub, hab, sub_self])
  exact sub_eq_zero.mp this
-- @endregion

-- @region fields_galois.zmod_sq_not_field
-- @provenance independent
/-- `ℤ/p²ℤ` is **not** the field with `p²` elements — it is not a field at all: the class of `p`
is non-zero but `p · p = p² = 0`. If `p` had an inverse `b`, then `p = b · p · p = 0`. -/
theorem zmod_sq_not_field (p : ℕ) [hp : Fact p.Prime] : ¬ IsField (ZMod (p ^ 2)) := by
  intro hF
  have hp1 : 1 < p := hp.out.one_lt
  have hpz : (p : ZMod (p ^ 2)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    nlinarith
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hpz
  apply hpz
  calc (p : ZMod (p ^ 2)) = (p * b) * p := by rw [hb, one_mul]
    _ = b * ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by push_cast; ring
    _ = 0 := by rw [ZMod.natCast_self, mul_zero]
-- @endregion

/-! ### Minimal polynomials and ruler-and-compass constructions -/

-- @region fields_galois.sqrt_two_irreducible
-- @provenance independent
/-- `X² − 2` is irreducible over `ℚ`: it has degree 2, so it could only factor with a linear
factor, i.e. a rational root `x` with `x² = 2` — but then `√2 = |x|` would be rational. -/
theorem sqrt_two_irreducible : Irreducible (X ^ 2 - C 2 : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 - C 2 : ℚ[X]).natDegree = 2 := by compute_degree!
    rw [this]
    decide
  · intro x hx
    rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
    apply irrational_sqrt_two
    refine ⟨|x|, ?_⟩
    have h : ((x : ℝ)) ^ 2 = 2 := by exact_mod_cast hx
    rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, h]
-- @endregion

-- @region fields_galois.finrank_sqrt_two
-- @provenance independent
/-- `[ℚ(√2) : ℚ] = 2`. The minimal polynomial of `√2` over `ℚ` is `X² − 2` (monic, irreducible,
vanishing at `√2`), and the degree of a simple extension is the degree of the minimal polynomial
(Mathlib's `IntermediateField.adjoin.finrank`). -/
theorem finrank_sqrt_two : finrank ℚ ℚ⟮(Real.sqrt 2 : ℝ)⟯ = 2 := by
  have hroot : aeval (Real.sqrt 2 : ℝ) (X ^ 2 - C 2 : ℚ[X]) = 0 := by
    simp [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hmonic : (X ^ 2 - C 2 : ℚ[X]).Monic := by monicity!
  have hmin : minpoly ℚ (Real.sqrt 2 : ℝ) = X ^ 2 - C 2 :=
    (minpoly.eq_of_irreducible_of_monic sqrt_two_irreducible hroot hmonic).symm
  have hint : IsIntegral ℚ (Real.sqrt 2 : ℝ) := ⟨_, hmonic, hroot⟩
  rw [IntermediateField.adjoin.finrank hint, hmin]
  compute_degree!
-- @endregion

-- @region fields_galois.cube_two_irreducible
-- @provenance independent
/-- `X³ − 2` is irreducible over `ℚ`. A cubic factors only with a linear factor, i.e. a rational
root `x` with `x³ = 2`. As a real number `x` would be a cube root of `2` lying strictly between
`1` and `2`, so not an integer, and a non-integer root of an integer is irrational
(Mathlib's `irrational_nrt_of_notint_nrt`) — contradicting `x ∈ ℚ`. -/
theorem cube_two_irreducible : Irreducible (X ^ 3 - C 2 : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 3 - C 2 : ℚ[X]).natDegree = 3 := by compute_degree!
    rw [this]
    decide
  · intro x hx
    rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
    have h : ((x : ℝ)) ^ 3 = ((2 : ℤ) : ℝ) := by exact_mod_cast hx
    have hnotint : ∀ y : ℤ, (x : ℝ) ≠ y := by
      intro y hy
      have hy3 : y ^ 3 = 2 := by
        have : ((y : ℝ)) ^ 3 = ((2 : ℤ) : ℝ) := by rw [← hy]; exact h
        exact_mod_cast this
      have h1 : y ≤ 1 ∨ 2 ≤ y := by omega
      rcases h1 with h1 | h1
      · have : y ^ 3 ≤ 1 := by
          rcases le_or_gt 0 y with h0 | h0
          · have : y = 0 ∨ y = 1 := by omega
            rcases this with rfl | rfl <;> norm_num
          · nlinarith [sq_nonneg y]
        omega
      · have : 8 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
        omega
    exact irrational_nrt_of_notint_nrt 3 2 h (by rintro ⟨y, hy⟩; exact hnotint y hy)
      (by norm_num) ⟨x, rfl⟩
-- @endregion

-- @region fields_galois.no_cube_root_two
-- @provenance independent
/-- **Why the cube cannot be doubled (the algebraic half).** No field extension `L` of `ℚ` of
degree `2ᵏ` contains a cube root `α` of `2`: the minimal polynomial of `α` is `X³ − 2`, so
`[ℚ(α) : ℚ] = 3`, and by the tower law `3` divides `[L : ℚ] = 2ᵏ` — impossible. Points
constructible with straightedge and compass lie in such extensions (proved in the lesson, not
here), so `∛2` is not constructible. -/
theorem no_cube_root_two {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] (k : ℕ)
    (hL : finrank ℚ L = 2 ^ k) (α : L) (hα : α ^ 3 = 2) : False := by
  have hroot : aeval α (X ^ 3 - C 2 : ℚ[X]) = 0 := by simp [hα]
  have hmonic : (X ^ 3 - C 2 : ℚ[X]).Monic := by monicity!
  have hmin : minpoly ℚ α = X ^ 3 - C 2 :=
    (minpoly.eq_of_irreducible_of_monic cube_two_irreducible hroot hmonic).symm
  have hint : IsIntegral ℚ α := ⟨_, hmonic, hroot⟩
  have hdeg : finrank ℚ ℚ⟮α⟯ = 3 := by
    rw [IntermediateField.adjoin.finrank hint, hmin]
    compute_degree!
  have hdvd : finrank ℚ ℚ⟮α⟯ ∣ finrank ℚ L := by
    rw [← tower_law ℚ ℚ⟮α⟯ L]
    exact dvd_mul_right _ _
  rw [hdeg, hL] at hdvd
  have := Nat.prime_three.dvd_of_dvd_pow hdvd
  omega
-- @endregion

/-! ### Finite fields -/

-- @region fields_galois.finite_field_card
-- @provenance library
/-- A finite field of characteristic `p` has `pⁿ` elements for some `n ≥ 1`: it is a vector
space of some dimension `n` over its prime field `𝔽_p`. Mathlib's `FiniteField.card`. -/
theorem finite_field_card (K : Type*) [Field K] [Fintype K] (p : ℕ) [CharP K p] :
    ∃ n : ℕ+, Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
  FiniteField.card K p
-- @endregion

-- @region fields_galois.frobenius_add
-- @provenance library
/-- In characteristic `p`, `(a + b)ᵖ = aᵖ + bᵖ`: the binomial coefficients `C(p, k)` with
`0 < k < p` are divisible by `p`. So `x ↦ xᵖ` (Frobenius) is a ring homomorphism.
Mathlib's `add_pow_char`. -/
theorem frobenius_add {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) :
    (a + b) ^ p = a ^ p + b ^ p :=
  add_pow_char a b p
-- @endregion

-- @region fields_galois.galois_field_card
-- @provenance library
/-- **Existence**: for every prime `p` and `n ≥ 1` there is a field with `pⁿ` elements — the
splitting field of `X^(pⁿ) − X` over `𝔽_p`, whose roots are exactly its elements. Mathlib calls
it `GaloisField p n` and proves `GaloisField.card`. -/
theorem galois_field_card (p : ℕ) [Fact p.Prime] (n : ℕ) (h : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n h
-- @endregion

-- @region fields_galois.finite_field_unique
-- @provenance library
/-- **Uniqueness**: two finite fields with the same number of elements are isomorphic (both are
splitting fields of `X^q − X` over `𝔽_p`). Mathlib's `FiniteField.algEquivOfCardEq`. -/
theorem finite_field_unique (p : ℕ) [Fact p.Prime] (K K' : Type*) [Field K] [Field K']
    [Fintype K] [Fintype K'] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
    (h : Fintype.card K = Fintype.card K') : Nonempty (K ≃ₐ[ZMod p] K') :=
  ⟨FiniteField.algEquivOfCardEq p h⟩
-- @endregion

-- @region fields_galois.units_cyclic
-- @provenance library
/-- The multiplicative group of a finite field is cyclic. (More generally, any finite subgroup of
the units of an integral domain is cyclic: Mathlib's `isCyclic_of_subgroup_isDomain`.) -/
theorem units_cyclic (K : Type*) [Field K] [Finite K] : IsCyclic Kˣ :=
  inferInstance
-- @endregion

/-! ### The Galois correspondence -/

-- @region fields_galois.fixed_field_antitone
-- @provenance independent
/-- Bigger subgroups fix smaller fields: if `H₁ ≤ H₂` then `E^{H₂} ⊆ E^{H₁}`, since an element
fixed by every automorphism in `H₂` is fixed by those in `H₁`. -/
theorem fixed_field_antitone {F E : Type*} [Field F] [Field E] [Algebra F E]
    {H₁ H₂ : Subgroup Gal(E/F)} (h : H₁ ≤ H₂) : fixedField H₂ ≤ fixedField H₁ := by
  intro x hx
  rw [mem_fixedField_iff] at hx ⊢
  exact fun σ hσ => hx σ (h hσ)
-- @endregion

-- @region fields_galois.fixing_subgroup_antitone
-- @provenance independent
/-- Bigger fields are fixed by smaller groups: if `K₁ ⊆ K₂` then `Gal(E/K₂) ≤ Gal(E/K₁)`. -/
theorem fixing_subgroup_antitone {F E : Type*} [Field F] [Field E] [Algebra F E]
    {K₁ K₂ : IntermediateField F E} (h : K₁ ≤ K₂) : K₂.fixingSubgroup ≤ K₁.fixingSubgroup := by
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  exact fun x hx => hσ x (h hx)
-- @endregion

-- @region fields_galois.galois_connection
-- @provenance independent
/-- The two maps form a **Galois connection**: `K ⊆ E^H` if and only if `H ≤ Gal(E/K)` — both say
"every element of `H` fixes every element of `K`". -/
theorem galois_connection {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (H : Subgroup Gal(E/F)) :
    K ≤ fixedField H ↔ H ≤ K.fixingSubgroup := by
  constructor
  · intro hK σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => (mem_fixedField_iff H x).mp (hK hx) σ hσ
  · intro hH x hx
    rw [mem_fixedField_iff]
    exact fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff K σ).mp (hH hσ) x hx
-- @endregion

-- @region fields_galois.card_aut_le_finrank
-- @provenance independent
/-- `|Aut(E/F)| ≤ [E : F]` for a finite extension. Each automorphism is in particular an
`F`-algebra map `E → E`, and by Dedekind's independence of characters there are at most
`[E : F]` of those (Mathlib's `card_algHom_le_finrank`). -/
theorem card_aut_le_finrank (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Nat.card Gal(E/F) ≤ finrank F E := by
  have hinj : Function.Injective (fun σ : Gal(E/F) => (σ : E →ₐ[F] E)) :=
    fun σ τ h => AlgEquiv.coe_toAlgHom_injective h
  have : Finite (E →ₐ[F] E) := inferInstance
  exact (Nat.card_le_card_of_injective _ hinj).trans (card_algHom_le_finrank F E E)
-- @endregion

-- @region fields_galois.artin
-- @provenance library
/-- **Artin's theorem**: for a finite group `H` of automorphisms of `E`, `[E : E^H] = |H|`.
Mathlib's `IntermediateField.finrank_fixedField_eq_card`. -/
theorem artin {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (H : Subgroup Gal(E/F)) : finrank (fixedField H) E = Nat.card H :=
  finrank_fixedField_eq_card H
-- @endregion

-- @region fields_galois.card_gal
-- @provenance library
/-- For a finite Galois extension, `|Gal(E/F)| = [E : F]`. Mathlib's `IsGalois.card_aut_eq_finrank`. -/
theorem card_gal (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] : Nat.card Gal(E/F) = finrank F E :=
  IsGalois.card_aut_eq_finrank F E
-- @endregion

-- @region fields_galois.fundamental_theorem
-- @provenance library
/-- **Fundamental theorem of Galois theory**: for a finite Galois extension `E/F`, `K ↦ Gal(E/K)`
is an inclusion-*reversing* bijection from intermediate fields to subgroups of `Gal(E/F)` (an
order isomorphism onto the order dual), with inverse `H ↦ E^H`.
Mathlib's `IsGalois.intermediateFieldEquivSubgroup`. -/
theorem fundamental_theorem (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nonempty (IntermediateField F E ≃o (Subgroup Gal(E/F))ᵒᵈ) :=
  ⟨IsGalois.intermediateFieldEquivSubgroup⟩
-- @endregion

/-! ### Solvability by radicals -/

-- @region fields_galois.solvable_of_radical_root
-- @provenance library
/-- **Abel–Ruffini, the Galois-theoretic direction**: if an irreducible polynomial `q` over `F`
has a root expressible by radicals, then its Galois group is solvable. Mathlib's
`isSolvable_gal_of_irreducible` (in characteristic zero, which the class `solvableByRad`
handles through its definition). -/
theorem solvable_of_radical_root {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E}
    (hx : x ∈ solvableByRad F E) {q : F[X]} (hq : Irreducible q) (hroot : aeval x q = 0) :
    Group.IsSolvable q.Gal :=
  isSolvable_gal_of_irreducible hx hq hroot
-- @endregion

-- @region fields_galois.s5_not_solvable
-- @provenance library
/-- `S₅` is not solvable: its commutator subgroup `A₅` is its own commutator subgroup, so the
derived series never reaches `1`. Mathlib's `Equiv.Perm.not_isSolvable_fin_5`. -/
theorem s5_not_solvable : ¬ Group.IsSolvable (Equiv.Perm (Fin 5)) :=
  Equiv.Perm.not_isSolvable_fin_5
-- @endregion

end Lumenary.FieldsGalois
