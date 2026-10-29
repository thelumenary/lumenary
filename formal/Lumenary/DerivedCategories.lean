/-
The Lumenary — formal mathematics
Derived categories: chain homotopies, quasi-isomorphisms, and the derived category `D(A)`.

Mathlib constructs the homotopy category `K(A)` (`HomotopyCategory`), the derived category
`DerivedCategory A` as the localisation of cochain complexes at quasi-isomorphisms (with its
triangulated structure), the fully faithful embedding `A → D(A)` in each degree, and defines
`Ext` groups as morphisms `X → Y[n]` in `D(A)`. Here we prove by hand the two-term shadow of
"homotopic maps induce the same map on homology", and the facts behind the lesson's running
example: `0 → ℤ --2--> ℤ → ℤ/2 → 0` is exact, so the projective resolution `[ℤ --2--> ℤ]` is
quasi-isomorphic to `ℤ/2`, yet there is no non-zero map `ℤ/2 → ℤ` — so the quasi-isomorphism
has no inverse chain map, and must be inverted formally. Not formalised here: the calculus of
fractions in detail, total derived functors, and the comparison of Mathlib's `Ext` with Ext
computed from a resolution.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.ZMod.Basic

open CategoryTheory

namespace Lumenary.DerivedCategories

section TwoTerm

variable {R : Type*} [Ring R] {A₁ A₀ B₁ B₀ : Type*}
  [AddCommGroup A₁] [AddCommGroup A₀] [AddCommGroup B₁] [AddCommGroup B₀]
  [Module R A₁] [Module R A₀] [Module R B₁] [Module R B₀]

-- @region derived_categories.cycles_map_eq_of_homotopy
-- @provenance independent
/-- Two-term complexes `A₁ --d--> A₀` and `B₁ --d'--> B₀`, chain maps `f = (f₁, f₀)`,
`g = (g₁, g₀)`, and a homotopy `h : A₀ → B₁` with `f₁ - g₁ = h ∘ d` (and `f₀ - g₀ = d' ∘ h`).
Then `f` and `g` agree on the cycles `H₁ = ker d`: if `d x = 0` then
`f₁ x - g₁ x = h (d x) = h 0 = 0`. -/
theorem cycles_map_eq_of_homotopy (d : A₁ →ₗ[R] A₀) (f₁ g₁ : A₁ →ₗ[R] B₁) (h : A₀ →ₗ[R] B₁)
    (hom₁ : f₁ - g₁ = h ∘ₗ d) (x : A₁) (hx : d x = 0) : f₁ x = g₁ x := by
  have key : f₁ x - g₁ x = h (d x) := by
    rw [← LinearMap.sub_apply, hom₁, LinearMap.comp_apply]
  rw [hx, map_zero] at key
  exact sub_eq_zero.mp key
-- @endregion

-- @region derived_categories.boundary_of_homotopy
-- @provenance independent
/-- With the same data, on `H₀ = A₀ / im d` the maps `f₀` and `g₀` differ by a boundary:
`f₀ y - g₀ y = d' (h y)` lies in `im d'`, so `f` and `g` induce the same map
`A₀ / im d → B₀ / im d'`. Together with `cycles_map_eq_of_homotopy` this is the two-term case
of "homotopic chain maps induce equal maps on homology". -/
theorem boundary_of_homotopy (d' : B₁ →ₗ[R] B₀) (f₀ g₀ : A₀ →ₗ[R] B₀) (h : A₀ →ₗ[R] B₁)
    (hom₀ : f₀ - g₀ = d' ∘ₗ h) (y : A₀) : f₀ y - g₀ y ∈ LinearMap.range d' := by
  refine ⟨h y, ?_⟩
  rw [← LinearMap.comp_apply, ← hom₀, LinearMap.sub_apply]
-- @endregion

-- @region derived_categories.homology_class_eq_of_homotopy
-- @provenance independent
/-- The same statement phrased with quotient classes: `f₀` and `g₀` send every `y` to the same
class in `H₀(B) = B₀ / im d'`. -/
theorem homology_class_eq_of_homotopy (d' : B₁ →ₗ[R] B₀) (f₀ g₀ : A₀ →ₗ[R] B₀)
    (h : A₀ →ₗ[R] B₁) (hom₀ : f₀ - g₀ = d' ∘ₗ h) (y : A₀) :
    Submodule.Quotient.mk (p := LinearMap.range d') (f₀ y) =
      Submodule.Quotient.mk (p := LinearMap.range d') (g₀ y) :=
  (Submodule.Quotient.eq _).mpr (boundary_of_homotopy d' f₀ g₀ h hom₀ y)
-- @endregion

end TwoTerm

section General

variable {C : Type*} [Category C] [Abelian C]

-- @region derived_categories.homology_map_eq_of_homotopy
-- @provenance library
/-- Homotopic chain maps induce the same map on homology in every degree, for complexes in any
abelian category. This applies Mathlib's `Homotopy.homologyMap_eq`. It is why homology is
well defined on the homotopy category `K(A)`. -/
theorem homologyMap_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L}
    (ho : Homotopy f g) (i : ℤ) : HomologicalComplex.homologyMap f i =
      HomologicalComplex.homologyMap g i :=
  ho.homologyMap_eq i
-- @endregion

variable [HasDerivedCategory C]

-- @region derived_categories.q_map_eq_of_homotopy
-- @provenance library
/-- Homotopic chain maps become equal in the derived category: the localisation functor
`Q : C(A) → D(A)` factors through `K(A)`. This applies Mathlib's
`DerivedCategory.Q_map_eq_of_homotopy`. -/
theorem Q_map_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (ho : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  DerivedCategory.Q_map_eq_of_homotopy (h := ho)
-- @endregion

-- @region derived_categories.is_iso_q_map_iff_quasi_iso
-- @provenance library
/-- A chain map becomes an isomorphism in `D(A)` exactly when it is a quasi-isomorphism: the
derived category inverts the quasi-isomorphisms and nothing else. This applies Mathlib's
`DerivedCategory.isIso_Q_map_iff_quasiIso`. -/
theorem isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (DerivedCategory.Q.map φ) ↔ QuasiIso φ :=
  DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ)
-- @endregion

-- @region derived_categories.single_map_bijective
-- @provenance library
/-- The embedding `A → D(A)` (an object placed in degree `0`) is fully faithful:
`Hom_A(X, Y) → Hom_{D(A)}(X, Y)` is a bijection. This applies Mathlib's instances
`(DerivedCategory.singleFunctor C 0).Full` and `.Faithful`, via
`Functor.FullyFaithful.map_bijective`. -/
theorem single_map_bijective (X Y : C) :
    Function.Bijective (fun f : X ⟶ Y => (DerivedCategory.singleFunctor C 0).map f) :=
  (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor C 0)).map_bijective X Y
-- @endregion

end General

-- @region derived_categories.ext_zero_bijective
-- @provenance library
/-- Mathlib *defines* `Ext X Y n` as morphisms `X → Y[n]` in the derived category (the lesson's
key formula `Extⁿ(X, Y) ≅ Hom_{D(A)}(X, Y[n])` is built into the definition). In degree `0`
these are just the morphisms of `A`: `Ext.mk₀ : (X ⟶ Y) → Ext X Y 0` is bijective. This applies
Mathlib's `Abelian.Ext.mk₀_bijective`. -/
theorem ext_zero_bijective {C : Type*} [Category C] [Abelian C] [HasExt C] (X Y : C) :
    Function.Bijective (Abelian.Ext.mk₀ (X := X) (Y := Y)) :=
  Abelian.Ext.mk₀_bijective X Y
-- @endregion

/-! ### The running example: `ℤ --2--> ℤ` resolves `ℤ/2` -/

-- @region derived_categories.two_mul_injective
-- @provenance independent
/-- Multiplication by `2` on `ℤ` is injective, so `0 → ℤ --2--> ℤ` is exact at the left. -/
theorem two_mul_injective : Function.Injective (fun n : ℤ => 2 * n) := by
  intro a b h
  simp only at h
  omega
-- @endregion

-- @region derived_categories.exact_at_middle
-- @provenance independent
/-- The kernel of reduction `ℤ → ℤ/2` is exactly the image of multiplication by `2`, so
`ℤ --2--> ℤ → ℤ/2` is exact in the middle. Together with `two_mul_injective` and surjectivity of
reduction, the complex `[ℤ --2--> ℤ]` (in degrees `-1, 0`) is quasi-isomorphic to `ℤ/2`. -/
theorem exact_at_middle (n : ℤ) : (n : ZMod 2) = 0 ↔ ∃ m : ℤ, 2 * m = n := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by simpa using hm.symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by norm_num⟩
-- @endregion

-- @region derived_categories.hom_zmod_two_int_eq_zero
-- @provenance independent
/-- There is no non-zero group homomorphism `ℤ/2 → ℤ`: `2 · φ(x) = φ(2x) = φ(0) = 0`, and `ℤ`
has no elements of order `2`. Consequently the quasi-isomorphism `[ℤ --2--> ℤ] → ℤ/2` has no
inverse chain map `ℤ/2 → [ℤ --2--> ℤ]` (its degree-0 part would be a map `ℤ/2 → ℤ`, hence zero,
and could not induce the identity on `H⁰ = ℤ/2`). In `D(Ab)` it is nevertheless an isomorphism:
inverting it is exactly what localisation does. -/
theorem hom_zmod_two_int_eq_zero (φ : ZMod 2 →+ ℤ) : φ = 0 := by
  ext x
  have h2 : (2 : ℤ) * φ x = 0 := by
    calc (2 : ℤ) * φ x = φ (x + x) := by rw [map_add]; ring
      _ = φ 0 := by
        congr 1
        fin_cases x <;> rfl
      _ = 0 := map_zero φ
  have : φ x = 0 := by omega
  simpa using this
-- @endregion

end Lumenary.DerivedCategories
