/-
The Lumenary — formal mathematics
Homological algebra: chain complexes and homology, the long exact sequence, projective
resolutions and the comparison theorem, Ext and Tor.

What is proved here. Independently: in the cellular chain complex of the real projective plane
`ℤ --d₂--> ℤ² --d₁--> ℤ²` we have `d₁ ∘ d₂ = 0`, the 1-cycle `a + b` is not a boundary but
`2(a + b)` is (so `H₁ ≠ 0` and has an element of order `2`); every homomorphism `ℤ/2 → ℤ` is
zero, hence the extension `0 → ℤ --2·--> ℤ → ℤ/2 → 0` does not split and the quasi-isomorphism
from `[ℤ --2·--> ℤ]` to `ℤ/2` has no inverse chain map; and the Tor and Ext computations
`Tor₁(ℤ/4, ℤ/6) ≅ ℤ/2 ≅ Ext¹(ℤ/4, ℤ/6)` at the level of the kernel and cokernel of
multiplication by `4` on `ℤ/6`.

What Mathlib provides. `HomologicalComplex`, `ChainComplex`, homology, the long exact homology
sequence of a short exact sequence of complexes (`ShortComplex.ShortExact.homology_exact₁/₂/₃`),
chain homotopies and their invariance (`Homotopy.homologyMap_eq`), projective resolutions and the
comparison theorem (`ProjectiveResolution.lift`, `ProjectiveResolution.homotopyEquiv`), and `Ext`
as a derived functor, computable from any projective resolution (`ProjectiveResolution.isoExt`).
Not formalised here: Ext¹ as classifying extensions (Mathlib relates `Ext` in the derived
category to extensions in `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass`), the
universal coefficient theorem, and the general formula `Tor₁(ℤ/m, ℤ/n) ≅ ℤ/gcd(m, n)`.
-/
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic

namespace Lumenary.HomologicalAlgebra

open CategoryTheory Limits

/-! ### A chain complex from topology: the real projective plane -/

-- @region homological_algebra.rp2_d2
-- @provenance definition
/-- The cellular boundary `d₂ : ℤ → ℤ²` of the real projective plane, glued from a square with
boundary word `a b a b`: the 2-cell runs along `a` twice and `b` twice, so `d₂(F) = 2a + 2b`. -/
def rp2_d2 : Matrix (Fin 2) (Fin 1) ℤ := !![2; 2]
-- @endregion

-- @region homological_algebra.rp2_d1
-- @provenance definition
/-- The cellular boundary `d₁ : ℤ² → ℤ²` (edges `a, b` to vertices `v, w`): `a` runs from `v` to
`w` and `b` from `w` back to `v`, so `d₁(a) = w - v` and `d₁(b) = v - w`. Columns are edges. -/
def rp2_d1 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 1, -1]
-- @endregion

-- @region homological_algebra.rp2_dd
-- @provenance independent
/-- **`d ∘ d = 0`**: the boundary of the boundary vanishes, `d₁(2a + 2b) = 2(w - v) + 2(v - w)`.
A direct matrix computation. -/
theorem rp2_dd : rp2_d1 * rp2_d2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rp2_d1, rp2_d2, Matrix.mul_apply, Fin.sum_univ_two]
-- @endregion

-- @region homological_algebra.rp2_torsion_cycle
-- @provenance independent
/-- **`H₁(ℝP²)` has a non-trivial element of order `2`.** The chain `a + b` is a cycle
(`d₁(a + b) = 0`), it is not a boundary (boundaries `d₂(n) = (2n, 2n)` have even coordinates), but
twice it is the boundary `d₂(1)`. So its class in `H₁ = ker d₁ / im d₂` is non-zero with order
`2`; the experiment computes `H₁(ℝP²; ℤ) ≅ ℤ/2` completely. -/
theorem rp2_torsion_cycle :
    rp2_d1.mulVec ![1, 1] = 0 ∧ (∀ n : Fin 1 → ℤ, rp2_d2.mulVec n ≠ ![1, 1]) ∧
      rp2_d2.mulVec ![1] = 2 • ![1, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [rp2_d1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro n h
    have h0 := congrFun h 0
    simp [rp2_d2, Matrix.mulVec, dotProduct] at h0
    omega
  · ext i
    fin_cases i <;> simp [rp2_d2, Matrix.mulVec, dotProduct]
-- @endregion

/-! ### Non-split extensions and quasi-isomorphisms without inverses -/

-- @region homological_algebra.hom_zmod_two_int
-- @provenance independent
/-- **`Hom(ℤ/2, ℤ) = 0`.** If `f : ℤ/2 → ℤ` is additive then `2 f(1) = f(1 + 1) = f(0) = 0`, so
`f(1) = 0`, and `f` vanishes on both elements of `ℤ/2`. -/
theorem hom_zmod_two_int (f : ZMod 2 →+ ℤ) : f = 0 := by
  have h1 : f 1 = 0 := by
    have h : f 1 + f 1 = 0 := by
      rw [← map_add]
      have : (1 : ZMod 2) + 1 = 0 := rfl
      rw [this, map_zero]
    omega
  ext x
  have hx : x = 0 ∨ x = 1 := by
    revert x
    decide
  rcases hx with rfl | rfl
  · simp
  · simp [h1]
-- @endregion

-- @region homological_algebra.not_split
-- @provenance independent
/-- **The extension `0 → ℤ --2·--> ℤ → ℤ/2 → 0` does not split**: reduction mod `2` has no
additive section, because the only homomorphism `ℤ/2 → ℤ` is zero. Equivalently, the chain map
from the complex `[ℤ --2·--> ℤ]` to `ℤ/2` (in degree `0`) is a quasi-isomorphism with no chain map
going back that induces the inverse on homology: in degree `0` such a map would be a section
`ℤ/2 → ℤ`. -/
theorem not_split : ¬ ∃ s : ZMod 2 →+ ℤ, ∀ x : ZMod 2, ((s x : ℤ) : ZMod 2) = x := by
  rintro ⟨s, hs⟩
  have h := hs 1
  rw [hom_zmod_two_int s] at h
  exact absurd h (by decide)
-- @endregion

/-! ### Tor and Ext of cyclic groups, by resolutions -/

-- @region homological_algebra.tor_four_six
-- @provenance independent
/-- **`Tor₁(ℤ/4, ℤ/6)` has `2` elements.** Resolve `ℤ/4` by `0 → ℤ --4·--> ℤ → ℤ/4 → 0`, tensor
with `ℤ/6` to get `ℤ/6 --4·--> ℤ/6`; `Tor₁` is the kernel of this map. A finite computation:
the kernel is `{0, 3}`, with `gcd(4, 6) = 2` elements. -/
theorem tor_four_six : (Finset.univ.filter (fun x : ZMod 6 => 4 * x = 0)).card = 2 := by
  decide
-- @endregion

-- @region homological_algebra.ext_four_six
-- @provenance independent
/-- **`Ext¹(ℤ/4, ℤ/6)` has `2` elements.** Applying `Hom(−, ℤ/6)` to the same resolution gives
`ℤ/6 --4·--> ℤ/6` again, and `Ext¹` is its cokernel: the image `{0, 2, 4}` has index `2`. -/
theorem ext_four_six : (Finset.univ.image (fun x : ZMod 6 => 4 * x)).card * 2 = 6 := by
  decide
-- @endregion

/-! ### Mathlib: long exact sequences, homotopy, resolutions, Ext -/

section Library

variable {C : Type*} [Category C] [Abelian C]

-- @region homological_algebra.long_exact_connecting
-- @provenance library
/-- **The long exact sequence, at the connecting map.** For a short exact sequence of chain
complexes `0 → X₁ → X₂ → X₃ → 0` and indices with `c.Rel i j`, the sequence
`Hᵢ(X₂) → Hᵢ(X₃) --δ--> Hⱼ(X₁)` is exact. Mathlib: `ShortComplex.ShortExact.homology_exact₃`;
`δ` is built from the snake lemma, as in the lesson. -/
theorem long_exact_connecting {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (hS.comp_δ i j hij)).Exact :=
  hS.homology_exact₃ i j hij
-- @endregion

-- @region homological_algebra.long_exact_after_connecting
-- @provenance library
/-- **The long exact sequence, after the connecting map**: `Hᵢ(X₃) --δ--> Hⱼ(X₁) → Hⱼ(X₂)` is
exact. Mathlib: `ShortComplex.ShortExact.homology_exact₁`. -/
theorem long_exact_after_connecting {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (hS.δ_comp i j hij)).Exact :=
  hS.homology_exact₁ i j hij
-- @endregion

-- @region homological_algebra.homotopy_invariance
-- @provenance library
/-- **Chain-homotopic maps induce the same map on homology.** Mathlib: `Homotopy.homologyMap_eq`. -/
theorem homotopy_invariance {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    {f g : K ⟶ L} (h : Homotopy f g) (i : ι) :
    HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i :=
  h.homologyMap_eq i
-- @endregion

-- @region homological_algebra.comparison
-- @provenance library
/-- **The comparison theorem**: any two projective resolutions of the same object are chain
homotopy equivalent (via lifts of the identity, unique up to homotopy). Mathlib:
`ProjectiveResolution.homotopyEquiv`, built from `ProjectiveResolution.lift` and
`ProjectiveResolution.liftHomotopy`. -/
theorem comparison {X : C} (P Q : ProjectiveResolution X) :
    Nonempty (HomotopyEquiv P.complex Q.complex) :=
  ⟨ProjectiveResolution.homotopyEquiv P Q⟩
-- @endregion

-- @region homological_algebra.ext_via_resolution
-- @provenance library
/-- **`Ext` does not depend on the resolution**: `Extⁿ(X, Y)` is the `n`-th cohomology of
`Hom(P•, Y)` for *any* projective resolution `P• → X`. Mathlib defines `Ext R C n` as a derived
functor and proves this as `ProjectiveResolution.isoExt`. -/
theorem ext_via_resolution (R : Type*) [Ring R] [Linear R C] [EnoughProjectives C] {X : C}
    (P : ProjectiveResolution X) (n : ℕ) (Y : C) :
    Nonempty (((Ext R C n).obj (Opposite.op X)).obj Y ≅
      (P.complex.linearYonedaObj R Y).homology n) :=
  ⟨P.isoExt n Y⟩
-- @endregion

-- @region homological_algebra.ext_projective
-- @provenance library
/-- **Projectives have no higher Ext**: `Extⁿ⁺¹(P, Y) = 0` for projective `P` (resolve `P` by
itself). Mathlib: `isZero_Ext_succ_of_projective`. -/
theorem ext_projective (R : Type*) [Ring R] [Linear R C] [EnoughProjectives C] (X Y : C)
    [Projective X] (n : ℕ) : IsZero (((Ext R C (n + 1)).obj (Opposite.op X)).obj Y) :=
  isZero_Ext_succ_of_projective X Y n
-- @endregion

end Library

end Lumenary.HomologicalAlgebra
