/-
The Lumenary — formal mathematics
Non-Euclidean geometry: the sphere and the hyperbolic plane.

Spherical geometry is done with vectors in `ℝ³` (Mathlib's `Fin 3 → ℝ`, with the dot product
`⬝ᵥ` and the cross product `⨯₃`). Proved here (`@provenance independent`): the vector identity
behind the spherical law of cosines, the law itself, the fact that any two great circles meet
(there are no parallels on the sphere), and the bookkeeping step of Girard's theorem. For the
hyperbolic plane we use the upper half-plane model: proved here are the formula for the
imaginary part of `(a z + b) / (c z + d)`, the invariance of `|z - w|² / (Im z · Im w)` under
these Möbius maps (which is why they are hyperbolic isometries), and the existence of
infinitely many lines through a point that miss a given line. Mathlib's `UpperHalfPlane` has
the hyperbolic metric itself; its distance formula and the isometric action of `SL(2, ℝ)` are
cited as `@provenance library`.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Lumenary.NonEuclideanGeometry

open Matrix

/-! ### The sphere -/

-- @region non_euclidean_geometry.lagrange_identity
-- @provenance independent
/-- **Lagrange's identity** for the cross product in `ℝ³`:
`(u × v) · (w × x) = (u · w)(v · x) - (u · x)(v · w)`, checked coordinate by coordinate.
(Mathlib has it, for any commutative ring, as `cross_dot_cross`.) -/
theorem lagrange_identity (u v w x : Fin 3 → ℝ) :
    (u ⨯₃ v) ⬝ᵥ (w ⨯₃ x) = (u ⬝ᵥ w) * (v ⬝ᵥ x) - (u ⬝ᵥ x) * (v ⬝ᵥ w) := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring
-- @endregion

-- @region non_euclidean_geometry.normals_dot
-- @provenance independent
/-- For points `A, B, C` on the unit sphere, the normals `C × A` and `C × B` to the great
circles `CA` and `CB` satisfy `(C × A) · (C × B) = A · B - (A · C)(B · C)`, i.e.
`cos c - cos a cos b` in terms of the sides of the spherical triangle. -/
theorem normals_dot (A B C : Fin 3 → ℝ) (hC : C ⬝ᵥ C = 1) :
    (C ⨯₃ A) ⬝ᵥ (C ⨯₃ B) = A ⬝ᵥ B - (A ⬝ᵥ C) * (B ⬝ᵥ C) := by
  rw [lagrange_identity, hC, one_mul, dotProduct_comm C B]
  ring
-- @endregion

-- @region non_euclidean_geometry.normal_sq
-- @provenance independent
/-- The normal `C × A` has squared length `1 - (A · C)²`, which is `sin² b` when the side `CA`
has length `b` (so `A · C = cos b`). -/
theorem normal_sq (A C : Fin 3 → ℝ) (hA : A ⬝ᵥ A = 1) (hC : C ⬝ᵥ C = 1) :
    (C ⨯₃ A) ⬝ᵥ (C ⨯₃ A) = 1 - (A ⬝ᵥ C) ^ 2 := by
  rw [normals_dot A A C hC, hA]
  ring
-- @endregion

-- @region non_euclidean_geometry.spherical_law_of_cosines
-- @provenance independent
/-- **The spherical law of cosines.** Let `A, B, C` be on the unit sphere, with sides
`a = ∠BOC`, `b = ∠COA`, `c = ∠AOB` (so `cos a = B · C`, …), and let `γ` be the angle at `C`,
i.e. the angle between the normals `C × A` and `C × B`, whose lengths are `sin b` and `sin a`:
`(C × A) · (C × B) = sin b · sin a · cos γ`. Then `cos c = cos a cos b + sin a sin b cos γ`. -/
theorem spherical_law_of_cosines (A B C : Fin 3 → ℝ) (hC : C ⬝ᵥ C = 1) {a b c γ : ℝ}
    (ha : Real.cos a = B ⬝ᵥ C) (hb : Real.cos b = A ⬝ᵥ C) (hc : Real.cos c = A ⬝ᵥ B)
    (hγ : (C ⨯₃ A) ⬝ᵥ (C ⨯₃ B) = Real.sin b * Real.sin a * Real.cos γ) :
    Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ := by
  have h := normals_dot A B C hC
  rw [hγ, ← ha, ← hb, ← hc] at h
  linarith
-- @endregion

-- @region non_euclidean_geometry.great_circles_meet
-- @provenance independent
/-- **There are no parallels on the sphere.** The great circle with normal `n` is the set of
unit vectors `v` with `v · n = 0`. Any two great circles meet: the linear map
`v ↦ (v · n, v · m)` from `ℝ³` to `ℝ²` has a non-zero kernel by rank–nullity, and a non-zero
kernel vector, rescaled to length `1`, lies on both circles (and so does its antipode). -/
theorem great_circles_meet (n m : Fin 3 → ℝ) :
    ∃ v : Fin 3 → ℝ, v ⬝ᵥ v = 1 ∧ v ⬝ᵥ n = 0 ∧ v ⬝ᵥ m = 0 := by
  -- The 2 × 3 matrix with rows `n` and `m`.
  set M : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of ![n, m] with hM
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hMw : M *ᵥ w = 0 := by simpa using hw
  have hn : w ⬝ᵥ n = 0 := by
    have := congrFun hMw 0
    simpa [hM, Matrix.mulVec, dotProduct_comm] using this
  have hm : w ⬝ᵥ m = 0 := by
    have := congrFun hMw 1
    simpa [hM, Matrix.mulVec, dotProduct_comm] using this
  -- Rescale `w` to unit length.
  have hpos : 0 < w ⬝ᵥ w := by
    have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hw0
  set s := (Real.sqrt (w ⬝ᵥ w))⁻¹ with hs
  refine ⟨s • w, ?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hs,
      ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · rw [smul_dotProduct, hn, smul_zero]
  · rw [smul_dotProduct, hm, smul_zero]
-- @endregion

-- @region non_euclidean_geometry.girard_bookkeeping
-- @provenance independent
/-- **The bookkeeping step of Girard's theorem.** The three great circles through the sides
of a spherical triangle of area `Δ` (radius `R`) cut out three pairs of antipodal lunes, of
areas `2αR²`, `2βR²`, `2γR²` each. Together the six lunes cover the sphere once, except that
the triangle and its antipodal copy are covered three times each:
`2(2αR² + 2βR² + 2γR²) = 4πR² + 4Δ`. Hence `Δ = R²(α + β + γ - π)`. (The lune areas and the
covering argument are proved in the lesson; this lemma checks the arithmetic.) -/
theorem girard_bookkeeping {R α β γ Δ : ℝ}
    (hcover : 2 * (2 * α * R ^ 2 + 2 * β * R ^ 2 + 2 * γ * R ^ 2) =
      4 * Real.pi * R ^ 2 + 4 * Δ) :
    Δ = R ^ 2 * (α + β + γ - Real.pi) := by
  linarith
-- @endregion

/-! ### The hyperbolic plane: the upper half-plane model -/

open Complex

-- @region non_euclidean_geometry.im_mobius
-- @provenance independent
/-- **Möbius maps preserve the upper half-plane.** For real `a, b, c, d` with `a d - b c = 1`,
`Im ((a z + b) / (c z + d)) = Im z / |c z + d|²`. In particular `Im z > 0` implies that the
image has positive imaginary part. (Mathlib: `UpperHalfPlane.im_smul_eq_div_normSq`.) -/
theorem im_mobius {a b c d : ℝ} (hdet : a * d - b * c = 1) (z : ℂ) :
    ((a * z + b) / (c * z + d)).im = z.im / normSq (c * z + d) := by
  rw [Complex.div_im]
  simp only [add_im, add_re, mul_im, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    add_zero]
  rw [div_sub_div_same]
  congr 1
  linear_combination z.im * hdet
-- @endregion

-- @region non_euclidean_geometry.mobius_sub
-- @provenance independent
/-- The difference of two image points: if `a d - b c = 1`, then
`g z - g w = (z - w) / ((c z + d)(c w + d))` for `g z = (a z + b) / (c z + d)`. -/
theorem mobius_sub {a b c d : ℝ} (hdet : a * d - b * c = 1) {z w : ℂ}
    (hz : (c : ℂ) * z + d ≠ 0) (hw : (c : ℂ) * w + d ≠ 0) :
    (a * z + b) / (c * z + d) - (a * w + b) / (c * w + d) =
      (z - w) / ((c * z + d) * (c * w + d)) := by
  rw [div_sub_div _ _ hz hw]
  congr 1
  have h : ((a : ℂ) * d - b * c) = 1 := by exact_mod_cast hdet
  linear_combination (z - w) * h
-- @endregion

-- @region non_euclidean_geometry.cross_term_invariant
-- @provenance independent
/-- **Möbius maps are hyperbolic isometries.** The hyperbolic distance in the upper half-plane
satisfies `cosh d(z, w) = 1 + |z - w|² / (2 Im z Im w)`. The quantity
`|z - w|² / (Im z · Im w)` is unchanged by `z ↦ (a z + b) / (c z + d)` (`a d - b c = 1`):
by `mobius_sub` and `im_mobius`, numerator and denominator are both divided by
`|c z + d|² |c w + d|²`. -/
theorem cross_term_invariant {a b c d : ℝ} (hdet : a * d - b * c = 1) {z w : ℂ}
    (hz : (c : ℂ) * z + d ≠ 0) (hw : (c : ℂ) * w + d ≠ 0) :
    normSq ((a * z + b) / (c * z + d) - (a * w + b) / (c * w + d)) /
        (((a * z + b) / (c * z + d)).im * ((a * w + b) / (c * w + d)).im) =
      normSq (z - w) / (z.im * w.im) := by
  rw [mobius_sub hdet hz hw, im_mobius hdet, im_mobius hdet, normSq_div, normSq_mul]
  have hz' : normSq ((c : ℂ) * z + d) ≠ 0 := (normSq_pos.mpr hz).ne'
  have hw' : normSq ((c : ℂ) * w + d) ≠ 0 := (normSq_pos.mpr hw).ne'
  rw [div_mul_div_comm, div_div_div_eq, mul_comm (normSq _ * normSq _) (z.im * w.im)]
  rw [mul_div_mul_right _ _ (mul_ne_zero hz' hw')]
-- @endregion

-- @region non_euclidean_geometry.cosh_dist
-- @provenance library
/-- **The hyperbolic distance formula** in Mathlib's upper half-plane `ℍ`:
`cosh (d z w) = 1 + |z - w|² / (2 Im z Im w)`. This is `UpperHalfPlane.cosh_dist`. -/
theorem cosh_dist (z w : UpperHalfPlane) :
    Real.cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) :=
  UpperHalfPlane.cosh_dist z w
-- @endregion

-- @region non_euclidean_geometry.sl2_isometry
-- @provenance library
/-- **`SL(2, ℝ)` acts on `ℍ` by isometries.** Mathlib proves the instance
`IsIsometricSMul SL(2, ℝ) ℍ` by writing each element as a composite of translations, dilations
and `z ↦ -1/z`; we use it through `isometry_smul`. -/
theorem sl2_isometry (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Isometry (fun z : UpperHalfPlane => g • z) :=
  isometry_smul UpperHalfPlane g
-- @endregion

-- @region non_euclidean_geometry.dist_vertical
-- @provenance library
/-- **The hyperbolic plane is infinitely large.** On a vertical line the distance is
`|log (Im z) - log (Im w)|`: from `i` to `i y` it is `|log y|`, which grows without bound as `y`
tends to `0` or `∞`. This is Mathlib's `UpperHalfPlane.dist_of_re_eq`. -/
theorem dist_vertical {z w : UpperHalfPlane} (h : z.re = w.re) :
    dist z w = dist (Real.log z.im) (Real.log w.im) :=
  UpperHalfPlane.dist_of_re_eq h
-- @endregion

-- @region non_euclidean_geometry.many_parallels
-- @provenance independent
/-- **Infinitely many parallels.** Let `L` be the hyperbolic line `Re z = 0` (the positive
imaginary axis) and `p = 1 + i`. For every real `c ≥ 1`, the semicircle centred at the real
point `c` through `p` is a hyperbolic line through `p`, and it does not meet `L`: a point `i y`
(`y > 0`) on it would satisfy `c² + y² = (1 - c)² + 1`, i.e. `y² = 2 - 2c ≤ 0`. Different `c`
give different lines, so there are infinitely many lines through `p` missing `L`. -/
theorem many_parallels {c : ℝ} (hc : 1 ≤ c) {y : ℝ} (hy : 0 < y) :
    normSq (I * y - c) ≠ normSq (1 + I - c) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, add_re, add_im, I_re, I_im,
    ofReal_re, ofReal_im, one_re, one_im]
  intro h
  nlinarith
-- @endregion

end Lumenary.NonEuclideanGeometry
