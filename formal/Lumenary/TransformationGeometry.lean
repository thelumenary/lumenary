/-
The Lumenary — formal mathematics
Transformation geometry: the classification of plane isometries, affine maps and the
cross-ratio.

We model the Euclidean plane as the complex numbers `ℂ`, with distance `‖z - w‖`. The main
theorem, proved here from scratch (`@provenance independent`), is the normal form: every
isometry of the plane is `z ↦ a z + b` or `z ↦ a z̄ + b` with `|a| = 1`. Further independent
results sort the normal forms into translations, rotations, reflections and glide reflections,
show that affine maps preserve ratios along lines but not angles, and prove that Möbius
(projective) transformations of a line preserve the cross-ratio. Mathlib proves the normal
form in a different way, from the Mazur–Ulam theorem (`IsometryEquiv.toRealLinearIsometryEquiv`)
and its description of the linear isometries of `ℂ` (`linear_isometry_complex`); that version
is included as `isometry_normal_form_mathlib` (`@provenance library`).
-/
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Lumenary.TransformationGeometry

open Complex ComplexConjugate Matrix

/-! ### Points are determined by distances -/

-- @region transformation_geometry.eq_of_three_dists
-- @provenance independent
/-- **Three distances determine a point.** If `w` has the same distances as `z` from the three
non-collinear points `0`, `1` and `i`, then `w = z`. Squaring the distances, the differences of
the three equations are linear: they give `Re w = Re z` and `Im w = Im z`. -/
theorem eq_of_three_dists {z w : ℂ} (h0 : ‖w‖ = ‖z‖) (h1 : ‖w - 1‖ = ‖z - 1‖)
    (hI : ‖w - I‖ = ‖z - I‖) : w = z := by
  have e0 : normSq w = normSq z := by rw [← Complex.sq_norm, ← Complex.sq_norm, h0]
  have e1 : normSq (w - 1) = normSq (z - 1) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, h1]
  have eI : normSq (w - I) = normSq (z - I) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, hI]
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, I_re, I_im] at e0 e1 eI
  apply Complex.ext <;> nlinarith
-- @endregion

-- @region transformation_geometry.fix_three_eq_id
-- @provenance independent
/-- **An isometry fixing `0`, `1` and `i` is the identity.** Apply `eq_of_three_dists` to
`w = g z`: its distances from `0 = g 0`, `1 = g 1`, `i = g i` equal those of `z`. -/
theorem fix_three_eq_id (g : ℂ → ℂ) (hg : ∀ z w, ‖g z - g w‖ = ‖z - w‖) (h0 : g 0 = 0)
    (h1 : g 1 = 1) (hI : g I = I) (z : ℂ) : g z = z := by
  apply eq_of_three_dists
  · simpa [h0] using hg z 0
  · simpa [h1] using hg z 1
  · simpa [hI] using hg z I
-- @endregion

-- @region transformation_geometry.isometry_normal_form
-- @provenance independent
/-- **The normal form of a plane isometry.** Every distance-preserving map `f : ℂ → ℂ` is
`z ↦ a z + b` or `z ↦ a z̄ + b` with `|a| = 1`. Proof as in the lesson: put `b = f 0` and
`a = f 1 - f 0`; then `g z = (f z - b) / a` preserves distances and fixes `0` and `1`, so `g i`
is at distance `1` from `0` and `√2` from `1`, i.e. `g i = ± i`. If `g i = i` then `g` is the
identity; if `g i = -i` then `z ↦ conj (g z)` fixes `0`, `1`, `i` and is the identity. -/
theorem isometry_normal_form (f : ℂ → ℂ) (hf : Isometry f) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ((∀ z, f z = a * z + b) ∨ (∀ z, f z = a * conj z + b)) := by
  have hd : ∀ z w, ‖f z - f w‖ = ‖z - w‖ := fun z w => by
    rw [← Complex.dist_eq, ← Complex.dist_eq, hf.dist_eq]
  set a := f 1 - f 0 with ha_def
  set b := f 0 with hb_def
  have ha : ‖a‖ = 1 := by simpa using hd 1 0
  have ha0 : a ≠ 0 := by
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  set g : ℂ → ℂ := fun z => (f z - b) / a with hg_def
  have hfg : ∀ z, f z = a * g z + b := fun z => by
    simp only [hg_def]; field_simp; ring
  have hgd : ∀ z w, ‖g z - g w‖ = ‖z - w‖ := fun z w => by
    have : g z - g w = (f z - f w) / a := by simp only [hg_def]; field_simp; ring
    rw [this, norm_div, ha, div_one, hd]
  have hg0 : g 0 = 0 := by simp [hg_def, hb_def]
  have hg1 : g 1 = 1 := by simp only [hg_def]; rw [← ha_def]; exact div_self ha0
  -- `g i` is `i` or `-i`.
  have hgI : g I = I ∨ g I = -I := by
    have e0 : normSq (g I) = 1 := by
      have := hgd I 0; rw [hg0, sub_zero, sub_zero, norm_I] at this
      rw [← Complex.sq_norm, this, one_pow]
    have e1 : normSq (g I - 1) = 2 := by
      have := hgd I 1; rw [hg1] at this
      rw [← Complex.sq_norm, this, Complex.sq_norm]; simp [normSq_apply]; norm_num
    simp only [normSq_apply, sub_re, sub_im, one_re, one_im] at e0 e1
    have hre : (g I).re = 0 := by nlinarith
    have him : (g I).im = 1 ∨ (g I).im = -1 := by
      have : (g I).im * (g I).im = 1 := by rw [hre] at e0; linarith
      rcases mul_self_eq_one_iff.mp this with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases him with h | h
    · left; apply Complex.ext <;> simp [hre, h]
    · right; apply Complex.ext <;> simp [hre, h]
  refine ⟨a, b, ha, ?_⟩
  rcases hgI with hI | hI
  · -- `g` is the identity: a direct isometry.
    left; intro z
    rw [hfg z, fix_three_eq_id g hgd hg0 hg1 hI z]
  · -- `conj ∘ g` is the identity: an opposite isometry.
    right; intro z
    have hc := fix_three_eq_id (fun z => conj (g z))
      (fun z w => by rw [← map_sub, Complex.norm_conj, hgd]) (by simp [hg0])
      (by simp [hg1]) (by simp [hI]) z
    have : g z = conj z := by rw [← Complex.conj_conj (g z), hc]
    rw [hfg z, this]
-- @endregion

-- @region transformation_geometry.isometry_normal_form_mathlib
-- @provenance library
/-- **The normal form, Mathlib's way.** For a surjective isometry (`ℂ ≃ᵢ ℂ`), Mathlib's
Mazur–Ulam theorem (`IsometryEquiv.toRealLinearIsometryEquiv`) makes `z ↦ f z - f 0` a real
linear isometry, and `linear_isometry_complex` says such a map is a rotation, possibly
preceded by conjugation. -/
theorem isometry_normal_form_mathlib (f : ℂ ≃ᵢ ℂ) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ((∀ z, f z = a * z + b) ∨ (∀ z, f z = a * conj z + b)) := by
  obtain ⟨u, hu⟩ := linear_isometry_complex f.toRealLinearIsometryEquiv
  refine ⟨u, f 0, by simp, ?_⟩
  rcases hu with h | h
  · left; intro z
    have := congrArg (fun e : ℂ ≃ₗᵢ[ℝ] ℂ => e z) h
    simp only [IsometryEquiv.toRealLinearIsometryEquiv_apply, rotation_apply] at this
    rw [← this]; ring
  · right; intro z
    have := congrArg (fun e : ℂ ≃ₗᵢ[ℝ] ℂ => e z) h
    simp only [IsometryEquiv.toRealLinearIsometryEquiv_apply, LinearIsometryEquiv.trans_apply,
      rotation_apply, conjLIE_apply] at this
    rw [← this]; ring
-- @endregion

/-! ### Sorting the normal forms into four types -/

-- @region transformation_geometry.direct_is_rotation
-- @provenance independent
/-- **A direct isometry with `a ≠ 1` is a rotation.** The point `c = b / (1 - a)` is fixed,
and `a z + b = a (z - c) + c`: turn about `c` through the angle `arg a`. (If `a = 1` the map
is the translation `z ↦ z + b`.) -/
theorem direct_is_rotation {a b : ℂ} (ha : a ≠ 1) :
    ∃ c : ℂ, ∀ z, a * z + b = a * (z - c) + c := by
  have h : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  refine ⟨b / (1 - a), fun z => ?_⟩
  field_simp
  ring
-- @endregion

-- @region transformation_geometry.opposite_square
-- @provenance independent
/-- **The square of an opposite isometry is a translation.** If `g z = a z̄ + b` with
`|a| = 1`, then `g (g z) = z + (a b̄ + b)`, because `a ā = |a|² = 1`. -/
theorem opposite_square {a b : ℂ} (ha : ‖a‖ = 1) (z : ℂ) :
    a * conj (a * conj z + b) + b = z + (a * conj b + b) := by
  have h : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; norm_num
  simp only [map_add, map_mul, Complex.conj_conj]
  linear_combination z * h
-- @endregion

-- @region transformation_geometry.opposite_fixed_iff
-- @provenance independent
/-- **When does an opposite isometry fix a point?** `g z = a z̄ + b` (with `|a| = 1`) has a
fixed point exactly when its square is the identity, i.e. `a b̄ + b = 0`. If `g c = c` then
`c = g (g c) = c + (a b̄ + b)`; conversely, if `a b̄ + b = 0` then `b / 2` is fixed. -/
theorem opposite_fixed_iff {a b : ℂ} (ha : ‖a‖ = 1) :
    (∃ c, a * conj c + b = c) ↔ a * conj b + b = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have h2 := opposite_square (b := b) ha c
    rw [hc, hc] at h2
    linear_combination -h2
  · intro h
    refine ⟨b / 2, ?_⟩
    rw [map_div₀, map_ofNat]
    linear_combination h / 2
-- @endregion

-- @region transformation_geometry.opposite_with_fixed_point
-- @provenance independent
/-- **An opposite isometry with a fixed point `c` is a reflection** in a line through `c`:
`g z = a · conj (z - c) + c`, which is the reflection `w ↦ a w̄` in a line through `0`,
conjugated by the translation taking `0` to `c`. -/
theorem opposite_with_fixed_point {a b c : ℂ} (hc : a * conj c + b = c) (z : ℂ) :
    a * conj z + b = a * conj (z - c) + c := by
  rw [map_sub]
  linear_combination hc
-- @endregion

-- @region transformation_geometry.glide_decomposition
-- @provenance independent
/-- **Every opposite isometry is a glide reflection** (possibly with zero glide). Let
`w = (a b̄ + b) / 2`, half the translation `g ∘ g`. Then `a w̄ = w`, so `w` points along the
mirror direction, and `z ↦ a z̄ + (b - w)` has a fixed point (by `opposite_fixed_iff`), so it
is a reflection. Hence `g` = (reflection) followed by (translation by `w` parallel to the
mirror). -/
theorem glide_decomposition {a b : ℂ} (ha : ‖a‖ = 1) :
    let w := (a * conj b + b) / 2
    a * conj w = w ∧ a * conj (b - w) + (b - w) = 0 := by
  intro w
  have h : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; norm_num
  have hw : a * conj w = w := by
    simp only [w, map_div₀, map_add, map_mul, Complex.conj_conj, map_ofNat]
    linear_combination b * h / 2
  refine ⟨hw, ?_⟩
  rw [map_sub, mul_sub, hw]
  simp only [w]
  ring
-- @endregion

-- @region transformation_geometry.glide_no_fixed_point
-- @provenance independent
/-- **A glide reflection moves every point.** For real `t ≠ 0`, the glide reflection
`z ↦ z̄ + t` (reflect in the real axis, then slide along it) has no fixed point: comparing
real parts would give `t = 0`. -/
theorem glide_no_fixed_point {t : ℝ} (ht : t ≠ 0) (z : ℂ) : conj z + t ≠ z := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact ht this
-- @endregion

-- @region transformation_geometry.reflect_reflect
-- @provenance independent
/-- **Two reflections make a rotation.** The reflection in the line through `0` in direction
`e^{iα}` is `z ↦ e^{2iα} z̄`. Composing the reflections for `β` and then `α` gives multiplication
by `e^{2iα} · conj(e^{2iβ}) = e^{2i(α - β)}`: a rotation by twice the angle between the
mirrors. -/
theorem reflect_reflect (α β : ℝ) (z : ℂ) :
    exp (2 * α * I) * conj (exp (2 * β * I) * conj z) = exp (2 * (α - β) * I) * z := by
  have hconj : conj (exp (2 * β * I)) = exp (-(2 * β * I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]
  rw [map_mul, Complex.conj_conj, hconj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring
-- @endregion

-- @region transformation_geometry.parallel_reflections
-- @provenance independent
/-- **Two reflections in parallel mirrors make a translation.** The reflection in the vertical
line `Re z = a` is `z ↦ 2a - z̄`. Reflecting in `Re z = b` and then in `Re z = a` translates by
`2(a - b)`, twice the distance between the mirrors. -/
theorem parallel_reflections (a b : ℝ) (z : ℂ) :
    2 * (a : ℂ) - conj (2 * (b : ℂ) - conj z) = z + 2 * ((a : ℂ) - b) := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]
  ring
-- @endregion

-- @region transformation_geometry.conj_translation
-- @provenance independent
/-- **Translations form a normal subgroup.** Conjugating the translation by `t` by a direct
similarity `f z = a z + b` (`a ≠ 0`) gives the translation by `a t`:
`f (f⁻¹ z + t) = z + a t`. So "being a translation" is a notion every observer agrees on —
in Klein's language, it is invariant. -/
theorem conj_translation {a b : ℂ} (ha : a ≠ 0) (t z : ℂ) :
    a * ((z - b) / a + t) + b = z + a * t := by
  field_simp
  ring
-- @endregion

/-! ### Affine maps -/

-- @region transformation_geometry.affine_preserves_ratio
-- @provenance independent
/-- **Affine maps preserve ratios along lines.** If `f x = A x + c` with `A` linear, then
`f` sends the point dividing the segment from `x` to `y` in the ratio `t : (1 - t)` to the point
dividing the image segment in the same ratio. (Midpoints go to midpoints; parallel lines go to
parallel lines.) -/
theorem affine_preserves_ratio {V : Type*} [AddCommGroup V] [Module ℝ V] (A : V →ₗ[ℝ] V)
    (c x y : V) (t : ℝ) :
    A ((1 - t) • x + t • y) + c = (1 - t) • (A x + c) + t • (A y + c) := by
  rw [map_add, map_smul, map_smul, smul_add, smul_add]
  module
-- @endregion

-- @region transformation_geometry.shear_breaks_right_angle
-- @provenance independent
/-- **Affine maps need not preserve angles.** The shear `(x, y) ↦ (x + y, y)` sends the
perpendicular vectors `e₁ = (1, 0)` and `e₂ = (0, 1)` to `(1, 0)` and `(1, 1)`, whose dot product
is `1 ≠ 0`. -/
theorem shear_breaks_right_angle :
    (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 0 ∧
      (!![1, 1; 0, 1] *ᵥ ![1, 0] : Fin 2 → ℝ) ⬝ᵥ (!![1, 1; 0, 1] *ᵥ ![0, 1]) = 1 := by
  constructor <;> simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
-- @endregion

/-! ### Projective maps of a line and the cross-ratio -/

-- @region transformation_geometry.cross_ratio
-- @provenance definition
/-- The **cross-ratio** of four points `a, b, c, d` of a line (coordinates in a field `K`):
`(a, b; c, d) = ((c - a)(d - b)) / ((c - b)(d - a))`. -/
def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=
  ((c - a) * (d - b)) / ((c - b) * (d - a))
-- @endregion

-- @region transformation_geometry.mobius
-- @provenance definition
/-- A **projective (Möbius) transformation of the line**, `x ↦ (p x + q) / (r x + s)`, given by
the matrix `!![p, q; r, s]` (invertible when `p s - q r ≠ 0`). -/
def mobius {K : Type*} [Field K] (p q r s x : K) : K := (p * x + q) / (r * x + s)
-- @endregion

-- @region transformation_geometry.mobius_sub
-- @provenance independent
/-- The key identity: `m(x) - m(y) = (p s - q r)(x - y) / ((r x + s)(r y + s))`. Differences
are multiplied by a factor that depends on each point separately, so in the cross-ratio all
the factors cancel. -/
theorem mobius_sub {K : Type*} [Field K] {p q r s x y : K} (hx : r * x + s ≠ 0)
    (hy : r * y + s ≠ 0) :
    mobius p q r s x - mobius p q r s y =
      (p * s - q * r) * (x - y) / ((r * x + s) * (r * y + s)) := by
  unfold mobius
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring
-- @endregion

-- @region transformation_geometry.cross_ratio_mobius
-- @provenance independent
/-- **Projective transformations preserve the cross-ratio.** Substitute `mobius_sub` into each
of the four differences: the factor `(p s - q r)²` and the four factors `(r x + s)` appear in
numerator and denominator alike, and cancel. -/
theorem crossRatio_mobius {K : Type*} [Field K] {p q r s a b c d : K} (hdet : p * s - q * r ≠ 0)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0) :
    crossRatio (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d) =
      crossRatio a b c d := by
  unfold crossRatio
  rw [mobius_sub hc ha, mobius_sub hd hb, mobius_sub hc hb, mobius_sub hd ha]
  rw [div_mul_div_comm, div_mul_div_comm, div_div_div_eq]
  by_cases h : (c - b) * (d - a) = 0
  · have h' : (p * s - q * r) * (c - b) * ((p * s - q * r) * (d - a)) = 0 := by
      rcases mul_eq_zero.mp h with h | h <;> simp [h]
    simp [h, h']
  · field_simp
-- @endregion

end Lumenary.TransformationGeometry
