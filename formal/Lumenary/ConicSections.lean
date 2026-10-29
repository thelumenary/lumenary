/-
The Lumenary — formal mathematics
Conic sections: focus–directrix and two-focus descriptions, standard equations, the reflective
property of the parabola, and the classification of quadratic curves by `B² − 4AC`.

Everything here is proved in coordinates, with real numbers (`@provenance independent`):
a point is equidistant from the focus `(0, p)` and the directrix `y = −p` exactly when
`x² = 4py`; a point satisfies `x²/a² + y²/b² = 1` exactly when its distances to the foci
`(±c, 0)` add up to `2a` (with `b² = a² − c²`); vertical rays reflect off a parabola through its
focus; completing the square for a circle; and the sign of `B² − 4AC` decides whether the
quadratic part `Ax² + Bxy + Cy²` is definite (ellipse type) or takes both signs (hyperbola type).
Mathlib has no theory of conics as such; from it we use the identity `cosh² t − sinh² t = 1`
(`@provenance library`) to parametrise a hyperbola.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Lumenary.ConicSections

open Real

/-! ### The parabola -/

-- @region conic_sections.parabola_focus_directrix
-- @provenance independent
/-- **The parabola as a locus.** A point `(x, y)` is as far from the focus `(0, p)` as from
the directrix, the line `y = −p`, exactly when `x² = 4py`. The distance to the focus is
`√(x² + (y − p)²)` and the distance to the line is `|y + p|`. Squaring both (they are
non-negative), `x² + (y − p)² = (y + p)²`, which simplifies to `x² = 4py`. -/
theorem parabola_focus_directrix (p x y : ℝ) :
    √(x ^ 2 + (y - p) ^ 2) = |y + p| ↔ x ^ 2 = 4 * p * y := by
  rw [← Real.sqrt_sq_eq_abs, Real.sqrt_inj (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith [h]
-- @endregion

-- @region conic_sections.dotp
-- @provenance definition
/-- The dot product of two vectors in the plane, `(u₁, u₂) · (v₁, v₂) = u₁ v₁ + u₂ v₂`. -/
def dotp (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
-- @endregion

-- @region conic_sections.reflect
-- @provenance definition
/-- The **law of reflection** for a direction `v` hitting a mirror whose normal vector is `n`:
the component of `v` along `n` is reversed and the rest is kept,
`reflect v n = v − (2 (v · n)/(n · n)) n`. -/
noncomputable def reflect (v n : ℝ × ℝ) : ℝ × ℝ := v - (2 * dotp v n / dotp n n) • n
-- @endregion

-- @region conic_sections.parabola_reflection
-- @provenance independent
/-- **The reflective property of the parabola** `y = x²/(4p)`. At the point
`P = (x₀, x₀²/(4p))` the tangent has direction `(2p, x₀)`, so `n = (x₀, −2p)` is a normal
vector. A ray coming straight down, with direction `(0, −1)`, is reflected to the direction
`reflect (0, −1) n`. The theorem says that this reflected direction, multiplied by the positive
number `x₀²/(4p) + p` (the distance `PF`), is exactly the vector from `P` to the focus
`F = (0, p)`: every vertical ray is reflected through the focus. -/
theorem parabola_reflection (p x₀ : ℝ) (hp : p ≠ 0) :
    (x₀ ^ 2 / (4 * p) + p) • reflect (0, -1) (x₀, -2 * p) = (0, p) - (x₀, x₀ ^ 2 / (4 * p)) := by
  have hN : x₀ ^ 2 + 4 * p ^ 2 ≠ 0 := by positivity
  have hN' : x₀ * x₀ + -(2 * p) * -(2 * p) ≠ 0 := by nlinarith [sq_nonneg x₀, sq_pos_of_ne_zero hp]
  simp only [reflect, dotp, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.ext_iff]
  constructor
  · field_simp
    ring
  · field_simp
    ring
-- @endregion

/-! ### The ellipse -/

-- @region conic_sections.ellipse_focal_radius
-- @provenance independent
/-- **The focal radius of an ellipse.** Let `0 ≤ c < a` and `b² = a² − c²`. On the ellipse
`x²/a² + y²/b² = 1`, the distance from `(x, y)` to the focus `(c, 0)` is `a − (c/a) x`.
Proof: substitute `y² = b² (1 − x²/a²)` into `(x − c)² + y²` and simplify to `(a − cx/a)²`;
since `|x| ≤ a` and `c < a`, the number `a − cx/a` is positive, so it is the square root. -/
theorem ellipse_focal_radius (a b c x y : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hb : b ^ 2 = a ^ 2 - c ^ 2) (h : x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1) :
    √((x - c) ^ 2 + y ^ 2) = a - c / a * x := by
  have hb2 : 0 < b ^ 2 := by nlinarith
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb2
  have hy : y ^ 2 = b ^ 2 - b ^ 2 * x ^ 2 / a ^ 2 := by
    have h1 : y ^ 2 / b ^ 2 = 1 - x ^ 2 / a ^ 2 := by linarith
    have h2 : y ^ 2 = b ^ 2 * (1 - x ^ 2 / a ^ 2) := by
      rw [← h1]; field_simp
    rw [h2]; ring
  have hx : x ^ 2 ≤ a ^ 2 := by
    have : y ^ 2 / b ^ 2 ≥ 0 := by positivity
    have h2 : x ^ 2 / a ^ 2 ≤ 1 := by linarith
    rwa [div_le_one (by positivity)] at h2
  have hxa : |x| ≤ a := abs_le_of_sq_le_sq hx ha.le
  have hpos : 0 ≤ a - c / a * x := by
    have h1 : c / a * x ≤ c / a * a := by
      apply mul_le_mul_of_nonneg_left (le_trans (le_abs_self x) hxa) (by positivity)
    have h2 : c / a * a = c := by field_simp
    linarith
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hpos]
  rw [hy, hb]
  field_simp
  ring
-- @endregion

-- @region conic_sections.ellipse_iff_focal_sum
-- @provenance independent
/-- **The ellipse: equation versus foci.** With `0 ≤ c < a` and `b² = a² − c²`, a point lies on
`x²/a² + y²/b² = 1` exactly when the sum of its distances to the foci `(c, 0)` and `(−c, 0)` is
`2a`. Forwards: add the two focal radii `a − cx/a` and `a + cx/a`. Backwards: if `d₁ + d₂ = 2a`,
then `d₂² − d₁² = 4cx` gives `d₂ − d₁ = 2cx/a`, so `d₁ = a − cx/a`; squaring this and
simplifying gives the equation. -/
theorem ellipse_iff_focal_sum (a b c x y : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hb : b ^ 2 = a ^ 2 - c ^ 2) :
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1 ↔
      √((x - c) ^ 2 + y ^ 2) + √((x + c) ^ 2 + y ^ 2) = 2 * a := by
  constructor
  · intro h
    have h1 := ellipse_focal_radius a b c x y ha hc hca hb h
    -- The other focus: reflect the picture in the y-axis (`x ↦ −x`).
    have h2 := ellipse_focal_radius a b c (-x) y ha hc hca hb (by rw [neg_sq]; exact h)
    rw [show (-x - c) ^ 2 = (x + c) ^ 2 by ring] at h2
    rw [h1, h2]
    ring
  · intro h
    set d₁ := √((x - c) ^ 2 + y ^ 2) with hd₁
    set d₂ := √((x + c) ^ 2 + y ^ 2) with hd₂
    have hsq₁ : d₁ ^ 2 = (x - c) ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
    have hsq₂ : d₂ ^ 2 = (x + c) ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
    -- `d₂² − d₁² = 4cx` and `d₁ + d₂ = 2a` give `d₂ − d₁ = 2cx/a`.
    have hdiff : (d₂ - d₁) * (2 * a) = 4 * c * x := by
      rw [← h]; nlinarith [hsq₁, hsq₂]
    have hd₁' : d₁ = a - c * x / a := by
      field_simp
      nlinarith [hdiff, h]
    have key : (a - c * x / a) ^ 2 = (x - c) ^ 2 + y ^ 2 := by rw [← hd₁', hsq₁]
    have hb2 : b ^ 2 ≠ 0 := by nlinarith
    rw [hb] at hb2 ⊢
    field_simp at key ⊢
    nlinarith [key]
-- @endregion

-- @region conic_sections.ellipse_param
-- @provenance independent
/-- The point `(a cos t, b sin t)` lies on the ellipse `x²/a² + y²/b² = 1` (for `a, b ≠ 0`):
the equation becomes `cos² t + sin² t = 1`. As `t` runs from `0` to `2π` the point goes once
round the ellipse; for `a = b` it is a circle. -/
theorem ellipse_param (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * cos t) ^ 2 / a ^ 2 + (b * sin t) ^ 2 / b ^ 2 = 1 := by
  rw [mul_pow, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 ha),
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hb), cos_sq_add_sin_sq]
-- @endregion

/-! ### The hyperbola -/

-- @region conic_sections.cosh_sq_sub_sinh_sq
-- @provenance library
/-- `cosh² t − sinh² t = 1`, the hyperbolic analogue of `cos² t + sin² t = 1`. Applies
Mathlib's `Real.cosh_sq_sub_sinh_sq`. (Here `cosh t = (eᵗ + e⁻ᵗ)/2`, `sinh t = (eᵗ − e⁻ᵗ)/2`.) -/
theorem cosh_sq_sub_sinh_sq (t : ℝ) : cosh t ^ 2 - sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
-- @endregion

-- @region conic_sections.hyperbola_param
-- @provenance independent
/-- The point `(a cosh t, b sinh t)` lies on the hyperbola `x²/a² − y²/b² = 1`; as `t` runs
over all real numbers it traces the right-hand branch (`cosh t ≥ 1`). This is why `cosh` and
`sinh` are called *hyperbolic* functions. -/
theorem hyperbola_param (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * cosh t) ^ 2 / a ^ 2 - (b * sinh t) ^ 2 / b ^ 2 = 1 := by
  rw [mul_pow, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 ha),
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hb), cosh_sq_sub_sinh_sq]
-- @endregion

/-! ### Second-degree equations -/

-- @region conic_sections.circle_complete_square
-- @provenance independent
/-- **Completing the square for a circle.**
`x² + y² + Dx + Ey + F = (x + D/2)² + (y + E/2)² − r²` with `r² = (D² + E²)/4 − F`. So the
equation `x² + y² + Dx + Ey + F = 0` describes a circle with centre `(−D/2, −E/2)` if `r² > 0`,
the single point `(−D/2, −E/2)` if `r² = 0`, and no points at all if `r² < 0`. -/
theorem circle_complete_square (D E F x y : ℝ) :
    x ^ 2 + y ^ 2 + D * x + E * y + F =
      (x + D / 2) ^ 2 + (y + E / 2) ^ 2 - ((D ^ 2 + E ^ 2) / 4 - F) := by
  ring
-- @endregion

-- @region conic_sections.definite_of_discriminant_neg
-- @provenance independent
/-- **Ellipse type.** If `A > 0` and `B² − 4AC < 0`, then `Ax² + Bxy + Cy² > 0` at every point
other than the origin. Completing the square,
`4A (Ax² + Bxy + Cy²) = (2Ax + By)² + (4AC − B²) y²`, a sum of two non-negative terms that are
both zero only when `y = 0` and then `x = 0`. So the level curves `Ax² + Bxy + Cy² = k` are
bounded: ellipses, a single point, or nothing. -/
theorem definite_of_discriminant_neg (A B C x y : ℝ) (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * C < 0)
    (hxy : (x, y) ≠ (0, 0)) : 0 < A * x ^ 2 + B * x * y + C * y ^ 2 := by
  have key : 4 * A * (A * x ^ 2 + B * x * y + C * y ^ 2) =
      (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 := by ring
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      intro hx; exact hxy (by rw [hx, hy])
    subst hy
    have : 0 < x ^ 2 := by positivity
    nlinarith
  · have hy2 : 0 < y ^ 2 := by positivity
    have : 0 < (4 * A * C - B ^ 2) * y ^ 2 := mul_pos (by linarith) hy2
    nlinarith [sq_nonneg (2 * A * x + B * y)]
-- @endregion

-- @region conic_sections.indefinite_of_discriminant_pos
-- @provenance independent
/-- **Hyperbola type.** If `B² − 4AC > 0`, then `Ax² + Bxy + Cy²` takes both positive and
negative values. If `A ≠ 0`, compare the points `(1, 0)` (value `A`) and `(−B, 2A)` (value
`A (4AC − B²)`, of the opposite sign). If `A = 0`, then `B ≠ 0`, and along the line `y = 1` the
value `Bx + C` takes every real value. So the level curves are unbounded, like hyperbolas. -/
theorem indefinite_of_discriminant_pos (A B C : ℝ) (hdisc : 0 < B ^ 2 - 4 * A * C) :
    (∃ x y : ℝ, 0 < A * x ^ 2 + B * x * y + C * y ^ 2) ∧
      (∃ x y : ℝ, A * x ^ 2 + B * x * y + C * y ^ 2 < 0) := by
  by_cases hA : A = 0
  · subst hA
    have hB : B ≠ 0 := by
      intro hB; subst hB; norm_num at hdisc
    refine ⟨⟨(1 - C) / B, 1, ?_⟩, ⟨(-1 - C) / B, 1, ?_⟩⟩
    · have h1 : B * ((1 - C) / B) = 1 - C := by field_simp
      simp only [zero_mul, zero_add, mul_one, one_pow]
      rw [h1]; linarith
    · have h1 : B * ((-1 - C) / B) = -1 - C := by field_simp
      simp only [zero_mul, zero_add, mul_one, one_pow]
      rw [h1]; linarith
  · have hval : A * (-B) ^ 2 + B * (-B) * (2 * A) + C * (2 * A) ^ 2 =
        A * (4 * A * C - B ^ 2) := by ring
    rcases lt_or_gt_of_ne hA with hneg | hpos
    · refine ⟨⟨-B, 2 * A, ?_⟩, ⟨1, 0, by nlinarith⟩⟩
      rw [hval]; nlinarith
    · refine ⟨⟨1, 0, by nlinarith⟩, ⟨-B, 2 * A, ?_⟩⟩
      rw [hval]; nlinarith
-- @endregion

end Lumenary.ConicSections
