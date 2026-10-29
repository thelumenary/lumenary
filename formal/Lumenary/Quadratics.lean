/-
The Lumenary — formal mathematics
Quadratic equations and functions: completing the square, the quadratic formula, the
discriminant, Vieta's formulas, the vertex and axis of symmetry, and an optimisation problem.

Proved here (`@provenance independent`), over the real numbers: the completed-square form
`ax² + bx + c = a(x + b/(2a))² − Δ/(4a)`; the quadratic formula (both directions: the two
numbers are roots, and there are no others); the three cases of the discriminant; Vieta's
formulas for two different roots; the minimum value at the vertex and the symmetry about the
axis `x = −b/(2a)`; and the largest rectangle with a given perimeter.

From Mathlib (`@provenance library`): the quadratic formula over any field in which `2 ≠ 0`
(`quadratic_eq_zero_iff`), and the converse direction "a quadratic that is never negative has
`Δ ≤ 0`" (`discrim_le_zero`). Mathlib writes `discrim a b c` for `b² − 4ac` and `x * x` for `x²`.
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Lumenary.Quadratics

/-! ### Completing the square and the quadratic formula -/

-- @region quadratics.complete_square
-- @provenance independent
/-- **Completing the square:** for `a ≠ 0`,
`ax² + bx + c = a(x + b/(2a))² − (b² − 4ac)/(4a)`.
`field_simp` clears the denominators `2a` and `4a`, and `ring` checks the resulting identity. -/
theorem complete_square {a b c : ℝ} (ha : a ≠ 0) (x : ℝ) :
    a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - (b ^ 2 - 4 * a * c) / (4 * a) := by
  field_simp
  ring
-- @endregion

-- @region quadratics.times_four_a
-- @provenance independent
/-- **The identity behind every case:** `4a(ax² + bx + c) = (2ax + b)² − (b² − 4ac)`.
This is completing the square with the fractions cleared, and it holds even when `a = 0`. -/
theorem times_four_a (a b c x : ℝ) :
    4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
  ring
-- @endregion

-- @region quadratics.quadratic_formula
-- @provenance independent
/-- **The quadratic formula.** If `a ≠ 0` and `Δ = b² − 4ac ≥ 0`, then
`ax² + bx + c = 0` exactly when `x = (−b + √Δ)/(2a)` or `x = (−b − √Δ)/(2a)`.
Proof: with `s = √Δ` (so `s² = Δ`), the quadratic factorises as `a(x − r₁)(x − r₂)` with
`r₁, r₂ = (−b ± s)/(2a)`; then use the zero-product property and `a ≠ 0`. Both directions are
proved: these numbers are roots, and there are no other roots. -/
theorem quadratic_formula {a b c : ℝ} (ha : a ≠ 0) (hΔ : 0 ≤ b ^ 2 - 4 * a * c) (x : ℝ) :
    a * x ^ 2 + b * x + c = 0 ↔
      x = (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) ∨
        x = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  set s := Real.sqrt (b ^ 2 - 4 * a * c) with hs
  have hs2 : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hΔ
  -- the factorisation `a(x − r₁)(x − r₂)`
  have expand : a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a)) =
      a * x ^ 2 + b * x + (b ^ 2 - s ^ 2) / (4 * a) := by
    field_simp
    ring
  have key : a * x ^ 2 + b * x + c = a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a)) := by
    rw [expand, hs2]
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 ha
      · exact Or.inl (sub_eq_zero.mp h4)
    · exact Or.inr (sub_eq_zero.mp h2)
  · rintro (h | h) <;> rw [h] <;> ring
-- @endregion

-- @region quadratics.quadratic_formula_library
-- @provenance library
/-- **The quadratic formula, Mathlib's form,** over any field in which `2 ≠ 0` (the rationals,
the reals, the complex numbers, the integers modulo an odd prime, …): if `s * s = b² − 4ac`
then the roots are `(−b ± s)/(2a)`. This applies `quadratic_eq_zero_iff`. Over the complex
numbers a square root `s` always exists, so every quadratic has roots there. -/
theorem quadratic_formula_library {K : Type*} [Field K] [NeZero (2 : K)] {a b c s : K}
    (ha : a ≠ 0) (h : discrim a b c = s * s) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) :=
  quadratic_eq_zero_iff ha h x
-- @endregion

/-! ### The discriminant decides how many real roots there are -/

-- @region quadratics.no_real_roots
-- @provenance independent
/-- **`Δ < 0`: no real roots.** If `ax² + bx + c = 0` then the identity `times_four_a` gives
`(2ax + b)² − Δ = 4a · 0 = 0` (`linear_combination` checks this), so `(2ax + b)² = Δ`. A square of
a real number is never negative, so `Δ ≥ 0`. (No assumption `a ≠ 0` is needed.) -/
theorem no_real_roots {a b c : ℝ} (hΔ : b ^ 2 - 4 * a * c < 0) (x : ℝ) :
    a * x ^ 2 + b * x + c ≠ 0 := by
  intro h
  have hsq : (2 * a * x + b) ^ 2 = b ^ 2 - 4 * a * c := by
    linear_combination 4 * a * h
  nlinarith [sq_nonneg (2 * a * x + b)]
-- @endregion

-- @region quadratics.one_root
-- @provenance independent
/-- **`Δ = 0`: exactly one real root,** `x = −b/(2a)` (a "double root").
By `times_four_a`, `4a(ax² + bx + c) = (2ax + b)²`, which is zero exactly when `2ax + b = 0`. -/
theorem one_root {a b c : ℝ} (ha : a ≠ 0) (hΔ : b ^ 2 - 4 * a * c = 0) (x : ℝ) :
    a * x ^ 2 + b * x + c = 0 ↔ x = -b / (2 * a) := by
  have h4 : 4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 := by
    rw [times_four_a, hΔ, sub_zero]
  constructor
  · intro h
    have hsq : (2 * a * x + b) ^ 2 = 0 := by rw [← h4, h, mul_zero]
    have hlin : 2 * a * x + b = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    field_simp
    linarith
  · intro hx
    have hlin : 2 * a * x + b = 0 := by rw [hx]; field_simp; ring
    have h4a : (4 * a) * (a * x ^ 2 + b * x + c) = 0 := by rw [h4, hlin]; ring
    rcases mul_eq_zero.mp h4a with h | h
    · exact absurd (by linarith : a = 0) ha
    · exact h
-- @endregion

-- @region quadratics.two_roots_distinct
-- @provenance independent
/-- **`Δ > 0`: the two roots are different.** They differ by `2√Δ/(2a)`, and `√Δ > 0`. -/
theorem two_roots_distinct {a b c : ℝ} (ha : a ≠ 0) (hΔ : 0 < b ^ 2 - 4 * a * c) :
    (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) ≠
      (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  have hs : 0 < Real.sqrt (b ^ 2 - 4 * a * c) := Real.sqrt_pos.mpr hΔ
  intro h
  have h2a : (2 * a) ≠ 0 := mul_ne_zero two_ne_zero ha
  rw [div_left_inj' h2a] at h
  linarith
-- @endregion

-- @region quadratics.discrim_le_zero_library
-- @provenance library
/-- **The converse view:** if `ax² + bx + c ≥ 0` for every `x`, then `Δ ≤ 0`.
(A parabola that never dips below the axis cannot cross it twice.) This applies Mathlib's
`discrim_le_zero`. -/
theorem discrim_le_zero_library {a b c : ℝ} (h : ∀ x : ℝ, 0 ≤ a * (x * x) + b * x + c) :
    discrim a b c ≤ 0 :=
  discrim_le_zero h
-- @endregion

/-! ### Vieta's formulas -/

-- @region quadratics.vieta
-- @provenance independent
/-- **Vieta's formulas.** If `r ≠ s` are both roots of `ax² + bx + c` with `a ≠ 0`, then
`r + s = −b/a` and `rs = c/a`.
Subtracting the two equations gives `(r − s)(a(r + s) + b) = 0`, and `r − s ≠ 0`; then
`c = −ar² − br = ar(r + s) − ar² = ars`. -/
theorem vieta {a b c r s : ℝ} (ha : a ≠ 0) (hrs : r ≠ s)
    (hr : a * r ^ 2 + b * r + c = 0) (hs : a * s ^ 2 + b * s + c = 0) :
    r + s = -b / a ∧ r * s = c / a := by
  have hdiff : (r - s) * (a * (r + s) + b) = 0 := by linear_combination hr - hs
  have hsum : a * (r + s) + b = 0 :=
    (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hrs)
  constructor
  · field_simp
    linarith
  · have hc : c = a * (r * s) := by linear_combination hr - r * hsum
    rw [hc]
    field_simp
-- @endregion

/-! ### The graph: vertex, axis of symmetry, optimisation -/

-- @region quadratics.vertex_min
-- @provenance independent
/-- **The vertex is the lowest point** when `a > 0`. With `h = −b/(2a)`,
`f(x) − f(h) = a(x − h)² ≥ 0` for every `x`. -/
theorem vertex_min {a b c : ℝ} (ha : 0 < a) (x : ℝ) :
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c ≤ a * x ^ 2 + b * x + c := by
  have hdiff : a * x ^ 2 + b * x + c - (a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c) =
      a * (x + b / (2 * a)) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ a * (x + b / (2 * a)) ^ 2 := by positivity
  linarith
-- @endregion

-- @region quadratics.vertex_value
-- @provenance independent
/-- **The height of the vertex** is `f(−b/(2a)) = c − b²/(4a) = −Δ/(4a)`. -/
theorem vertex_value {a b c : ℝ} (ha : a ≠ 0) :
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = -(b ^ 2 - 4 * a * c) / (4 * a) := by
  field_simp
  ring
-- @endregion

-- @region quadratics.axis_of_symmetry
-- @provenance independent
/-- **Axis of symmetry:** the parabola is symmetric about the vertical line `x = −b/(2a)`:
going a distance `t` to the right or to the left of it gives the same height. -/
theorem axis_of_symmetry {a b c : ℝ} (ha : a ≠ 0) (t : ℝ) :
    a * (-b / (2 * a) + t) ^ 2 + b * (-b / (2 * a) + t) + c =
      a * (-b / (2 * a) - t) ^ 2 + b * (-b / (2 * a) - t) + c := by
  field_simp
  ring
-- @endregion

-- @region quadratics.rectangle_max
-- @provenance independent
/-- **Optimisation:** among rectangles with perimeter `P`, the square has the largest area.
A rectangle with one side `x` has other side `P/2 − x`, and
`P²/16 − x(P/2 − x) = (x − P/4)² ≥ 0`, with equality exactly when `x = P/4`. -/
theorem rectangle_max (P x : ℝ) :
    x * (P / 2 - x) ≤ P ^ 2 / 16 ∧ (x * (P / 2 - x) = P ^ 2 / 16 ↔ x = P / 4) := by
  have key : P ^ 2 / 16 - x * (P / 2 - x) = (x - P / 4) ^ 2 := by ring
  refine ⟨by nlinarith [sq_nonneg (x - P / 4)], ?_⟩
  constructor
  · intro h
    have h0 : (x - P / 4) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith
  · rintro rfl
    ring
-- @endregion

end Lumenary.Quadratics
