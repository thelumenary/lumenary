/-
The Lumenary — Lean exercises: Conic sections.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ConicSections.lean`.
-/
import Lumenary.ConicSections

namespace LumenaryExercises.ConicSections

open Real

-- @region ex.conic_sections.circle_complete_square
-- @solution Lumenary.ConicSections.circle_complete_square
/-- Completing the square for a circle. Hint: both sides are polynomials; one tactic does it. -/
theorem circle_complete_square (D E F x y : ℝ) :
    x ^ 2 + y ^ 2 + D * x + E * y + F =
      (x + D / 2) ^ 2 + (y + E / 2) ^ 2 - ((D ^ 2 + E ^ 2) / 4 - F) := by
  sorry
-- @endregion

-- @region ex.conic_sections.ellipse_param
-- @solution Lumenary.ConicSections.ellipse_param
/-- The point `(a cos t, b sin t)` lies on the ellipse `x²/a² + y²/b² = 1`.
Hint: `mul_pow`, then `mul_div_cancel_left₀` (twice), then `cos_sq_add_sin_sq`. -/
theorem ellipse_param (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * cos t) ^ 2 / a ^ 2 + (b * sin t) ^ 2 / b ^ 2 = 1 := by
  sorry
-- @endregion

end LumenaryExercises.ConicSections
