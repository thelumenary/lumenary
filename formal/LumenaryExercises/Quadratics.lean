/-
The Lumenary — Lean exercises: Quadratics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Quadratics.lean`.
-/
import Lumenary.Quadratics

namespace LumenaryExercises.Quadratics

-- @region ex.quadratics.times_four_a
-- @solution Lumenary.Quadratics.times_four_a
/-- Prove the identity behind completing the square:
`4a(ax² + bx + c) = (2ax + b)² − (b² − 4ac)`.
Hint: there are no fractions, so one tactic that expands both sides is enough. -/
theorem times_four_a (a b c x : ℝ) :
    4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
  sorry
-- @endregion

-- @region ex.quadratics.rectangle_max
-- @solution Lumenary.Quadratics.rectangle_max
/-- Among rectangles with perimeter `P`, the square has the largest area.
Hint: `P²/16 − x(P/2 − x) = (x − P/4)²`. For the first part, `nlinarith [sq_nonneg (x - P / 4)]`
may help; for the second, a square is zero only if the number is zero (`pow_eq_zero_iff`). -/
theorem rectangle_max (P x : ℝ) :
    x * (P / 2 - x) ≤ P ^ 2 / 16 ∧ (x * (P / 2 - x) = P ^ 2 / 16 ↔ x = P / 4) := by
  sorry
-- @endregion

end LumenaryExercises.Quadratics
