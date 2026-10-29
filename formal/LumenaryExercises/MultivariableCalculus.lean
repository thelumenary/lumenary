/-
The Lumenary — Lean exercises: Multivariable and vector calculus.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/MultivariableCalculus.lean`.
-/
import Lumenary.MultivariableCalculus

namespace LumenaryExercises.MultivariableCalculus

open Lumenary.MultivariableCalculus

-- @region ex.multivariable_calculus.xy_quot_not_differentiable_at
-- @solution Lumenary.MultivariableCalculus.xyQuot_not_differentiableAt
/-- Deduce that `xyQuot` is not differentiable at the origin.
Hint: use `Lumenary.MultivariableCalculus.xyQuot_not_continuousAt` and the fact that a
differentiable function is continuous, `DifferentiableAt.continuousAt`. -/
theorem xyQuot_not_differentiableAt : ¬ DifferentiableAt ℝ xyQuot 0 := by
  sorry
-- @endregion

-- @region ex.multivariable_calculus.circle_max_xy
-- @solution Lumenary.MultivariableCalculus.circle_max_xy
/-- On the circle `x² + y² = 2`, the product `xy` is at most `1`.
Hint: `nlinarith [sq_nonneg (x - y)]`. -/
theorem circle_max_xy (x y : ℝ) (h : x ^ 2 + y ^ 2 = 2) : x * y ≤ 1 := by
  sorry
-- @endregion

end LumenaryExercises.MultivariableCalculus
