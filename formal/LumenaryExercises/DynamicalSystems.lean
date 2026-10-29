/-
The Lumenary — Lean exercises: Dynamical systems and chaos.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/DynamicalSystems.lean`.
-/
import Lumenary.DynamicalSystems

namespace LumenaryExercises.DynamicalSystems

-- @region ex.dynamical_systems.logistic_stable_iff
-- @solution Lumenary.DynamicalSystems.logistic_stable_iff
/-- The multiplier of the fixed point `1 - 1/r` of the logistic map is `2 - r`. Show that it has
absolute value less than `1` exactly when `1 < r < 3`.
Hint: `rw [abs_lt]`, then split both directions and finish with `linarith`. -/
theorem logistic_stable_iff (r : ℝ) : |2 - r| < 1 ↔ 1 < r ∧ r < 3 := by
  sorry
-- @endregion

-- @region ex.dynamical_systems.doubling_separates
-- @solution Lumenary.DynamicalSystems.doubling_separates
/-- Show that `n` steps of `z ↦ 2z` multiply the distance between two points by `2ⁿ`.
Hint: induction on `n`; `Function.iterate_succ_apply'` rewrites `f^[n+1] x` as `f (f^[n] x)`. -/
theorem doubling_separates (x y : ℝ) (n : ℕ) :
    (fun z : ℝ => 2 * z)^[n] x - (fun z : ℝ => 2 * z)^[n] y = 2 ^ n * (x - y) := by
  sorry
-- @endregion

end LumenaryExercises.DynamicalSystems
