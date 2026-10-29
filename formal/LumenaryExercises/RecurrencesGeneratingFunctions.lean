/-
The Lumenary — Lean exercises: Recurrences and generating functions.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/RecurrencesGeneratingFunctions.lean`.
-/
import Lumenary.RecurrencesGeneratingFunctions

namespace LumenaryExercises.RecurrencesGeneratingFunctions

open Lumenary.RecurrencesGeneratingFunctions

-- @region ex.recurrences_generating_functions.three_pow_is_sol
-- @solution Lumenary.RecurrencesGeneratingFunctions.three_pow_isSol
/-- Show that `aₙ = 3ⁿ` solves `aₙ₊₂ = 5aₙ₊₁ − 6aₙ`.
Hint: `isSol_geom` reduces the goal to `3 ^ 2 = 5 * 3 + -6`, which `norm_num` can check. -/
theorem three_pow_isSol : IsSol 5 (-6) (fun n => (3 : ℝ) ^ n) := by
  sorry
-- @endregion

-- @region ex.recurrences_generating_functions.hanoi_eq
-- @solution Lumenary.RecurrencesGeneratingFunctions.hanoi_eq
/-- Show that the Tower of Hanoi needs `2ⁿ − 1` moves, in the subtraction-free form
`hanoi n + 1 = 2 ^ n`.
Hint: induction on `n`; in the step, `hanoi (k + 1) + 1 = 2 * (hanoi k + 1)`. -/
theorem hanoi_eq (n : ℕ) : hanoi n + 1 = 2 ^ n := by
  sorry
-- @endregion

end LumenaryExercises.RecurrencesGeneratingFunctions
