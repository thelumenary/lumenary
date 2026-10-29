/-
The Lumenary — Lean exercises: Estimation and rounding.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Estimation.lean`.
-/
import Lumenary.Estimation

namespace LumenaryExercises.Estimation

open Lumenary.Estimation

-- @region ex.estimation.round_hundred_error
-- @solution Lumenary.Estimation.roundHundred_error
/-- Show that rounding to the nearest hundred moves a number by at most `50`.
Hint: `unfold roundHundred`, then `omega` can finish (it understands division by `100`). -/
theorem roundHundred_error (n : Nat) : roundHundred n ≤ n + 50 ∧ n ≤ roundHundred n + 49 := by
  sorry
-- @endregion

-- @region ex.estimation.add_bounds
-- @solution Lumenary.Estimation.add_bounds
/-- Show that lower bounds add and upper bounds add.
Hint: `Nat.add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d`. -/
theorem add_bounds {a b la ua lb ub : Nat} (ha₁ : la ≤ a) (ha₂ : a ≤ ua)
    (hb₁ : lb ≤ b) (hb₂ : b ≤ ub) : la + lb ≤ a + b ∧ a + b ≤ ua + ub := by
  sorry
-- @endregion

end LumenaryExercises.Estimation
