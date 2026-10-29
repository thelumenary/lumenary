/-
The Lumenary — Lean exercises: Algorithm design and analysis.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AlgorithmDesign.lean`.
-/
import Lumenary.AlgorithmDesign

namespace LumenaryExercises.AlgorithmDesign

open Lumenary.AlgorithmDesign

-- @region ex.algorithm_design.four_items_need_five
-- @solution Lumenary.AlgorithmDesign.four_items_need_five
/-- Show that any decision tree with at least `4! = 24` leaves has height at least `5`.
Hint: apply `sorting_lower_bound`, then argue by contradiction: if the height were at most `4`,
then `2 ^ height ≤ 2 ^ 4 = 16 < 24` (`Nat.pow_le_pow_right`, then `omega`). -/
theorem four_items_need_five (t : DecisionTree) (h : (4 : ℕ).factorial ≤ t.leaves) :
    5 ≤ t.height := by
  sorry
-- @endregion

-- @region ex.algorithm_design.fib_pair_eq
-- @solution Lumenary.AlgorithmDesign.fibPair_eq
/-- Show that the dynamic-programming pair is correct: `fibPair n = (Fₙ, Fₙ₊₁)`.
Hint: induction on `n`; in the step, unfold `fibPair`, rewrite with the inductive hypothesis
and use `Nat.fib_add_two`. -/
theorem fibPair_eq (n : ℕ) : fibPair n = (Nat.fib n, Nat.fib (n + 1)) := by
  sorry
-- @endregion

end LumenaryExercises.AlgorithmDesign
