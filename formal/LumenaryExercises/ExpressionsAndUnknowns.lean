/-
The Lumenary — Lean exercises: Expressions, unknowns and rules.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ExpressionsAndUnknowns.lean`.
-/
import Lumenary.ExpressionsAndUnknowns

namespace LumenaryExercises.ExpressionsAndUnknowns

open Lumenary.ExpressionsAndUnknowns

-- @region ex.expressions_and_unknowns.order_of_operations
-- @solution Lumenary.ExpressionsAndUnknowns.order_of_operations
/-- Check that Lean uses the same order of operations as the lesson.
Hint: these are calculations with small numbers, so `decide` can do them. -/
theorem order_of_operations : 2 + 3 * 4 = 14 ∧ (2 + 3) * 4 = 20 := by
  sorry
-- @endregion

-- @region ex.expressions_and_unknowns.double_add_one_table
-- @solution Lumenary.ExpressionsAndUnknowns.doubleAddOne_table
/-- Complete the table for the rule "double, then add 1".
Hint: Lean can work out every entry of the list itself — try `decide`. -/
theorem doubleAddOne_table : [1, 2, 3, 10].map doubleAddOne = [3, 5, 7, 21] := by
  sorry
-- @endregion

-- @region ex.expressions_and_unknowns.no_whole_answer
-- @solution Lumenary.ExpressionsAndUnknowns.no_whole_answer
/-- Show that 3 × □ = 25 has no whole-number answer.
Hint: the tactic `omega` knows a lot about adding and multiplying by fixed numbers. -/
theorem no_whole_answer : ¬ ∃ x : Nat, 3 * x = 25 := by
  sorry
-- @endregion

end LumenaryExercises.ExpressionsAndUnknowns
