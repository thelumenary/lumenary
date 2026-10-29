/-
The Lumenary — Lean exercises: True, false, and, or, not.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LogicStatements.lean`.
-/
import Lumenary.LogicStatements

namespace LumenaryExercises.LogicStatements

-- @region ex.logic_statements.or_example
-- @solution Lumenary.LogicStatements.or_example
/-- Show that "6 is even or 6 is a multiple of 3" is true, and that "7 is even or 7 is bigger
than 10" is false.
Hint: these are statements about small numbers, so Lean can calculate: try `decide`. -/
theorem or_example : (6 % 2 = 0 ∨ 6 % 3 = 0) ∧ ¬ (7 % 2 = 0 ∨ 7 > 10) := by
  sorry
-- @endregion

-- @region ex.logic_statements.de_morgan_or
-- @solution Lumenary.LogicStatements.de_morgan_or
/-- Prove De Morgan's law for "or" by checking every row of the truth table.
Hint: `cases p <;> cases q <;> rfl` splits into the four rows and checks each one. -/
theorem de_morgan_or (p q : Bool) : (!(p || q)) = (!p && !q) := by
  sorry
-- @endregion

-- @region ex.logic_statements.ending_in_two_counterexample
-- @solution Lumenary.LogicStatements.ending_in_two_counterexample
/-- Show that not every number ending in 2 is divisible by 4.
Hint: start with `intro h`. Then `h 22 rfl` says that `22 % 4 = 0`. Is that true? -/
theorem ending_in_two_counterexample : ¬ ∀ n : Nat, n % 10 = 2 → n % 4 = 0 := by
  sorry
-- @endregion

end LumenaryExercises.LogicStatements
