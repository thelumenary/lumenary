/-
The Lumenary — Lean exercises: Variables and algebraic expressions.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/VariablesExpressions.lean`.
-/
import Lumenary.VariablesExpressions

namespace LumenaryExercises.VariablesExpressions

-- @region ex.variables_expressions.square_of_sum_counterexample
-- @solution Lumenary.VariablesExpressions.square_of_sum_counterexample
/-- Refute the tempting "identity" `(a + b)² = a² + b²` with a counterexample.
Hint: `intro h`, then specialise `h` to two small numbers with `have h11 := h 1 1`.
`revert h11` turns it back into a goal that `decide` can check by calculation. -/
theorem square_of_sum_counterexample : ¬ ∀ a b : Int, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  sorry
-- @endregion

-- @region ex.variables_expressions.square_of_difference
-- @solution Lumenary.VariablesExpressions.square_of_difference
/-- Prove `(a − b)² = a² − 2ab + b²`.
Hint: rewrite `a - b` as `a + -b` (`Int.sub_eq_add_neg`) and use
`Lumenary.VariablesExpressions.square_of_sum a (-b)`; `grind` can tidy up the signs. -/
theorem square_of_difference (a b : Int) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  sorry
-- @endregion

end LumenaryExercises.VariablesExpressions
