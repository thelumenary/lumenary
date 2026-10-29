/-
The Lumenary — Lean exercises: Programming for mathematics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProgrammingIntro.lean`.
-/
import Lumenary.ProgrammingIntro

namespace LumenaryExercises.ProgrammingIntro

open Lumenary.ProgrammingIntro

-- @region ex.programming_intro.no_solution_x_eq_x_add_one
-- @solution Lumenary.ProgrammingIntro.no_solution_x_eq_x_add_one
/-- The *equation* `x = x + 1` has no solution in the natural numbers (even though the
*assignment* `x := x + 1` is a perfectly good program step).
Hint: `intro ⟨x, hx⟩`, then `omega` finds the contradiction in `hx`. -/
theorem no_solution_x_eq_x_add_one : ¬ ∃ x : Nat, x = x + 1 := by
  sorry
-- @endregion

-- @region ex.programming_intro.sum_odds_eq_square
-- @solution Lumenary.ProgrammingIntro.sum_odds_eq_square
/-- Prove that the sum of the first `n` odd numbers is `n²` for **every** `n`.
Hint: `induction n with | zero => rfl | succ k ih => ?_`. In the step, `show
sumOdds k + (2 * k + 1) = (k + 1) * (k + 1)`, rewrite with `ih`, expand `(k + 1) * (k + 1)` with
`Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul`, and finish with `omega`. -/
theorem sum_odds_eq_square (n : Nat) : sumOdds n = n * n := by
  sorry
-- @endregion

end LumenaryExercises.ProgrammingIntro
