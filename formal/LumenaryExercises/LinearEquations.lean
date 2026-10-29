/-
The Lumenary — Lean exercises: Linear equations and inequalities.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LinearEquations.lean`.
-/
import Lumenary.LinearEquations

namespace LumenaryExercises.LinearEquations

-- @region ex.linear_equations.no_solution_example
-- @solution Lumenary.LinearEquations.no_solution_example
/-- Show that `2(x + 3) = 2x + 5` has no rational solution.
Hint: `intro ⟨x, h⟩` gives you a supposed solution. Derive `(6 : Rat) = 5` from `h` (the tactic
`grind` can do the algebra), then finish with `absurd` and `decide`. -/
theorem no_solution_example : ¬ ∃ x : Rat, 2 * (x + 3) = 2 * x + 5 := by
  sorry
-- @endregion

-- @region ex.linear_equations.notebooks
-- @solution Lumenary.LinearEquations.notebooks
/-- With `200` dirhams, a `45`-dirham book and `n` notebooks at `12` dirhams each are
affordable exactly when `n ≤ 12`. Prove it for whole numbers `n`.
Hint: this is linear arithmetic with whole numbers — the tactic `omega` decides it. Before you
use it, check the boundary cases `n = 12` and `n = 13` by hand. -/
theorem notebooks (n : Nat) : 45 + 12 * n ≤ 200 ↔ n ≤ 12 := by
  sorry
-- @endregion

end LumenaryExercises.LinearEquations
