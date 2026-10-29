/-
The Lumenary — Lean exercises: Mathematical modelling with functions.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ModellingWithFunctions.lean`.
-/
import Lumenary.ModellingWithFunctions

namespace LumenaryExercises.ModellingWithFunctions

-- @region ex.modelling_with_functions.exponential_of_const_ratio
-- @solution Lumenary.ModellingWithFunctions.exponential_of_const_ratio
/-- Constant ratios mean an exponential model: if `u (n + 1) = b * u n` for every `n`, then
`u n = u 0 * b ^ n`. Hint: `induction n with`; in the successor step rewrite with `h n`, the
induction hypothesis and `pow_succ`, then finish with `ring`. -/
theorem exponential_of_const_ratio (u : ℕ → ℝ) (b : ℝ) (h : ∀ n, u (n + 1) = b * u n) (n : ℕ) :
    u n = u 0 * b ^ n := by
  sorry
-- @endregion

-- @region ex.modelling_with_functions.linear_of_const_diff
-- @solution Lumenary.ModellingWithFunctions.linear_of_const_diff
/-- Constant differences mean a linear model. Hint: induction on `n`; in the successor step
`have := h n`, then `push_cast` and `linarith`. -/
theorem linear_of_const_diff (u : ℕ → ℝ) (d : ℝ) (h : ∀ n, u (n + 1) - u n = d) (n : ℕ) :
    u n = u 0 + n * d := by
  sorry
-- @endregion

end LumenaryExercises.ModellingWithFunctions
