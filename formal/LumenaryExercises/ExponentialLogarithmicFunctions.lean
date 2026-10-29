/-
The Lumenary — Lean exercises: Exponential and logarithmic functions.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/ExponentialLogarithmicFunctions.lean`.
-/
import Lumenary.ExponentialLogarithmicFunctions

namespace LumenaryExercises.ExponentialLogarithmicFunctions

open Real

-- @region ex.exponential_logarithmic_functions.law_zero
-- @solution Lumenary.ExponentialLogarithmicFunctions.law_zero
/-- If `E(x + y) = E(x)·E(y)` for all `x, y` and `E` is not the zero function, then `E 0 = 1`.
Hint: `obtain ⟨x, hx⟩ := hE`, show `E x * E 0 = E x * 1` (rewrite `E x` as `E (x + 0)`), and
cancel with `mul_left_cancel₀ hx`. -/
theorem law_zero {E : ℝ → ℝ} (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) :
    E 0 = 1 := by
  sorry
-- @endregion

-- @region ex.exponential_logarithmic_functions.log_mul_from_exp
-- @solution Lumenary.ExponentialLogarithmicFunctions.log_mul_from_exp
/-- Derive the product law for logarithms from the exponential law.
Hint: `apply Real.exp_injective`, then rewrite with `Real.exp_add` and `Real.exp_log`. -/
theorem log_mul_from_exp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log (x * y) = log x + log y := by
  sorry
-- @endregion

end LumenaryExercises.ExponentialLogarithmicFunctions
