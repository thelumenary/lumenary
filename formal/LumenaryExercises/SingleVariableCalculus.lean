/-
The Lumenary — Lean exercises: Calculus of one variable.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/SingleVariableCalculus.lean`.
-/
import Lumenary.SingleVariableCalculus

namespace LumenaryExercises.SingleVariableCalculus

open Set

-- @region ex.single_variable_calculus.const_of_deriv_zero
-- @solution Lumenary.SingleVariableCalculus.const_of_deriv_zero
/-- A function with derivative zero everywhere is constant.
Hint: for `u < v`, apply `Lumenary.SingleVariableCalculus.mvt_from_rolle` with `f' := fun _ => 0`;
continuity comes from `(hf t).continuousAt.continuousWithinAt`. Then treat `x < y`, `x = y`
and `x > y` with `lt_trichotomy`. -/
theorem const_of_deriv_zero {f : ℝ → ℝ} (hf : ∀ x, HasDerivAt f 0 x) (x y : ℝ) :
    f x = f y := by
  sorry
-- @endregion

-- @region ex.single_variable_calculus.integral_sq
-- @solution Lumenary.SingleVariableCalculus.integral_sq
/-- Compute `∫₀¹ x² dx` with the fundamental theorem of calculus.
Hint: the antiderivative is `x ^ 3 / 3`; use `(hasDerivAt_pow 3 x).div_const 3` and
`Lumenary.SingleVariableCalculus.ftc`. -/
theorem integral_sq : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  sorry
-- @endregion

end LumenaryExercises.SingleVariableCalculus
