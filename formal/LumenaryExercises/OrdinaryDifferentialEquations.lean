/-
The Lumenary — Lean exercises: Ordinary differential equations.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/OrdinaryDifferentialEquations.lean`.
-/
import Lumenary.OrdinaryDifferentialEquations

namespace LumenaryExercises.OrdinaryDifferentialEquations

open Real

-- @region ex.ordinary_differential_equations.exp_solves
-- @solution Lumenary.OrdinaryDifferentialEquations.exp_solves
/-- Check that `x(t) = x₀ e^{at}` solves `x' = a x`.
Hint: `((hasDerivAt_id' t).const_mul a).exp.const_mul x₀`, then `convert … using 1` and `ring`. -/
theorem exp_solves (a x₀ t : ℝ) :
    HasDerivAt (fun s => x₀ * exp (a * s)) (a * (x₀ * exp (a * t))) t := by
  sorry
-- @endregion

-- @region ex.ordinary_differential_equations.oscillator_unique
-- @solution Lumenary.OrdinaryDifferentialEquations.oscillator_unique
/-- Uniqueness for `x'' = -x` by conservation of energy.
Hint: show that `E s = x s ^ 2 + v s ^ 2` has derivative `0` everywhere (use `HasDerivAt.pow` and
`HasDerivAt.add`), conclude with `is_const_of_deriv_eq_zero` that `E t = E 0 = 0`, and finish
with `nlinarith`. -/
theorem oscillator_unique {x v : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (-x t) t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (t : ℝ) : x t = 0 := by
  sorry
-- @endregion

end LumenaryExercises.OrdinaryDifferentialEquations
