/-
The Lumenary — Lean exercises: Differential forms and Stokes' theorem.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/DifferentialForms.lean`.
-/
import Lumenary.DifferentialForms

namespace LumenaryExercises.DifferentialForms

open Lumenary.DifferentialForms

-- @region ex.differential_forms.wedge_antisymm
-- @solution Lumenary.DifferentialForms.wedge_antisymm
/-- Prove that the wedge product of 1-forms is anticommutative.
Hint: `unfold wedge`, then `ring`. -/
theorem wedge_antisymm {E : Type*} [AddCommGroup E] [Module ℝ E] (α β : E →ₗ[ℝ] ℝ) (u v : E) :
    wedge α β u v = -wedge β α u v := by
  sorry
-- @endregion

-- @region ex.differential_forms.d_theta_circle_integral
-- @solution Lumenary.DifferentialForms.dTheta_circle_integral
/-- Prove that `∮ dθ = 2π` around the unit circle.
Hint: rewrite the integrand with `dTheta_on_circle`, then use `intervalIntegral.integral_const`. -/
theorem dTheta_circle_integral :
    ∫ t in (0 : ℝ)..2 * Real.pi, dTheta (Real.cos t, Real.sin t) (-Real.sin t, Real.cos t) =
      2 * Real.pi := by
  sorry
-- @endregion

end LumenaryExercises.DifferentialForms
