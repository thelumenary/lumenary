/-
The Lumenary — Lean exercises: Geometric analysis.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/GeometricAnalysis.lean`.
-/
import Lumenary.GeometricAnalysis

namespace LumenaryExercises.GeometricAnalysis

open Real Lumenary.GeometricAnalysis

-- @region ex.geometric_analysis.heat_step_const
-- @solution Lumenary.GeometricAnalysis.heatStep_const
/-- Show that constant functions are fixed by one step of the heat scheme.
Hint: `funext i`, unfold with `simp only [heatStep]`, and finish with `ring`. -/
theorem heatStep_const (lam c : ℝ) : heatStep lam (fun _ => c) = fun _ => c := by
  sorry
-- @endregion

-- @region ex.geometric_analysis.catenary_first_integral
-- @solution Lumenary.GeometricAnalysis.catenary_first_integral
/-- Show that the catenary `y = a cosh(x/a)` has first integral `y / √(1 + y'²) = a`.
Hint: first prove `√(1 + sinh (x / a) ^ 2) = cosh (x / a)` using `cosh_sq'` and `sqrt_sq`
(with `cosh_pos`), then cancel `cosh (x / a)`. -/
theorem catenary_first_integral (a x : ℝ) :
    a * cosh (x / a) / √(1 + sinh (x / a) ^ 2) = a := by
  sorry
-- @endregion

end LumenaryExercises.GeometricAnalysis
