/-
The Lumenary — Lean exercises: Complex analysis.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ComplexAnalysis.lean`.
-/
import Lumenary.ComplexAnalysis

namespace LumenaryExercises.ComplexAnalysis

open Complex

-- @region ex.complex_analysis.liouville_from_cauchy_estimate
-- @solution Lumenary.ComplexAnalysis.liouville_from_cauchy_estimate
/-- Prove Liouville's theorem from the Cauchy estimate `Lumenary.ComplexAnalysis.cauchy_estimate`.
Hint: show `deriv f c = 0` for every `c` by applying the estimate on a circle of radius
`(M + 1) / ‖deriv f c‖`, then finish with `is_const_of_deriv_eq_zero`. -/
theorem liouville_from_cauchy_estimate {f : ℂ → ℂ} (hf : Differentiable ℂ f) {M : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (z w : ℂ) : f z = f w := by
  sorry
-- @endregion

end LumenaryExercises.ComplexAnalysis
