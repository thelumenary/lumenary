/-
The Lumenary — Lean exercises: Sampling and statistical reasoning.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/StatisticalInferenceIntro.lean`.
-/
import Lumenary.StatisticalInferenceIntro

namespace LumenaryExercises.StatisticalInferenceIntro

open Lumenary.StatisticalInferenceIntro

-- @region ex.statistical_inference_intro.mean_minimizes
-- @solution Lumenary.StatisticalInferenceIntro.mean_minimizes
/-- The mean minimises the sum of squared deviations.
Hint: rewrite with `sum_sq_sub hn x c`; the extra term `n * (mean x - c) ^ 2` is `≥ 0`
(`positivity`), and `linarith` finishes. -/
theorem mean_minimizes {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - mean x) ^ 2 ≤ ∑ i, (x i - c) ^ 2 := by
  sorry
-- @endregion

end LumenaryExercises.StatisticalInferenceIntro
