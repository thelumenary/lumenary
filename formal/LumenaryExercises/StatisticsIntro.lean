/-
The Lumenary — Lean exercises: Statistics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/StatisticsIntro.lean`.
-/
import Lumenary.StatisticsIntro

namespace LumenaryExercises.StatisticsIntro

open Lumenary.StatisticsIntro

-- @region ex.statistics_intro.outlier_example
-- @solution Lumenary.StatisticsIntro.outlier_example
/-- Check the outlier example: the median stays at `5`, the mean moves from `38/7` to `110/7`.
Hint: everything here is a finite computation — `decide +kernel` can do it. Then try your own
data: what happens to the median and the mean if the outlier is `800`? -/
theorem outlier_example :
    medianSorted [3, 4, 5, 5, 6, 7, 8] = 5 ∧ mean [3, 4, 5, 5, 6, 7, 8] = 38 / 7 ∧
    medianSorted [3, 4, 5, 5, 6, 7, 80] = 5 ∧ mean [3, 4, 5, 5, 6, 7, 80] = 110 / 7 := by
  sorry
-- @endregion

-- @region ex.statistics_intro.mean_minimises_sq
-- @solution Lumenary.StatisticsIntro.mean_minimises_sq
/-- The mean is the best centre for squared distances.
Hint: rewrite with `sum_sq_dev xs h c`. The extra term `n · (m - c)²` is non-negative by
`Rat.mul_nonneg Rat.natCast_nonneg (mul_self_nonneg _)`; then `grind` finishes. -/
theorem mean_minimises_sq (xs : List Rat) (h : xs ≠ []) (c : Rat) :
    (xs.map (fun x => (x - mean xs) * (x - mean xs))).sum
      ≤ (xs.map (fun x => (x - c) * (x - c))).sum := by
  sorry
-- @endregion

end LumenaryExercises.StatisticsIntro
