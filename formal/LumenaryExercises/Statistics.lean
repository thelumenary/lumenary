/-
The Lumenary — Lean exercises: Statistical inference.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Statistics.lean`.
-/
import Lumenary.Statistics

open Finset

namespace LumenaryExercises.Statistics

open Lumenary.Statistics

-- @region ex.statistics.sum_sq_dev_eq
-- @solution Lumenary.Statistics.sum_sq_dev_eq
/-- Prove the shift identity `∑ (xᵢ − x̄)² = ∑ (xᵢ − c)² − n (x̄ − c)²`.
Hints: first show `∑ (xᵢ − c) = n (x̄ − c)` using `sum_eq_card_mul_mean`; then rewrite each
`(xᵢ − x̄)²` as `(xᵢ − c)² − 2 (x̄ − c)(xᵢ − c) + (x̄ − c)²` (`ring`) and split the sum with
`sum_add_distrib`, `sum_sub_distrib` and `mul_sum`. -/
theorem sum_sq_dev_eq {ι : Type*} (s : Finset ι) (x : ι → ℝ) (c : ℝ) :
    ∑ i ∈ s, (x i - sampleMean s x) ^ 2 =
      ∑ i ∈ s, (x i - c) ^ 2 - s.card * (sampleMean s x - c) ^ 2 := by
  sorry
-- @endregion

-- @region ex.statistics.fwer_independent_le
-- @solution Lumenary.Statistics.fwer_independent_le
/-- Show that the family-wise error rate `1 − (1 − α)ᵐ` of `m` independent tests is at most
`mα`. Hint: Bernoulli's inequality is `one_add_mul_le_pow : -2 ≤ a → 1 + n * a ≤ (1 + a) ^ n`. -/
theorem fwer_independent_le {α : ℝ} (h1 : α ≤ 1) (m : ℕ) :
    1 - (1 - α) ^ m ≤ m * α := by
  sorry
-- @endregion

end LumenaryExercises.Statistics
