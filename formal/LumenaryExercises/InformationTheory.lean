/-
The Lumenary — Lean exercises: Information theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/InformationTheory.lean`.
-/
import Lumenary.InformationTheory

open Finset Real

namespace LumenaryExercises.InformationTheory

variable {S : Type*} [Fintype S]

-- @region ex.information_theory.gibbs
-- @solution Lumenary.InformationTheory.gibbs
/-- Prove Gibbs' inequality. Hints: first show the termwise bound
`p x * log (q x / p x) ≤ q x - p x`, splitting into the cases `0 < p x` (use
`log_le_sub_one_of_pos`) and `p x = 0`; then sum with `sum_le_sum` and `sum_sub_distrib`. -/
theorem gibbs {p q : S → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ x, 0 < q x)
    (hq1 : ∑ x, q x ≤ 1) : ∑ x, p x * log (q x / p x) ≤ 0 := by
  sorry
-- @endregion

-- @region ex.information_theory.bsc_capacity
-- @solution Lumenary.InformationTheory.bsc_capacity
/-- Show that the uniform input attains `log 2 − h(p)` on the binary symmetric channel.
Hint: the output probability `½(1 − p) + ½ p` equals `2⁻¹`, and
`binEntropy_eq_log_two : binEntropy p = log 2 ↔ p = 2⁻¹`. -/
theorem bsc_capacity (p : ℝ) :
    Lumenary.InformationTheory.bscInfo p (1 / 2) = log 2 - binEntropy p := by
  sorry
-- @endregion

end LumenaryExercises.InformationTheory
