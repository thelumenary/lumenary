/-
The Lumenary — Lean exercises: Markov chains.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/MarkovChains.lean`.
-/
import Lumenary.MarkovChains

open Finset Matrix

namespace LumenaryExercises.MarkovChains

variable {S : Type*} [Fintype S]

-- @region ex.markov_chains.detailed_balance_stationary
-- @solution Lumenary.MarkovChains.detailed_balance_stationary
/-- Prove that detailed balance implies stationarity.
Hints: `funext j`, unfold `vecMul` and `dotProduct`, rewrite each term with `hdb _ j`, then pull
`π j` out of the sum (`← mul_sum`) and use the row sum of row `j`. -/
theorem detailed_balance_stationary {P : Matrix S S ℝ} (hrow : ∀ i, ∑ j, P i j = 1)
    {π : S → ℝ} (hdb : ∀ i j, π i * P i j = π j * P j i) : π ᵥ* P = π := by
  sorry
-- @endregion

-- @region ex.markov_chains.zero_sum_vec_mul
-- @solution Lumenary.MarkovChains.zero_sum_vecMul
/-- Prove that a stochastic step preserves zero-sum vectors.
Hint: after unfolding, swap the two sums with `sum_comm` and use `mul_sum` and `hrow`. -/
theorem zero_sum_vecMul {P : Matrix S S ℝ} (hrow : ∀ i, ∑ j, P i j = 1) {x : S → ℝ}
    (hx : ∑ i, x i = 0) : ∑ j, (x ᵥ* P) j = 0 := by
  sorry
-- @endregion

end LumenaryExercises.MarkovChains
