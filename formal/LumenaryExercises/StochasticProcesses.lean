/-
The Lumenary — Lean exercises: Stochastic processes.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/StochasticProcesses.lean`.
-/
import Lumenary.StochasticProcesses

namespace LumenaryExercises.StochasticProcesses

-- @region ex.stochastic_processes.discrete_stratonovich
-- @solution Lumenary.StochasticProcesses.discrete_stratonovich
/-- **Midpoint sums telescope.** Hint: induction on `n`; in the successor case rewrite with
`Finset.sum_range_succ` and the induction hypothesis, then `ring`. -/
theorem discrete_stratonovich (S : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (S k + S (k + 1)) / 2 * (S (k + 1) - S k) =
      (S n ^ 2 - S 0 ^ 2) / 2 := by
  sorry
-- @endregion

-- @region ex.stochastic_processes.random_walk_ito
-- @solution Lumenary.StochasticProcesses.random_walk_ito
/-- **Itô's formula for the simple random walk.** Hint: first show that the quadratic variation
`∑ k ∈ Finset.range n, (S (k + 1) - S k) ^ 2` equals `n` (each term is `1`), then rewrite with
`Lumenary.StochasticProcesses.discrete_ito`. -/
theorem random_walk_ito (S : ℕ → ℝ) (h0 : S 0 = 0)
    (hstep : ∀ k, S (k + 1) - S k = 1 ∨ S (k + 1) - S k = -1) (n : ℕ) :
    ∑ k ∈ Finset.range n, S k * (S (k + 1) - S k) = (S n ^ 2 - n) / 2 := by
  sorry
-- @endregion

end LumenaryExercises.StochasticProcesses
