/-
The Lumenary — Lean exercises: The probabilistic method (counting principles).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProbabilisticMethod.lean`.
-/
import Lumenary.ProbabilisticMethod

namespace LumenaryExercises.ProbabilisticMethod

open Finset

-- @region ex.probabilistic_method.exists_avoiding
-- @solution Lumenary.ProbabilisticMethod.exists_avoiding
/-- The union bound: if the bad sets have total size less than `|Ω|`, some point avoids them all.
Hint: `card_biUnion_le` bounds `(S.biUnion B).card` by the sum, and
`exists_mem_notMem_of_card_lt_card` finds a point of `univ` outside the union. -/
theorem exists_avoiding {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] (S : Finset ι)
    (B : ι → Finset Ω) (h : ∑ i ∈ S, (B i).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i ∈ S, ω ∉ B i := by
  sorry
-- @endregion

-- @region ex.probabilistic_method.exists_ge_average
-- @solution Lumenary.ProbabilisticMethod.exists_ge_average
/-- The averaging principle: some value is at least the average.
Hint: argue by contradiction; `sum_lt_sum_of_nonempty` compares `∑ f` with `∑ c`, and
`sum_const` with `nsmul_eq_mul` evaluates the latter. -/
theorem exists_ge_average {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) (c : ℝ)
    (h : s.card * c ≤ ∑ ω ∈ s, f ω) : ∃ ω ∈ s, c ≤ f ω := by
  sorry
-- @endregion

end LumenaryExercises.ProbabilisticMethod
