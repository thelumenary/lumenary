/-
The Lumenary — Lean exercises: Conditional probability and independence.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProbabilityRules.lean`.
-/
import Lumenary.ProbabilityRules

namespace LumenaryExercises.ProbabilityRules

open Lumenary.ProbabilityRules Finset

-- @region ex.probability_rules.exclusive_not_indep
-- @solution Lumenary.ProbabilityRules.FinProb.exclusive_not_indep
/-- Mutually exclusive events with positive probabilities are not independent.
Hint: after `intro h`, rewrite `h : μ.P (A ∩ B) = μ.P A * μ.P B` with `hdisj`; the probability
of `∅` is an empty sum (`sum_empty`), and `mul_ne_zero hA hB` finishes. -/
theorem exclusive_not_indep {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω)
    (A B : Finset Ω) (hdisj : A ∩ B = ∅) (hA : μ.P A ≠ 0) (hB : μ.P B ≠ 0) :
    ¬ μ.Indep A B := by
  sorry
-- @endregion

end LumenaryExercises.ProbabilityRules
