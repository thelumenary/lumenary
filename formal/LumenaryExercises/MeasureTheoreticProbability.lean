/-
The Lumenary — Lean exercises: Measure-theoretic probability.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/MeasureTheoreticProbability.lean`.
-/
import Lumenary.MeasureTheoreticProbability

namespace LumenaryExercises.MeasureTheoreticProbability

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

-- @region ex.measure_theoretic_probability.borel_cantelli_first
-- @solution Lumenary.MeasureTheoreticProbability.borel_cantelli_first
/-- **First Borel–Cantelli lemma.** If `∑ μ(Aₙ) < ∞` then `μ(limsup Aₙ) = 0`.
Hint: show `limsup A atTop ⊆ ⋃ k, A (k + n)` for every `n` (rewrite with
`limsup_eq_iInf_iSup_of_nat'` and use `iInf_le`), bound by `measure_iUnion_le`, and let `n → ∞`
with `ENNReal.tendsto_sum_nat_add` and `ge_of_tendsto'`. -/
theorem borel_cantelli_first {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A : ℕ → Set Ω}
    (hA : ∑' n, μ (A n) ≠ ∞) : μ (limsup A atTop) = 0 := by
  sorry
-- @endregion

-- @region ex.measure_theoretic_probability.martingale_integral_eq
-- @solution Lumenary.MeasureTheoreticProbability.martingale_integral_eq
/-- **A martingale has constant expectation.**
Hint: `integral_condExp (𝓕.le i)` says `∫ μ[M j | 𝓕 i] = ∫ M j`; the martingale property
`hM.condExp_ae_eq hij` and `integral_congr_ae` do the rest. -/
theorem martingale_integral_eq {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Martingale M 𝓕 μ)
    {i j : ℕ} (hij : i ≤ j) : ∫ ω, M j ω ∂μ = ∫ ω, M i ω ∂μ := by
  sorry
-- @endregion

end LumenaryExercises.MeasureTheoreticProbability
