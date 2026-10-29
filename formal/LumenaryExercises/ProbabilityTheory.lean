/-
The Lumenary — Lean exercises: Probability theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProbabilityTheory.lean`.
-/
import Lumenary.ProbabilityTheory

open MeasureTheory ProbabilityTheory Filter

namespace LumenaryExercises.ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

-- @region ex.probability_theory.chebyshev
-- @solution Lumenary.ProbabilityTheory.chebyshev
/-- Prove Chebyshev's inequality from Markov's inequality.
Hints: (1) show `{ω | c ≤ |X ω - μ[X]|} = {ω | c ^ 2 ≤ (X ω - μ[X]) ^ 2}` using `sq_le_sq`
and `abs_of_pos`; (2) `(hX.sub (memLp_const _)).integrable_sq` gives integrability of the
square; (3) `variance_eq_integral` rewrites the variance as an integral; (4) finish with
Markov's inequality `mul_meas_ge_le_integral_of_nonneg`. -/
theorem chebyshev [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) : c ^ 2 * μ.real {ω | c ≤ |X ω - μ[X]|} ≤ Var[X; μ] := by
  sorry
-- @endregion

-- @region ex.probability_theory.exponential_memoryless
-- @solution Lumenary.ProbabilityTheory.exponential_memoryless
/-- Prove that the exponential distribution is memoryless.
Hint: `cdf_expMeasure_eq hr x` says `cdf (expMeasure r) x = if 0 ≤ x then 1 - exp (-(r * x))
else 0`; after simplifying the `if`s, use `Real.exp_add`. -/
theorem exponential_memoryless {r : ℝ} (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    1 - cdf (expMeasure r) (s + t) =
      (1 - cdf (expMeasure r) s) * (1 - cdf (expMeasure r) t) := by
  sorry
-- @endregion

end LumenaryExercises.ProbabilityTheory
