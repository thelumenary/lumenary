/-
The Lumenary — formal mathematics
Probability theory: expectation and variance, linearity and indicators, independence,
Chebyshev's inequality, the weak law of large numbers, and Mathlib's strong law and central
limit theorem.

Mathlib builds probability on measure theory: a probability space is a measure `μ` with
`IsProbabilityMeasure μ`, a random variable is a (measurable) function `X : Ω → ℝ`, its
expectation is the integral `∫ ω, X ω ∂μ` (notation `μ[X]`), and `Var[X; μ]` is its variance.
Proved here from more basic facts (`@provenance independent`): Chebyshev's inequality from
Markov's, the weak law of large numbers with an explicit rate, linearity of expectation for
indicators, the mean of the geometric distribution, the memoryless property of the exponential
distribution, a pair of uncorrelated but dependent random variables, and the fact that a random
permutation has on average one fixed point (from Burnside's lemma). Cited from Mathlib
(`@provenance library`): Markov's inequality, the product rule for independent variables, the
additivity of variance, the binomial mean, the Gaussian mean and variance, the Poisson limit
theorem, the strong law of large numbers (Etemadi's proof) and the central limit theorem.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.Integration
import Mathlib.GroupTheory.GroupAction.Quotient

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace Lumenary.ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Linearity of expectation and indicators -/

-- @region probability_theory.expectation_sum_indicators
-- @provenance independent
/-- **Linearity of expectation for indicators.** For any events `A i` (`i ∈ s`), the expected
number of them that occur is the sum of their probabilities: `E[∑ 1_{A i}] = ∑ P(A i)`.
No independence is assumed. Proof: the integral of a finite sum is the sum of the integrals
(`integral_finsetSum`), and the integral of an indicator is the measure of the set
(`integral_indicator_one`). -/
theorem expectation_sum_indicators [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    ∫ ω, (∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω) ∂μ = ∑ i ∈ s, μ.real (A i) := by
  rw [integral_finsetSum]
  · exact sum_congr rfl fun i _ => integral_indicator_one (hA i)
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator (hA i)
-- @endregion

-- @region probability_theory.perm_fixed_points_average
-- @provenance independent
/-- **A random permutation has, on average, exactly one fixed point.** Summing the number of
fixed points over all permutations of a non-empty finite set gives the number of permutations.
The lesson proves this with indicators and linearity of expectation; here it follows from
Mathlib's **Burnside lemma** (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`:
the total number of fixed points is (number of orbits) × (size of the group)), because the
permutations of `α` move any point to any other, so there is exactly one orbit. -/
theorem perm_fixed_points_average (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    (∑ σ : Equiv.Perm α, Fintype.card (MulAction.fixedBy α σ)) =
      Fintype.card (Equiv.Perm α) := by
  classical
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  have h1 : Fintype.card (MulAction.orbitRel.Quotient (Equiv.Perm α) α) = 1 := by
    rw [Fintype.card_eq_one_iff]
    obtain ⟨a⟩ := ‹Nonempty α›
    refine ⟨Quotient.mk _ a, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      exact MulAction.exists_smul_eq (Equiv.Perm α) a b |>.imp fun g hg => hg
  rw [h1, one_mul]
-- @endregion

/-! ### Distributions -/

-- @region probability_theory.binomial_mean
-- @provenance library
/-- **The binomial mean.** If `X` has the binomial distribution `Bin(n, p)`, then `E[X] = np`.
This is Mathlib's `ProbabilityTheory.integral_of_hasLaw_binomial`, proved there with the
identity `k·C(n, k) = n·C(n − 1, k − 1)` and the binomial theorem; the lesson's proof writes
`X` as a sum of `n` indicators instead. -/
theorem binomial_mean {n : ℕ} {p : unitInterval} {X : Ω → ℝ}
    (hX : HasLaw X (Bin(ℝ, n, p)) μ) : μ[X] = (p : ℝ) * n :=
  integral_of_hasLaw_binomial hX
-- @endregion

-- @region probability_theory.geometric_mean
-- @provenance independent
/-- **The geometric mean.** If each trial succeeds with probability `p ∈ (0, 1]`, the number
of trials up to and including the first success takes the value `k + 1` with probability
`p (1 − p)ᵏ`, and its expectation is `∑ (k + 1) p (1 − p)ᵏ = 1/p`. Proof, as in the lesson:
with `r = 1 − p`, `∑ k rᵏ = r/(1 − r)²` (Mathlib's `hasSum_coe_mul_geometric_of_norm_lt_one`,
"differentiate the geometric series") and `∑ rᵏ = 1/(1 − r)`, so
`∑ (k + 1) rᵏ = 1/(1 − r)² = 1/p²`; multiply by `p`. -/
theorem geometric_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) * (p * (1 - p) ^ k)) (1 / p) := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_norm_lt_one hr
  have h3 := (h1.add h2).mul_left p
  have hp : p ≠ 0 := hp0.ne'
  convert h3 using 1
  · funext k
    ring
  · simp only [sub_sub_cancel]
    field_simp
    ring
-- @endregion

-- @region probability_theory.exponential_memoryless
-- @provenance independent
/-- **The exponential distribution is memoryless.** For Mathlib's exponential distribution
`expMeasure r` with rate `r > 0`, the survival function `P(T > x) = 1 − F(x)` satisfies
`P(T > s + t) = P(T > s) · P(T > t)` for `s, t ≥ 0`; equivalently
`P(T > s + t | T > s) = P(T > t)`. Proof: Mathlib's `cdf_expMeasure_eq` gives
`1 − F(x) = e^{−rx}` for `x ≥ 0`, and `e^{−r(s + t)} = e^{−rs} e^{−rt}`. -/
theorem exponential_memoryless {r : ℝ} (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    1 - cdf (expMeasure r) (s + t) = (1 - cdf (expMeasure r) s) * (1 - cdf (expMeasure r) t) := by
  simp only [cdf_expMeasure_eq hr, add_nonneg hs ht, hs, ht, ↓reduceIte, sub_sub_cancel]
  rw [← Real.exp_add]
  ring_nf
-- @endregion

-- @region probability_theory.gaussian_mean
-- @provenance library
/-- The normal distribution `N(m, v)` (Mathlib's `gaussianReal m v`) has mean `m`. This is
Mathlib's `ProbabilityTheory.integral_id_gaussianReal`. -/
theorem gaussian_mean (m : ℝ) (v : NNReal) : ∫ x, x ∂(gaussianReal m v) = m :=
  integral_id_gaussianReal
-- @endregion

-- @region probability_theory.gaussian_variance
-- @provenance library
/-- The normal distribution `N(m, v)` has variance `v`. This is Mathlib's
`ProbabilityTheory.variance_id_gaussianReal`. -/
theorem gaussian_variance (m : ℝ) (v : NNReal) : Var[id; gaussianReal m v] = v :=
  variance_id_gaussianReal
-- @endregion

-- @region probability_theory.poisson_limit
-- @provenance library
/-- **Poisson limit theorem.** If `n · pₙ → λ`, then the binomial probabilities
`C(n, k) pₙᵏ (1 − pₙ)ⁿ⁻ᵏ` tend to the Poisson probability `e^{−λ} λᵏ / k!` for each fixed `k`.
This is Mathlib's `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`; the lesson
proves the case `pₙ = λ/n`. -/
theorem poisson_limit {p : ℕ → ℝ} {lam : ℝ} (k : ℕ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto (fun n : ℕ => ((n.choose k : ℕ) : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) atTop
      (𝓝 (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ))) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k hp
-- @endregion

/-! ### Independence, covariance and variance -/

-- @region probability_theory.expectation_mul_indep
-- @provenance library
/-- **Independent variables multiply in expectation:** if `X` and `Y` are independent then
`E[XY] = E[X] E[Y]`. This is Mathlib's `IndepFun.integral_fun_mul_eq_mul_integral`.
Without independence (or at least zero covariance) the formula fails: see
`uncorrelated_not_independent` and the lesson's example `X = Y` a fair coin. -/
theorem expectation_mul_indep {X Y : Ω → ℝ} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ :=
  hXY.integral_fun_mul_eq_mul_integral hX hY
-- @endregion

-- @region probability_theory.variance_add_indep
-- @provenance library
/-- **Variances of independent variables add:** `Var(X + Y) = Var X + Var Y` when `X ⟂ Y` and
both have finite variance. This is Mathlib's `ProbabilityTheory.IndepFun.variance_add`.
(Mathlib also has the general formula with the covariance term.) -/
theorem variance_add_indep {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXY : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] :=
  hXY.variance_add hX hY
-- @endregion

-- @region probability_theory.uniform3
-- @provenance definition
/-- The average of a function on three equally likely outcomes `0, 1, 2`: the expectation for
the uniform distribution on `Fin 3`, computed exactly in `ℚ`. -/
def avg3 (f : Fin 3 → ℚ) : ℚ := (∑ i, f i) / 3
-- @endregion

-- @region probability_theory.uncorrelated_not_independent
-- @provenance independent
/-- **Uncorrelated does not imply independent.** Let `X` be uniform on `{−1, 0, 1}` and
`Y = X²`. Then `E[XY] = E[X] E[Y]` (both sides are `0`), yet `X` and `Y` are dependent:
`P(X = 1 and Y = 0) = 0` while `P(X = 1) · P(Y = 0) = 1/3 · 1/3`. The probabilities of events
are averages of indicator functions. Checked by exact rational arithmetic. -/
theorem uncorrelated_not_independent :
    let X : Fin 3 → ℚ := ![-1, 0, 1]
    let Y : Fin 3 → ℚ := fun i => X i ^ 2
    avg3 (fun i => X i * Y i) = avg3 X * avg3 Y ∧
      avg3 (fun i => if X i = 1 ∧ Y i = 0 then 1 else 0) ≠
        avg3 (fun i => if X i = 1 then 1 else 0) * avg3 (fun i => if Y i = 0 then 1 else 0) := by
  simp only [avg3, Fin.sum_univ_three]
  norm_num
-- @endregion

/-! ### Markov, Chebyshev and the weak law of large numbers -/

-- @region probability_theory.markov
-- @provenance library
/-- **Markov's inequality:** for a non-negative integrable `f` and any `a`,
`a · P(f ≥ a) ≤ E[f]`. This is Mathlib's `mul_meas_ge_le_integral_of_nonneg`. (The measure
theory lesson proves the version for `[0, ∞]`-valued functions.) -/
theorem markov {f : Ω → ℝ} (hf : 0 ≤ᵐ[μ] f) (hint : Integrable f μ) (a : ℝ) :
    a * μ.real {ω | a ≤ f ω} ≤ ∫ ω, f ω ∂μ :=
  mul_meas_ge_le_integral_of_nonneg hf hint a
-- @endregion

-- @region probability_theory.chebyshev
-- @provenance independent
/-- **Chebyshev's inequality**, proved from Markov's as in the lesson: for `X` with finite
variance and `c > 0`, `c² · P(|X − E X| ≥ c) ≤ Var X`. Proof: `|X − EX| ≥ c` happens exactly
when `(X − EX)² ≥ c²`; apply Markov's inequality to the non-negative variable `(X − EX)²`,
whose expectation is `Var X`. -/
theorem chebyshev [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) : c ^ 2 * μ.real {ω | c ≤ |X ω - μ[X]|} ≤ Var[X; μ] := by
  set m := μ[X]
  -- The events `{c ≤ |X − m|}` and `{c² ≤ (X − m)²}` are equal.
  have hset : {ω | c ≤ |X ω - m|} = {ω | c ^ 2 ≤ (X ω - m) ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [sq_le_sq, abs_of_pos hc]
  -- `(X − m)²` is non-negative and integrable.
  have hint : Integrable (fun ω => (X ω - m) ^ 2) μ :=
    (hX.sub (memLp_const m)).integrable_sq
  have hnn : 0 ≤ᵐ[μ] fun ω => (X ω - m) ^ 2 := Eventually.of_forall fun ω => sq_nonneg _
  rw [hset, variance_eq_integral hX.aestronglyMeasurable.aemeasurable]
  exact mul_meas_ge_le_integral_of_nonneg hnn hint (c ^ 2)
-- @endregion

-- @region probability_theory.chebyshev_library
-- @provenance library
/-- Mathlib's form of Chebyshev's inequality, `meas_ge_le_variance_div_sq`:
`P(|X − E X| ≥ c) ≤ Var X / c²`, with the probability as an extended non-negative real. -/
theorem chebyshev_library [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) :
    μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2) :=
  meas_ge_le_variance_div_sq hX hc
-- @endregion

-- @region probability_theory.weak_law_bound
-- @provenance independent
/-- **The weak law of large numbers, with a rate.** Let `X₀, X₁, …` be pairwise independent,
with finite variance, all with mean `m` and variance `v`. For `n ≥ 1` and `ε > 0`, the sample
mean `X̄ₙ = (X₀ + ⋯ + Xₙ₋₁)/n` satisfies `ε² · P(|X̄ₙ − m| ≥ ε) ≤ v / n`.
Proof, as in the lesson: `E[X̄ₙ] = m` by linearity; `Var X̄ₙ = (1/n²) · n v = v/n` because
variances of pairwise independent variables add (`IndepFun.variance_sum`) and
`Var(cX) = c² Var X`; then apply `chebyshev`. -/
theorem weak_law_bound [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m v : ℝ}
    (hL2 : ∀ i, MemLp (X i) 2 μ) (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m) (hvar : ∀ i, Var[X i; μ] = v) {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : 0 < ε) :
    ε ^ 2 * μ.real {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω - m|} ≤ v / n := by
  set S : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω with hS
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- The sample mean has finite variance.
  have hsum : MemLp (∑ i ∈ range n, X i) 2 μ := memLp_finsetSum' _ fun i _ => hL2 i
  have hSL2 : MemLp S 2 μ := by
    have := hsum.const_mul ((n : ℝ)⁻¹)
    convert this using 1
    funext ω
    simp [hS, Finset.sum_apply]
  -- Its expectation is `m` (linearity of expectation).
  have hES : μ[S] = m := by
    simp only [hS]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hL2 i).integrable one_le_two]
    simp only [hmean, sum_const, card_range, nsmul_eq_mul]
    field_simp
  -- Its variance is `v / n`.
  have hVS : Var[S; μ] = v / n := by
    have hS' : S = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω := by
      funext ω
      simp [hS, Finset.sum_apply]
    rw [hS', variance_const_mul,
      IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]
    simp only [hvar, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have key := chebyshev hSL2 hε
  rw [hES, hVS] at key
  exact key
-- @endregion

-- @region probability_theory.weak_law
-- @provenance independent
/-- **The weak law of large numbers.** Under the hypotheses of `weak_law_bound`, for every
`ε > 0`, `P(|X̄ₙ − m| ≥ ε) → 0` as `n → ∞`: the sample mean converges in probability to the
mean. Proof: the probability lies between `0` and `v / (n ε²)`, which tends to `0`. -/
theorem weak_law [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m v : ℝ}
    (hL2 : ∀ i, MemLp (X i) 2 μ) (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m) (hvar : ∀ i, Var[X i; μ] = v) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => μ.real {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω - m|}) atTop
      (𝓝 0) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  -- Upper bound `v / ε² · (1 / n)`, which tends to `0`.
  have hup : Tendsto (fun n : ℕ => v / ε ^ 2 * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (v / ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun n => measureReal_nonneg
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := weak_law_bound hL2 hindep hmean hvar hn hε
    set P := μ.real {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω - m|}
    calc P = ε ^ 2 * P / ε ^ 2 := by field_simp
      _ ≤ v / n / ε ^ 2 := div_le_div_of_nonneg_right h hε2.le
      _ = v / ε ^ 2 * (1 / (n : ℝ)) := by ring
-- @endregion

-- @region probability_theory.strong_law
-- @provenance library
/-- **The strong law of large numbers** (Kolmogorov; Etemadi's 1981 proof, which needs only
pairwise independence). If `X₀, X₁, …` are pairwise independent, identically distributed and
integrable, then almost surely `X̄ₙ → E[X₀]`. This is Mathlib's
`ProbabilityTheory.strong_law_ae`. Note that no finite variance is needed. -/
theorem strong_law [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω) atTop (𝓝 μ[X 0]) := by
  simpa [smul_eq_mul] using strong_law_ae X hint hindep hident
-- @endregion

/-! ### The central limit theorem -/

-- @region probability_theory.clt
-- @provenance library
/-- **The central limit theorem** (Lindeberg–Lévy form, standardised). If `X₀, X₁, …` are
independent and identically distributed with mean `0` and variance `1`, then
`(X₀ + ⋯ + Xₙ₋₁)/√n` converges in distribution to a standard normal variable `Y`. This is
Mathlib's `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`, proved with
characteristic functions and Lévy's continuity theorem, as sketched in the lesson. The general
case (mean `μ`, variance `σ² > 0`) follows by standardising `(Xᵢ − μ)/σ`. -/
theorem clt {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) P') (h0 : μ[X 0] = 0) (h1 : μ[X 0 ^ 2] = 1)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ k ∈ range n, X k ω) atTop Y
      (fun _ => μ) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum hY h0 h1 hindep hident
-- @endregion

end Lumenary.ProbabilityTheory
