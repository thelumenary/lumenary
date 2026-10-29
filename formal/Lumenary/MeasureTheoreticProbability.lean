/-
The Lumenary — formal mathematics
Measure-theoretic probability: the Borel–Cantelli lemmas, the weak and strong laws of large
numbers, conditional expectation, martingales and the central limit theorem.

Mathlib's probability library is built on its measure theory, exactly as Kolmogorov proposed:
a probability space is a measure space of total mass one, a random variable is a measurable
function, and `μ[X]` is the integral. Mathlib proves the second Borel–Cantelli lemma,
Kolmogorov's zero–one law, Etemadi's strong law of large numbers, the existence and properties
of conditional expectation, Doob's martingale convergence theorem, Lévy's continuity theorem and
the central limit theorem; we cite these. Proved here from more basic facts: the first
Borel–Cantelli lemma (by bounding a tail of a convergent series), the weak law of large numbers
with Chebyshev's explicit rate, and the fact that a martingale has constant expectation.
-/
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Lumenary.MeasureTheoreticProbability

/-! ### The Borel–Cantelli lemmas and the zero–one law -/

-- @region measure_theoretic_probability.borel_cantelli_first
-- @provenance independent
/-- **First Borel–Cantelli lemma.** If `∑ P(Aₙ) < ∞`, then almost surely only finitely many of
the events `Aₙ` occur: `P(limsup Aₙ) = 0`. No independence is needed. Proof (as in the lesson):
for every `n`, the event "infinitely many `Aₖ` occur" lies inside `⋃ₖ A_{k+n}`, whose probability
is at most the tail `∑ₖ P(A_{k+n})` of a convergent series, and the tails tend to `0`
(`ENNReal.tendsto_sum_nat_add`). Mathlib's version is `measure_limsup_atTop_eq_zero`. -/
theorem borel_cantelli_first {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A : ℕ → Set Ω}
    (hA : ∑' n, μ (A n) ≠ ∞) : μ (limsup A atTop) = 0 := by
  -- `limsup A = ⋂ n, ⋃ k, A (k + n)`, so it lies in each tail union.
  have hsub : ∀ n, limsup A atTop ⊆ ⋃ k, A (k + n) := fun n => by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact iInf_le (fun n => ⋃ k, A (k + n)) n
  -- Each tail union has probability at most the tail of the series.
  have hle : ∀ n, μ (limsup A atTop) ≤ ∑' k, μ (A (k + n)) := fun n =>
    (measure_mono (hsub n)).trans (measure_iUnion_le _)
  -- The tails of a convergent series tend to zero.
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_sum_nat_add _ hA) hle) (by simp)
-- @endregion

-- @region measure_theoretic_probability.borel_cantelli_second
-- @provenance library
/-- **Second Borel–Cantelli lemma.** If the events `Aₙ` are independent and `∑ P(Aₙ) = ∞`,
then almost surely infinitely many of them occur: `P(limsup Aₙ) = 1`. Independence cannot be
dropped (take `Aₙ = A` for one event with `0 < P(A) < 1`). This is Mathlib's
`ProbabilityTheory.measure_limsup_eq_one`. -/
theorem borel_cantelli_second {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : ℕ → Set Ω} (hmeas : ∀ n, MeasurableSet (A n)) (hindep : iIndepSet A μ)
    (hdiv : ∑' n, μ (A n) = ∞) : μ (limsup A atTop) = 1 :=
  measure_limsup_eq_one hmeas hindep hdiv
-- @endregion

-- @region measure_theoretic_probability.zero_one_law
-- @provenance library
/-- **Kolmogorov's zero–one law.** If `(𝓕ₙ)` is an independent sequence of sub-σ-algebras, every
event in the tail σ-algebra `limsup 𝓕ₙ = ⋂ₙ σ(𝓕ₙ, 𝓕ₙ₊₁, …)` has probability `0` or `1`. The event
"the sample means converge" is such a tail event. This is Mathlib's
`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`. -/
theorem zero_one_law {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : ℕ → MeasurableSpace Ω} (hle : ∀ n, 𝓕 n ≤ m0) (hindep : iIndep 𝓕 μ) {T : Set Ω}
    (htail : MeasurableSet[limsup 𝓕 atTop] T) : μ T = 0 ∨ μ T = 1 :=
  measure_zero_or_one_of_measurableSet_limsup_atTop hle hindep htail
-- @endregion

/-! ### Laws of large numbers -/

-- @region measure_theoretic_probability.weak_law
-- @provenance independent
/-- **Weak law of large numbers, with Chebyshev's rate.** Let `X₀, X₁, …` be pairwise independent
square-integrable random variables with common variance `σ²`, and let `Ȳₙ = (X₀ + ⋯ + X_{n-1})/n`.
Then `P(|Ȳₙ − E Ȳₙ| ≥ ε) ≤ σ² / (n ε²)`. Proof: by pairwise independence the variance of the sum
is the sum of the variances (`IndepFun.variance_sum`), so `Var Ȳₙ = n σ² / n² = σ²/n`; then apply
Chebyshev's inequality (`meas_ge_le_variance_div_sq`). The bound tends to `0` as `n → ∞`, which is
convergence in probability. -/
theorem weak_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hL2 : ∀ i, MemLp (X i) 2 μ) (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    {σ2 : ℝ} (hvar : ∀ i, Var[X i; μ] = σ2) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω -
        μ[fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω]|}
      ≤ ENNReal.ofReal (σ2 / (n * ε ^ 2)) := by
  have hsum : MemLp (∑ i ∈ Finset.range n, X i) 2 μ := memLp_finsetSum' _ fun i _ => hL2 i
  have hY : MemLp (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) 2 μ := by
    have := hsum.const_mul (n : ℝ)⁻¹
    convert this using 2 with ω
    simp [Finset.sum_apply]
  have hvarY : Var[fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω; μ] = σ2 / n := by
    have heq : (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω)
        = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω := by
      ext ω
      simp [Finset.sum_apply]
    rw [heq, variance_const_mul,
      IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]
    simp only [hvar, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  calc _ ≤ ENNReal.ofReal (Var[fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω; μ] / ε ^ 2) :=
        meas_ge_le_variance_div_sq hY hε
    _ = ENNReal.ofReal (σ2 / (n * ε ^ 2)) := by
        rw [hvarY, div_div]
-- @endregion

-- @region measure_theoretic_probability.strong_law
-- @provenance library
/-- **Strong law of large numbers** (Etemadi's version: pairwise independence suffices). If the
`Xᵢ` are pairwise independent, identically distributed and integrable, then almost surely the
sample means `(X₀ + ⋯ + X_{n-1})/n` converge to `E[X₀]`. This is Mathlib's
`ProbabilityTheory.strong_law_ae`, specialised to real-valued variables. -/
theorem strong_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ) (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) atTop
      (𝓝 μ[X 0]) := by
  simpa [smul_eq_mul] using strong_law_ae X hint hindep hident
-- @endregion

/-! ### Conditional expectation -/

-- @region measure_theoretic_probability.cond_exp_set_integral
-- @provenance library
/-- **The defining property of conditional expectation.** For a sub-σ-algebra `𝒢 ≤ 𝓕` and an
integrable `X`, the random variable `μ[X | 𝒢]` (it is a function on `Ω`, not a number) is
`𝒢`-measurable and has the same integral as `X` over every `𝒢`-measurable set. Mathlib
constructs it by extending the orthogonal projection of `L²` onto `L²(𝒢)` to `L¹`, and proves
this property as `setIntegral_condExp`. -/
theorem cond_exp_set_integral {Ω : Type*} {𝒢 m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (h𝒢 : 𝒢 ≤ m0) {X : Ω → ℝ} (hX : Integrable X μ) {G : Set Ω}
    (hG : MeasurableSet[𝒢] G) : ∫ ω in G, (μ[X | 𝒢]) ω ∂μ = ∫ ω in G, X ω ∂μ :=
  setIntegral_condExp h𝒢 hX hG
-- @endregion

-- @region measure_theoretic_probability.cond_exp_tower
-- @provenance library
/-- **Tower property.** Conditioning first on the finer σ-algebra `𝒢₂` and then on the coarser
`𝒢₁ ≤ 𝒢₂` is the same as conditioning on `𝒢₁` directly (almost surely). This is Mathlib's
`condExp_condExp_of_le`. -/
theorem cond_exp_tower {Ω : Type*} {𝒢₁ 𝒢₂ m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (h₁₂ : 𝒢₁ ≤ 𝒢₂) (h₂ : 𝒢₂ ≤ m0) (X : Ω → ℝ) :
    μ[μ[X | 𝒢₂] | 𝒢₁] =ᵐ[μ] μ[X | 𝒢₁] :=
  condExp_condExp_of_le h₁₂ h₂
-- @endregion

-- @region measure_theoretic_probability.cond_exp_pull_out
-- @provenance library
/-- **Taking out what is known.** If `Z` is `𝒢`-measurable and `Z · X` and `X` are integrable,
then `E[Z X | 𝒢] = Z · E[X | 𝒢]` almost surely. This is Mathlib's
`condExp_mul_of_stronglyMeasurable_left`. -/
theorem cond_exp_pull_out {Ω : Type*} {𝒢 m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {Z X : Ω → ℝ} (hZ : StronglyMeasurable[𝒢] Z) (hZX : Integrable (Z * X) μ)
    (hX : Integrable X μ) : μ[Z * X | 𝒢] =ᵐ[μ] Z * μ[X | 𝒢] :=
  condExp_mul_of_stronglyMeasurable_left hZ hZX hX
-- @endregion

-- @region measure_theoretic_probability.cond_exp_indep
-- @provenance library
/-- **Independent information is useless.** If `X` is measurable with respect to a σ-algebra
`𝓗` that is independent of `𝒢`, then `E[X | 𝒢] = E[X]`, a constant, almost surely. This is
Mathlib's `ProbabilityTheory.condExp_indep_eq`. -/
theorem cond_exp_indep {Ω : Type*} {𝓗 𝒢 m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h𝓗 : 𝓗 ≤ m0) (h𝒢 : 𝒢 ≤ m0) {X : Ω → ℝ}
    (hX : StronglyMeasurable[𝓗] X) (hindep : Indep 𝓗 𝒢 μ) :
    μ[X | 𝒢] =ᵐ[μ] fun _ => μ[X] :=
  condExp_indep_eq h𝓗 h𝒢 hX hindep
-- @endregion

/-! ### Martingales -/

-- @region measure_theoretic_probability.martingale_integral_eq
-- @provenance independent
/-- **A martingale has constant expectation.** If `(Mₙ)` is a martingale for the filtration
`(𝓕ₙ)` and `i ≤ j`, then `E[Mⱼ] = E[Mᵢ]`. Proof: integrating the conditional expectation does not
change the integral (`integral_condExp`, the defining property with `G = Ω`), and the martingale
property says `E[Mⱼ | 𝓕ᵢ] = Mᵢ` almost surely. -/
theorem martingale_integral_eq {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Martingale M 𝓕 μ)
    {i j : ℕ} (hij : i ≤ j) : ∫ ω, M j ω ∂μ = ∫ ω, M i ω ∂μ :=
  calc ∫ ω, M j ω ∂μ = ∫ ω, (μ[M j | 𝓕 i]) ω ∂μ := (integral_condExp (𝓕.le i)).symm
    _ = ∫ ω, M i ω ∂μ := integral_congr_ae (hM.condExp_ae_eq hij)
-- @endregion

-- @region measure_theoretic_probability.martingale_convergence
-- @provenance library
/-- **Doob's martingale convergence theorem.** An `L¹`-bounded martingale (`E|Mₙ| ≤ R` for all
`n`) converges almost surely; its limit is the `limitProcess`, measurable with respect to
`⋁ₙ 𝓕ₙ`. The proof goes through Doob's upcrossing inequality. This is Mathlib's
`Submartingale.ae_tendsto_limitProcess` (every martingale is a submartingale). -/
theorem martingale_convergence {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {R : ℝ≥0}
    (hM : Martingale M 𝓕 μ) (hbdd : ∀ n, eLpNorm (M n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (𝓕.limitProcess M μ ω)) :=
  hM.submartingale.ae_tendsto_limitProcess hbdd
-- @endregion

/-! ### Characteristic functions and the central limit theorem -/

-- @region measure_theoretic_probability.levy_continuity
-- @provenance library
/-- **Lévy's continuity theorem.** Probability measures on `ℝᵈ` converge weakly if and only if
their characteristic functions `φ(t) = ∫ e^{i⟨t, x⟩} dμ(x)` converge at every `t`. This is
Mathlib's `ProbabilityMeasure.tendsto_iff_tendsto_charFun`. -/
theorem levy_continuity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : ℕ → ProbabilityMeasure E}
    {μ₀ : ProbabilityMeasure E} :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : E, Tendsto (fun n => charFun (μ n : Measure E) t) atTop
        (𝓝 (charFun (μ₀ : Measure E) t)) :=
  ProbabilityMeasure.tendsto_iff_tendsto_charFun
-- @endregion

-- @region measure_theoretic_probability.central_limit
-- @provenance library
/-- **Central limit theorem.** If `X₀, X₁, …` are independent and identically distributed with
mean `0` and variance `1`, then `(X₀ + ⋯ + X_{n-1})/√n` converges in distribution to a standard
Gaussian `Y`. Mathlib proves it as in the lesson: the characteristic function of the normalised
sum is `φ(t/√n)ⁿ`, which tends to `e^{-t²/2}` by the second-order Taylor expansion of `φ`, and
Lévy's continuity theorem concludes. This is
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`. -/
theorem central_limit {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P') (h0 : P[X 0] = 0)
    (h1 : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ => P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum hY h0 h1 hindep hident
-- @endregion

end Lumenary.MeasureTheoreticProbability
