/-
The Lumenary — formal mathematics
Stochastic processes: Poisson processes, continuous-time Markov chains, Brownian motion and the
first steps of Itô calculus.

Mathlib defines (pre-)Brownian motion through its finite-dimensional Gaussian laws, and proves
that its covariance is `min s t`, that its increments are independent and Gaussian, and that it
is invariant under scaling and time inversion; it has Poisson distributions, their convolution
and the Poisson limit theorem, and the exponential distribution. It does not (yet) construct the
Itô integral. Proved here from more basic facts: the discrete Itô and Stratonovich formulas for
`∑ Sₖ (Sₖ₊₁ − Sₖ)` (the finite skeleton of `∫ B dB = (B_t² − t)/2`), the Poisson convolution
identity `Po(s) ∗ Po(t) = Po(s + t)` by the binomial theorem, the memorylessness of exponential
waiting times, the solution of the two-state Kolmogorov forward equation, and the calculus
identity behind the solution of the geometric Brownian motion equation.
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Lumenary.StochasticProcesses

/-! ### Discrete stochastic integrals: why Itô's chain rule has an extra term -/

-- @region stochastic_processes.discrete_ito
-- @provenance independent
/-- **The discrete Itô formula.** For any real sequence `S₀, S₁, …` the left-point sums satisfy
`∑_{k<n} Sₖ (Sₖ₊₁ − Sₖ) = (Sₙ² − S₀²)/2 − ½ ∑_{k<n} (Sₖ₊₁ − Sₖ)²`.
The last sum is the quadratic variation. For a smooth path it tends to `0` under refinement and we
recover `∫ S dS = (Sₙ² − S₀²)/2`; for Brownian motion it tends to `t`, which gives
`∫₀ᵗ B dB = (B_t² − t)/2`. Proof: induction on `n`; each step is the identity
`a (b − a) = (b² − a²)/2 − (b − a)²/2`. -/
theorem discrete_ito (S : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, S k * (S (k + 1) - S k) =
      (S n ^ 2 - S 0 ^ 2) / 2 - (∑ k ∈ Finset.range n, (S (k + 1) - S k) ^ 2) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring
-- @endregion

-- @region stochastic_processes.discrete_stratonovich
-- @provenance independent
/-- **The discrete Stratonovich formula.** With midpoint values `(Sₖ + Sₖ₊₁)/2` instead of
left-point values, the sum telescopes exactly and the ordinary chain rule holds:
`∑_{k<n} (Sₖ + Sₖ₊₁)/2 · (Sₖ₊₁ − Sₖ) = (Sₙ² − S₀²)/2`. The two sums differ by half the quadratic
variation, so for Brownian paths the choice of evaluation point matters. -/
theorem discrete_stratonovich (S : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (S k + S (k + 1)) / 2 * (S (k + 1) - S k) = (S n ^ 2 - S 0 ^ 2) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
-- @endregion

-- @region stochastic_processes.random_walk_ito
-- @provenance independent
/-- **Itô's formula for the simple random walk.** If `S₀ = 0` and every step is `±1`, the
quadratic variation after `n` steps is exactly `n`, so
`∑_{k<n} Sₖ (Sₖ₊₁ − Sₖ) = (Sₙ² − n)/2`. Rescaling space by `√n` and time by `n` turns this into
`∫₀¹ B dB = (B₁² − 1)/2`. Proof: the discrete Itô formula with `(±1)² = 1`. -/
theorem random_walk_ito (S : ℕ → ℝ) (h0 : S 0 = 0)
    (hstep : ∀ k, S (k + 1) - S k = 1 ∨ S (k + 1) - S k = -1) (n : ℕ) :
    ∑ k ∈ Finset.range n, S k * (S (k + 1) - S k) = (S n ^ 2 - n) / 2 := by
  have hqv : ∑ k ∈ Finset.range n, (S (k + 1) - S k) ^ 2 = n := by
    rw [Finset.sum_congr rfl fun k _ => show (S (k + 1) - S k) ^ 2 = 1 by
      rcases hstep k with h | h <;> rw [h] <;> norm_num]
    simp
  rw [discrete_ito, h0, hqv]
  ring
-- @endregion

/-! ### The Poisson process -/

-- @region stochastic_processes.poisson_pmf
-- @provenance definition
/-- The Poisson probabilities `pₖ(r) = e^{-r} rᵏ / k!`: the probability of exactly `k` arrivals
in a time interval of length `t` for a Poisson process of rate `λ`, with `r = λt`. -/
noncomputable def poissonPMF (r : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-r) * r ^ k / k.factorial
-- @endregion

-- @region stochastic_processes.poisson_pmf_eq
-- @provenance library
/-- Our `poissonPMF` agrees with the point masses of Mathlib's Poisson distribution `Po(r)`
(`ProbabilityTheory.poissonMeasure_real_singleton`). -/
theorem poissonPMF_eq (r : ℝ≥0) (k : ℕ) : (poissonMeasure r).real {k} = poissonPMF r k :=
  poissonMeasure_real_singleton r k
-- @endregion

-- @region stochastic_processes.poisson_convolution
-- @provenance independent
/-- **Poisson counts add.** `∑_{j ≤ k} pⱼ(s) p_{k−j}(t) = pₖ(s + t)`: if `N_s` and `N_{s+t} − N_s`
are independent Poisson variables with means `s` and `t`, their sum is Poisson with mean
`s + t`. This is the consistency (Chapman–Kolmogorov) condition that makes the Poisson process
well defined. Proof: expand `(s + t)ᵏ` by the binomial theorem (`add_pow`) and write
`C(k, j) = k! / (j! (k − j)!)` (`Nat.cast_choose`). -/
theorem poisson_convolution (s t : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), poissonPMF s j * poissonPMF t (k - j) = poissonPMF (s + t) k := by
  simp only [poissonPMF]
  rw [add_pow, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.cast_choose ℝ hjk, neg_add, Real.exp_add]
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((k - j).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
-- @endregion

-- @region stochastic_processes.poisson_conv
-- @provenance library
/-- Mathlib's measure-level statement of the same fact: the convolution of `Po(r₁)` and `Po(r₂)`
is `Po(r₁ + r₂)`, proved through characteristic functions
(`ProbabilityTheory.poissonMeasure_conv_poissonMeasure`). -/
theorem poisson_conv (r₁ r₂ : ℝ≥0) :
    poissonMeasure r₁ ∗ poissonMeasure r₂ = poissonMeasure (r₁ + r₂) :=
  poissonMeasure_conv_poissonMeasure r₁ r₂
-- @endregion

-- @region stochastic_processes.law_of_rare_events
-- @provenance library
/-- **The law of rare events** (Poisson limit theorem). If `n pₙ → r`, the binomial
probabilities `C(n, k) pₙᵏ (1 − pₙ)^{n−k}` tend to `e^{-r} rᵏ / k!`. Chop `[0, t]` into `n` slots
with an arrival in each with probability `λt/n`: in the limit the count is Poisson. This is
Mathlib's `tendsto_choose_mul_pow_of_tendsto_mul_atTop`. -/
theorem law_of_rare_events {p : ℕ → ℝ} {r : ℝ} (k : ℕ)
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * p n ^ k * (1 - p n) ^ (n - k)) atTop
      (𝓝 (Real.exp (-r) * r ^ k / k.factorial)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr
-- @endregion

-- @region stochastic_processes.exp_memoryless
-- @provenance independent
/-- **Exponential waiting times are memoryless.** If `T` has the exponential distribution with
rate `r > 0`, then `P(T > s + t) = P(T > s) · P(T > t)` for `s, t ≥ 0`, i.e.
`P(T > s + t | T > s) = P(T > t)`: having waited `s` units tells you nothing. This is why the
holding times of a Poisson process (and of any continuous-time Markov chain) are exponential.
Proof: Mathlib's formula `F(x) = 1 − e^{−rx}` for the distribution function (`cdf_expMeasure_eq`)
and `e^{a+b} = eᵃ eᵇ`. -/
theorem exp_memoryless {r : ℝ} (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    1 - cdf (expMeasure r) (s + t) =
      (1 - cdf (expMeasure r) s) * (1 - cdf (expMeasure r) t) := by
  rw [cdf_expMeasure_eq hr, cdf_expMeasure_eq hr, cdf_expMeasure_eq hr]
  simp only [add_nonneg hs ht, hs, ht, ite_true, sub_sub_cancel]
  rw [← Real.exp_add]
  ring_nf
-- @endregion

/-! ### Continuous-time Markov chains -/

-- @region stochastic_processes.two_state_forward
-- @provenance independent
/-- **The two-state chain solves Kolmogorov's forward equation.** A chain on `{0, 1}` jumps
`0 → 1` at rate `a` and `1 → 0` at rate `b` (with `a + b > 0`). Its transition probability
`p(t) = P(X_t = 0 | X_0 = 0) = b/(a+b) + a/(a+b) · e^{−(a+b)t}` satisfies `p(0) = 1` and
`p′(t) = −a p(t) + b (1 − p(t))`: probability flows out of `0` at rate `a` and back in at rate
`b`. As `t → ∞`, `p(t) → b/(a+b)`, the stationary probability of state `0`. -/
theorem two_state_forward {a b : ℝ} (hab : 0 < a + b) (t : ℝ) :
    (b / (a + b) + a / (a + b) * Real.exp (-(a + b) * 0) = 1) ∧
    HasDerivAt (fun s => b / (a + b) + a / (a + b) * Real.exp (-(a + b) * s))
      (-a * (b / (a + b) + a / (a + b) * Real.exp (-(a + b) * t)) +
        b * (1 - (b / (a + b) + a / (a + b) * Real.exp (-(a + b) * t)))) t := by
  have hne : a + b ≠ 0 := hab.ne'
  constructor
  · field_simp
    simp
    ring
  · have hexp : HasDerivAt (fun s => Real.exp (-(a + b) * s))
        (Real.exp (-(a + b) * t) * (-(a + b))) t := by
      have := ((hasDerivAt_id t).const_mul (-(a + b))).exp
      simpa using this
    convert (hexp.const_mul (a / (a + b))).const_add (b / (a + b)) using 1
    field_simp
    ring
-- @endregion

/-! ### Brownian motion (Mathlib) -/

-- @region stochastic_processes.brownian_covariance
-- @provenance library
/-- **The covariance of Brownian motion** is `Cov(B_s, B_t) = min(s, t)`. Together with
`E[B_t] = 0` and Gaussian finite-dimensional laws this characterises (pre-)Brownian motion. This
is Mathlib's `IsPreBrownianReal.covariance_eval`. -/
theorem brownian_covariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = ((min s t : ℝ≥0) : ℝ) :=
  hB.covariance_eval s t
-- @endregion

-- @region stochastic_processes.brownian_increment
-- @provenance library
/-- **Brownian increments are Gaussian:** `B_s − B_t` has law `N(0, |s − t|)`. This is Mathlib's
`IsPreBrownianReal.hasLaw_sub`. -/
theorem brownian_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P :=
  hB.hasLaw_sub s t
-- @endregion

-- @region stochastic_processes.brownian_indep_increments
-- @provenance library
/-- **Brownian increments over disjoint intervals are independent.** This is Mathlib's
`IsPreBrownianReal.hasIndepIncrements`. -/
theorem brownian_indep_increments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) : HasIndepIncrements B P :=
  hB.hasIndepIncrements
-- @endregion

-- @region stochastic_processes.brownian_scaling
-- @provenance library
/-- **Brownian scaling.** If `B` is a Brownian motion and `c > 0`, then `t ↦ c^{−1/2} B_{ct}` is
again a Brownian motion: zooming in on a Brownian path by `c` in time and `√c` in space gives a
Brownian path. This is Mathlib's `IsBrownianReal.smul`. -/
theorem brownian_scaling {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω => (√c)⁻¹ * B (c * t) ω) P :=
  hB.smul hc
-- @endregion

-- @region stochastic_processes.brownian_time_inversion
-- @provenance library
/-- **Time inversion.** If `B` is a pre-Brownian motion, so is `t ↦ t B_{1/t}`. It converts
statements about `t → ∞` into statements about `t → 0`. This is Mathlib's
`IsPreBrownianReal.inv`. -/
theorem brownian_time_inversion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω => t * B (1 / t) ω) P :=
  hB.inv
-- @endregion

/-! ### Geometric Brownian motion -/

-- @region stochastic_processes.gbm
-- @provenance definition
/-- The candidate solution of `dS = μ S dt + σ S dB`, written as a function of time `t` and of
the value `x = B_t` of the driving Brownian motion: `f(t, x) = S₀ exp((μ − σ²/2) t + σ x)`. -/
noncomputable def gbm (S₀ μ σ t x : ℝ) : ℝ :=
  S₀ * Real.exp ((μ - σ ^ 2 / 2) * t + σ * x)
-- @endregion

-- @region stochastic_processes.gbm_ito
-- @provenance independent
/-- **The calculus behind geometric Brownian motion.** For `f = gbm S₀ μ σ`:
`∂ₓf = σ f`, `∂ₓₓf = σ² f`, `∂ₜf = (μ − σ²/2) f`, and hence `∂ₜf + ½ ∂ₓₓf = μ f`.
Itô's formula `df(t, B_t) = (∂ₜf + ½ ∂ₓₓf) dt + ∂ₓf dB_t` then gives
`dS_t = μ S_t dt + σ S_t dB_t` for `S_t = f(t, B_t)`: the `−σ²/2` in the exponent is exactly
cancelled by Itô's correction term `½ ∂ₓₓf`. (Itô's formula itself is not in Mathlib; this
theorem verifies the derivatives it needs.) -/
theorem gbm_ito (S₀ μ σ t x : ℝ) :
    HasDerivAt (fun y => gbm S₀ μ σ t y) (σ * gbm S₀ μ σ t x) x ∧
    HasDerivAt (fun y => σ * gbm S₀ μ σ t y) (σ ^ 2 * gbm S₀ μ σ t x) x ∧
    HasDerivAt (fun s => gbm S₀ μ σ s x) ((μ - σ ^ 2 / 2) * gbm S₀ μ σ t x) t ∧
    (μ - σ ^ 2 / 2) * gbm S₀ μ σ t x + σ ^ 2 * gbm S₀ μ σ t x / 2 = μ * gbm S₀ μ σ t x := by
  -- derivative in the space variable
  have hx : HasDerivAt (fun y => gbm S₀ μ σ t y) (σ * gbm S₀ μ σ t x) x := by
    have h := (((hasDerivAt_id x).const_mul σ).const_add ((μ - σ ^ 2 / 2) * t)).exp.const_mul S₀
    convert h using 1
    · simp only [gbm, id]
    · simp only [gbm, id]
      ring
  refine ⟨hx, ?_, ?_, by ring⟩
  · convert hx.const_mul σ using 1
    ring
  · have h := ((((hasDerivAt_id t).const_mul (μ - σ ^ 2 / 2)).add_const (σ * x)).exp).const_mul S₀
    convert h using 1
    · simp only [gbm, id]
    · simp only [gbm, id]
      ring
-- @endregion

end Lumenary.StochasticProcesses
