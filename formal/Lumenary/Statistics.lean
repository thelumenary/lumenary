/-
The Lumenary — formal mathematics
Statistical inference: unbiased estimation (the sample mean and Bessel's correction), the
bias–variance decomposition of mean squared error, consistency, the Bernoulli maximum likelihood
estimator, least squares and the normal equations, and multiple testing.

Random variables, expectations (`μ[X]`) and variances (`Var[X; μ]`) are Mathlib's, as in the
probability theory lesson; data sets are functions `x : ι → ℝ` summed over a `Finset`.
Proved here from more basic facts (`@provenance independent`): the shift identity behind
Bessel's correction, the unbiasedness of the sample mean and of the sample variance with
`n − 1`, the variance `σ²/n` of the sample mean and a consistency bound, the decomposition
`MSE = variance + bias²`, the fact that `k/n` maximises the Bernoulli log-likelihood (with no
calculus: only `log x ≤ x − 1`), the normal equations of least squares in both directions, and
the Bonferroni correction. Cited from Mathlib (`@provenance library`): the union bound and
Chebyshev's inequality.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Lumenary.Statistics

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### The sample mean and the shift identity -/

-- @region statistics.sample_mean
-- @provenance definition
/-- The **sample mean** `x̄ = (∑ᵢ xᵢ)/|s|` of the data `xᵢ`, `i ∈ s`. (For the empty data set
Lean's convention `a / 0 = 0` gives `0`.) -/
noncomputable def sampleMean {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℝ :=
  (∑ i ∈ s, x i) / s.card
-- @endregion

-- @region statistics.sum_eq_card_mul_mean
-- @provenance independent
/-- The total of the data is `n · x̄`. -/
theorem sum_eq_card_mul_mean {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∑ i ∈ s, x i = s.card * sampleMean s x := by
  unfold sampleMean
  rcases Nat.eq_zero_or_pos s.card with h | h
  · rw [Finset.card_eq_zero.mp h]
    simp
  · have : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
    field_simp
-- @endregion

-- @region statistics.sum_sq_dev_eq
-- @provenance independent
/-- **The shift identity.** For any number `c`,
`∑ (xᵢ − x̄)² = ∑ (xᵢ − c)² − n (x̄ − c)²`. In particular (taking `c` arbitrary) the sample
mean minimises `c ↦ ∑ (xᵢ − c)²`, and (taking `c = μ`) it is the key step in Bessel's
correction. Proof: expand `((xᵢ − c) − (x̄ − c))²` and use `∑ (xᵢ − c) = n (x̄ − c)`. -/
theorem sum_sq_dev_eq {ι : Type*} (s : Finset ι) (x : ι → ℝ) (c : ℝ) :
    ∑ i ∈ s, (x i - sampleMean s x) ^ 2 =
      ∑ i ∈ s, (x i - c) ^ 2 - s.card * (sampleMean s x - c) ^ 2 := by
  set m := sampleMean s x
  have hsum : ∑ i ∈ s, (x i - c) = s.card * (m - c) := by
    rw [sum_sub_distrib, sum_eq_card_mul_mean s x, sum_const, nsmul_eq_mul]
    ring
  have hpt : ∀ i ∈ s, (x i - m) ^ 2 = (x i - c) ^ 2 - 2 * (m - c) * (x i - c) + (m - c) ^ 2 := by
    intro i _
    ring
  rw [sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsum, sum_const,
    nsmul_eq_mul]
  ring
-- @endregion

/-! ### Unbiased estimators -/

section Sampling

variable {X : ℕ → Ω → ℝ} {m v : ℝ}

-- @region statistics.sample_mean_unbiased
-- @provenance independent
/-- **The sample mean is unbiased:** if each `Xᵢ` has mean `m`, then `E[X̄ₙ] = m` (`n ≥ 1`).
Only linearity of expectation is used — no independence. -/
theorem sample_mean_unbiased (hint : ∀ i, Integrable (X i) μ) (hmean : ∀ i, μ[X i] = m)
    {n : ℕ} (hn : 0 < n) : μ[fun ω => sampleMean (range n) (fun i => X i ω)] = m := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [sampleMean, card_range]
  rw [integral_div, integral_finsetSum _ fun i _ => hint i]
  simp only [hmean, sum_const, card_range, nsmul_eq_mul]
  field_simp
-- @endregion

-- @region statistics.variance_sample_mean
-- @provenance independent
/-- **The variance of the sample mean is `σ²/n`** for pairwise independent observations with
common variance `σ² = v`: variances of independent variables add (`IndepFun.variance_sum`),
and `Var(X/n) = Var(X)/n²`. -/
theorem variance_sample_mean (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hvar : ∀ i, Var[X i; μ] = v) (n : ℕ) :
    Var[fun ω => sampleMean (range n) (fun i => X i ω); μ] = v / n := by
  have h : (fun ω => sampleMean (range n) (fun i => X i ω)) =
      fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω := by
    funext ω
    simp [sampleMean, Finset.sum_apply, div_eq_inv_mul]
  rw [h, variance_const_mul,
    IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]
  simp only [hvar, sum_const, card_range, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
-- @endregion

-- @region statistics.sample_mean_mem_lp
-- @provenance independent
/-- The sample mean of finitely many observations with finite variance has finite variance. -/
theorem sample_mean_memLp [IsProbabilityMeasure μ] (hL2 : ∀ i, MemLp (X i) 2 μ) (n : ℕ) :
    MemLp (fun ω => sampleMean (range n) (fun i => X i ω)) 2 μ := by
  have hsum : MemLp (∑ i ∈ range n, X i) 2 μ := memLp_finsetSum' _ fun i _ => hL2 i
  have := hsum.const_mul ((n : ℝ)⁻¹)
  convert this using 1
  funext ω
  simp [sampleMean, Finset.sum_apply, div_eq_inv_mul]
-- @endregion

-- @region statistics.bessel
-- @provenance independent
/-- **Bessel's correction.** For pairwise independent observations with common mean `m` and
common variance `v`, and `n ≥ 1`, `E[∑ (Xᵢ − X̄)²] = (n − 1) v`. Hence the sample variance
`S² = ∑ (Xᵢ − X̄)²/(n − 1)` is an unbiased estimator of `v` (for `n ≥ 2`), while dividing by
`n` underestimates it on average. Proof, as in the lesson: by the shift identity with `c = m`,
`∑ (Xᵢ − X̄)² = ∑ (Xᵢ − m)² − n (X̄ − m)²`; the expectations are `n v` and `n · v/n`. -/
theorem bessel [IsProbabilityMeasure μ] (hL2 : ∀ i, MemLp (X i) 2 μ) (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m) (hvar : ∀ i, Var[X i; μ] = v) {n : ℕ} (hn : 0 < n) :
    ∫ ω, ∑ i ∈ range n, (X i ω - sampleMean (range n) (fun j => X j ω)) ^ 2 ∂μ =
      (n - 1) * v := by
  set Xbar : Ω → ℝ := fun ω => sampleMean (range n) (fun j => X j ω) with hXbar
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Pointwise, the shift identity with `c = m`.
  have hpt : (fun ω => ∑ i ∈ range n, (X i ω - Xbar ω) ^ 2) =
      fun ω => ∑ i ∈ range n, (X i ω - m) ^ 2 - n * (Xbar ω - m) ^ 2 := by
    funext ω
    rw [hXbar]
    simp only
    rw [sum_sq_dev_eq (range n) (fun j => X j ω) m, card_range]
  -- Integrability of the two pieces.
  have hint_i : ∀ i, Integrable (fun ω => (X i ω - m) ^ 2) μ := fun i =>
    ((hL2 i).sub (memLp_const m)).integrable_sq
  have hint_bar : Integrable (fun ω => (Xbar ω - m) ^ 2) μ :=
    ((sample_mean_memLp hL2 n).sub (memLp_const m)).integrable_sq
  -- Each `E[(Xᵢ − m)²] = v`, and `E[(X̄ − m)²] = Var X̄ = v/n`.
  have hEi : ∀ i, ∫ ω, (X i ω - m) ^ 2 ∂μ = v := by
    intro i
    rw [← hvar i, variance_eq_integral (hL2 i).aestronglyMeasurable.aemeasurable, hmean i]
  have hEbar : ∫ ω, (Xbar ω - m) ^ 2 ∂μ = v / n := by
    have hm : μ[Xbar] = m :=
      sample_mean_unbiased (fun i => (hL2 i).integrable one_le_two) hmean hn
    rw [← variance_sample_mean hL2 hindep hvar n, ← hXbar,
      variance_eq_integral (sample_mean_memLp hL2 n).aestronglyMeasurable.aemeasurable, hm]
  show ∫ ω, (fun ω => ∑ i ∈ range n, (X i ω - Xbar ω) ^ 2) ω ∂μ = (n - 1) * v
  rw [hpt, integral_sub (integrable_finsetSum _ fun i _ => hint_i i) (hint_bar.const_mul _),
    integral_finsetSum _ fun i _ => hint_i i, integral_const_mul, hEbar]
  simp only [hEi, sum_const, card_range, nsmul_eq_mul]
  field_simp
-- @endregion

-- @region statistics.sample_mean_consistent
-- @provenance independent
/-- **Consistency of the sample mean**, with a rate: `P(|X̄ₙ − m| ≥ ε) ≤ v / (n ε²)`. Proof:
Mathlib's Chebyshev inequality (`meas_ge_le_variance_div_sq`) applied to `X̄ₙ`, whose mean is
`m` and whose variance is `v/n`. As `n → ∞` the bound tends to `0`. -/
theorem sample_mean_consistent [IsProbabilityMeasure μ] (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j) (hmean : ∀ i, μ[X i] = m)
    (hvar : ∀ i, Var[X i; μ] = v) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |sampleMean (range n) (fun i => X i ω) - m|} ≤
      ENNReal.ofReal (v / (n * ε ^ 2)) := by
  have h := meas_ge_le_variance_div_sq (sample_mean_memLp hL2 n) hε
  rw [sample_mean_unbiased (fun i => (hL2 i).integrable one_le_two) hmean hn,
    variance_sample_mean hL2 hindep hvar n, div_div] at h
  exact h
-- @endregion

end Sampling

-- @region statistics.variance_computing_formula
-- @provenance library
/-- The computing formula `Var X = E[X²] − (E X)²`, for `X` with finite variance. This is
Mathlib's `ProbabilityTheory.variance_eq_sub`. -/
theorem variance_computing_formula [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2 :=
  variance_eq_sub hX
-- @endregion

-- @region statistics.mse_decomposition
-- @provenance independent
/-- **Mean squared error = variance + bias².** For an estimator `T` with finite variance and
a parameter value `θ`, `E[(T − θ)²] = Var T + (E T − θ)²`. Proof: write
`T − θ = (T − E T) + (E T − θ)`; the cross term has expectation `0`. -/
theorem mse_decomposition [IsProbabilityMeasure μ] {T : Ω → ℝ} (hT : MemLp T 2 μ) (θ : ℝ) :
    ∫ ω, (T ω - θ) ^ 2 ∂μ = Var[T; μ] + (μ[T] - θ) ^ 2 := by
  set a := μ[T]
  have hTi : Integrable T μ := hT.integrable one_le_two
  have hpt : (fun ω => (T ω - θ) ^ 2) =
      fun ω => (T ω - a) ^ 2 + (2 * (a - θ) * (T ω - a) + (a - θ) ^ 2) := by
    funext ω
    ring
  have h1 : Integrable (fun ω => (T ω - a) ^ 2) μ := (hT.sub (memLp_const a)).integrable_sq
  have h2 : Integrable (fun ω => 2 * (a - θ) * (T ω - a)) μ :=
    (hTi.sub (integrable_const a)).const_mul _
  have h3 : Integrable (fun ω => 2 * (a - θ) * (T ω - a) + (a - θ) ^ 2) μ :=
    h2.add (integrable_const _)
  rw [hpt, integral_add h1 h3, integral_add h2 (integrable_const _),
    integral_const_mul, integral_sub hTi (integrable_const a),
    variance_eq_integral hT.aestronglyMeasurable.aemeasurable]
  simp [a]
-- @endregion

/-! ### Maximum likelihood -/

-- @region statistics.bernoulli_mle
-- @provenance independent
/-- **The Bernoulli maximum likelihood estimator is `k/n`.** With `k` successes in `n`
independent trials (`0 < k < n`), the log-likelihood `ℓ(p) = k log p + (n − k) log(1 − p)` is
largest at `p̂ = k/n`. Proof without calculus, as in the lesson: with `q = k/n`,
`ℓ(p) − ℓ(q) = k log(p/q) + (n − k) log((1 − p)/(1 − q))
  ≤ k (p/q − 1) + (n − k)((1 − p)/(1 − q) − 1) = 0`, using `log x ≤ x − 1`
(Mathlib's `Real.log_le_sub_one_of_pos`). -/
theorem bernoulli_mle {n k : ℕ} (hk : 0 < k) (hkn : k < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    k * Real.log p + (n - k) * Real.log (1 - p) ≤
      k * Real.log (k / n) + (n - k) * Real.log (1 - k / n) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hnR : (0 : ℝ) < n := hkR.trans hknR
  set q : ℝ := k / n with hq
  have hq0 : 0 < q := div_pos hkR hnR
  have hq1 : q < 1 := (div_lt_one hnR).mpr hknR
  have h1 : Real.log p - Real.log q ≤ p / q - 1 := by
    rw [← Real.log_div hp0.ne' hq0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have h2 : Real.log (1 - p) - Real.log (1 - q) ≤ (1 - p) / (1 - q) - 1 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  have hzero : (k : ℝ) * (p / q - 1) + (n - k) * ((1 - p) / (1 - q) - 1) = 0 := by
    have hnk : (n : ℝ) - k ≠ 0 := by linarith
    rw [hq]
    field_simp
    ring
  have e1 := mul_le_mul_of_nonneg_left h1 hkR.le
  have e2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ n - k by linarith)
  linarith
-- @endregion

/-! ### Least squares -/

-- @region statistics.normal_equations_minimize
-- @provenance independent
/-- **Least squares via the normal equations.** If `b` satisfies `(XᵀX) b = Xᵀy`, then `b`
minimises the residual sum of squares `‖y − Xβ‖²` over all `β`. Proof (Pythagoras): with
`r = y − Xb` and `w = b − β`, `y − Xβ = r + Xw`, and the cross term `r · Xw = (Xᵀr) · w`
vanishes because `Xᵀr = Xᵀy − XᵀXb = 0`; so `‖y − Xβ‖² = ‖r‖² + ‖Xw‖² ≥ ‖r‖²`. -/
theorem normal_equations_minimize {n p : Type*} [Fintype n] [Fintype p] (X : Matrix n p ℝ)
    (y : n → ℝ) (b : p → ℝ) (hb : (Xᵀ * X) *ᵥ b = Xᵀ *ᵥ y) (β : p → ℝ) :
    (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b) ≤ (y - X *ᵥ β) ⬝ᵥ (y - X *ᵥ β) := by
  set r := y - X *ᵥ b
  set w := b - β
  have hr : Xᵀ *ᵥ r = 0 := by
    simp only [r, mulVec_sub, mulVec_mulVec, hb, sub_self]
  have hcross : r ⬝ᵥ (X *ᵥ w) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hr, zero_dotProduct]
  have hsplit : y - X *ᵥ β = r + X *ᵥ w := by
    simp only [r, w, mulVec_sub]
    abel
  have hsq : 0 ≤ (X *ᵥ w) ⬝ᵥ (X *ᵥ w) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [hsplit, add_dotProduct, dotProduct_add, dotProduct_add, hcross, dotProduct_comm (X *ᵥ w) r,
    hcross]
  linarith
-- @endregion

-- @region statistics.minimizer_normal_equations
-- @provenance independent
/-- **Conversely, every least-squares solution satisfies the normal equations.** If `b`
minimises `‖y − Xβ‖²`, then `(XᵀX) b = Xᵀy`. Proof: for each direction `w` and real `t`,
`‖y − X(b + tw)‖² = ‖r‖² − 2t (Xᵀr)·w + t² ‖Xw‖²` must be at least `‖r‖²`; a quadratic
`−2ta + t²c` with `c ≥ 0` that is never negative has `a = 0`. Taking `w = Xᵀr` gives
`‖Xᵀr‖² = 0`. -/
theorem minimizer_normal_equations {n p : Type*} [Fintype n] [Fintype p] (X : Matrix n p ℝ)
    (y : n → ℝ) (b : p → ℝ)
    (hmin : ∀ β, (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b) ≤ (y - X *ᵥ β) ⬝ᵥ (y - X *ᵥ β)) :
    (Xᵀ * X) *ᵥ b = Xᵀ *ᵥ y := by
  set r := y - X *ᵥ b
  set g := Xᵀ *ᵥ r
  -- Expand the residual sum of squares at `b + t g`.
  have hexp : ∀ t : ℝ, (y - X *ᵥ (b + t • g)) ⬝ᵥ (y - X *ᵥ (b + t • g)) =
      r ⬝ᵥ r - 2 * t * (g ⬝ᵥ g) + t ^ 2 * ((X *ᵥ g) ⬝ᵥ (X *ᵥ g)) := by
    intro t
    have hsplit : y - X *ᵥ (b + t • g) = r - t • (X *ᵥ g) := by
      simp only [r, mulVec_add, mulVec_smul]
      abel
    have hrg : r ⬝ᵥ (X *ᵥ g) = g ⬝ᵥ g := by
      rw [dotProduct_mulVec, ← mulVec_transpose]
    rw [hsplit]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hrg, dotProduct_comm (X *ᵥ g) r]
    ring
  set a := g ⬝ᵥ g
  set c := (X *ᵥ g) ⬝ᵥ (X *ᵥ g)
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  -- Choose `t = a/(c + 1)`: the quadratic becomes `−a²(c + 2)/(c + 1)² ≤ 0`, so `a = 0`.
  have key := hmin (b + (a / (c + 1)) • g)
  rw [hexp] at key
  have hc1 : 0 < c + 1 := by linarith
  have hq : -2 * (a / (c + 1)) * a + (a / (c + 1)) ^ 2 * c = -(a ^ 2 * (c + 2)) / (c + 1) ^ 2 := by
    field_simp
    ring
  have h0 : 0 ≤ -(a ^ 2 * (c + 2)) / (c + 1) ^ 2 := by
    rw [← hq]
    linarith
  have h0' : a ^ 2 * (c + 2) ≤ 0 := by
    by_contra hneg
    have hpos : 0 < a ^ 2 * (c + 2) := not_le.mp hneg
    have : -(a ^ 2 * (c + 2)) / (c + 1) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  have ha0 : a = 0 := by
    have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg a]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp ha2
  -- `g · g = 0` forces `g = 0`, i.e. `Xᵀ(y − Xb) = 0`.
  have hg : g = 0 := by
    funext i
    have hsum : ∑ j, g j * g j = 0 := ha0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (g j)).mp hsum i
      (Finset.mem_univ i)
    simpa using this
  have : Xᵀ *ᵥ y - (Xᵀ * X) *ᵥ b = 0 := by
    rw [← mulVec_mulVec, ← mulVec_sub]
    exact hg
  exact (sub_eq_zero.mp this).symm
-- @endregion

/-! ### Multiple testing -/

-- @region statistics.union_bound
-- @provenance library
/-- **The union bound** (Boole's inequality): `P(A₁ ∪ ⋯ ∪ Aₘ) ≤ P(A₁) + ⋯ + P(Aₘ)`, for any
events, dependent or not. This is Mathlib's `measureReal_biUnion_finset_le`. -/
theorem union_bound [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) (A : ι → Set Ω) :
    μ.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.real (A i) :=
  measureReal_biUnion_finset_le s A
-- @endregion

-- @region statistics.bonferroni
-- @provenance independent
/-- **The Bonferroni correction controls the family-wise error rate.** If each of `m` tests
has probability at most `α/m` of a false rejection (event `Aᵢ`), then the probability of at
least one false rejection is at most `α` — whatever the dependence between the tests.
Proof: the union bound, then `m · (α/m) = α`. -/
theorem bonferroni [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) (A : ι → Set Ω) {α : ℝ}
    (hα : 0 ≤ α) (h : ∀ i ∈ s, μ.real (A i) ≤ α / s.card) :
    μ.real (⋃ i ∈ s, A i) ≤ α := by
  calc μ.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.real (A i) := union_bound s A
    _ ≤ ∑ _i ∈ s, α / s.card := sum_le_sum h
    _ = s.card * (α / s.card) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ α := by
      rcases Nat.eq_zero_or_pos s.card with h0 | h0
      · rw [h0]
        simp [hα]
      · have : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
        rw [mul_div_cancel₀ α this]
-- @endregion

-- @region statistics.fwer_independent_le
-- @provenance independent
/-- For `m` **independent** tests each at level `α`, the family-wise error rate is exactly
`1 − (1 − α)ᵐ`, and this is at most `mα` — Bernoulli's inequality `(1 + a)ᵐ ≥ 1 + ma`
(Mathlib's `one_add_mul_le_pow`, valid for `a ≥ −2`) with `a = −α`; we only need `α ≤ 1`. So Bonferroni's union bound is close to exact
for independent tests with small `α`. -/
theorem fwer_independent_le {α : ℝ} (h1 : α ≤ 1) (m : ℕ) :
    1 - (1 - α) ^ m ≤ m * α := by
  have h := one_add_mul_le_pow (a := -α) (by linarith) m
  have : (1 + -α) = 1 - α := by ring
  rw [this] at h
  linarith
-- @endregion

-- @region statistics.twenty_tests
-- @provenance independent
/-- Twenty independent tests of true null hypotheses at level `0.05` produce at least one
"significant" result with probability `1 − 0.95²⁰ > 0.64`. Checked by exact arithmetic. -/
theorem twenty_tests : (1 : ℚ) - (95 / 100) ^ 20 > 64 / 100 := by
  norm_num
-- @endregion

end Lumenary.Statistics
