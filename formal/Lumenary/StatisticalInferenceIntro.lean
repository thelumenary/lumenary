/-
The Lumenary — formal mathematics
Sampling and statistical reasoning: the algebra behind least squares, correlation and the
1/√n law.

Statistics is about data and chance, and most of it cannot be "proved" — whether a sample is
biased, or whether one variable causes another, are questions about the world. But the
*algebra* that statistical methods rest on can be proved, and that is what this file does.

Proved here (`@provenance independent`): the decomposition
`Σ (xᵢ − c)² = Σ (xᵢ − x̄)² + n (x̄ − c)²`, so the mean is the best single "prediction" in the
least-squares sense; the Cauchy–Schwarz inequality for finite sums, by the least-squares
argument; that the correlation coefficient always lies between −1 and 1; the decomposition of
the sum of squared residuals of any line, from which the least-squares line
`y = â + b̂x` with `b̂ = Sxy/Sxx` and `â = ȳ − b̂x̄` is the best line and its residual sum of
squares is `Syy − Sxy²/Sxx`.

From Mathlib (`@provenance library`): the Cauchy–Schwarz inequality
`Finset.sum_mul_sq_le_sq_mul_sq`, and the variance of a sample mean of independent
measurements, `σ²/n`, computed from `ProbabilityTheory.IndepFun.variance_sum` and
`ProbabilityTheory.variance_const_mul`.

Also from Mathlib (`@provenance library`): the central limit theorem,
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`.

Not formalised: anything about real samples — bias, randomisation, causation — and the coverage
of confidence intervals.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Lumenary.StatisticalInferenceIntro

open Finset

/-! ### The mean as a least-squares estimate -/

-- @region statistical_inference_intro.mean
-- @provenance definition
/-- The **mean** `x̄ = (x₁ + ⋯ + xₙ)/n` of `n` data values `x : Fin n → ℝ`. -/
noncomputable def mean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n
-- @endregion

-- @region statistical_inference_intro.sum_sub_mean
-- @provenance independent
/-- The deviations from the mean add up to zero: `Σ (xᵢ − x̄) = 0`. -/
theorem sum_sub_mean {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) : ∑ i, (x i - mean x) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  ring
-- @endregion

-- @region statistical_inference_intro.sum_sq_sub
-- @provenance independent
/-- **Spread about any point `c`:** `Σ (xᵢ − c)² = Σ (xᵢ − x̄)² + n (x̄ − c)²`. Write
`xᵢ − c = (xᵢ − x̄) + (x̄ − c)` and expand; the cross term is `2(x̄ − c) Σ (xᵢ − x̄) = 0`. -/
theorem sum_sq_sub {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - c) ^ 2 = ∑ i, (x i - mean x) ^ 2 + n * (mean x - c) ^ 2 := by
  have h0 := sum_sub_mean hn x
  calc ∑ i, (x i - c) ^ 2
      = ∑ i, ((x i - mean x) ^ 2 + 2 * (mean x - c) * (x i - mean x) + (mean x - c) ^ 2) :=
        sum_congr rfl fun i _ => by ring
    _ = ∑ i, (x i - mean x) ^ 2 + 2 * (mean x - c) * ∑ i, (x i - mean x) +
          n * (mean x - c) ^ 2 := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = ∑ i, (x i - mean x) ^ 2 + n * (mean x - c) ^ 2 := by rw [h0]; ring
-- @endregion

-- @region statistical_inference_intro.mean_minimizes
-- @provenance independent
/-- **The mean minimises the sum of squared deviations:** `Σ (xᵢ − x̄)² ≤ Σ (xᵢ − c)²` for
every number `c`, with the extra amount exactly `n (x̄ − c)²`. -/
theorem mean_minimizes {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - mean x) ^ 2 ≤ ∑ i, (x i - c) ^ 2 := by
  rw [sum_sq_sub hn x c]
  have : 0 ≤ (n : ℝ) * (mean x - c) ^ 2 := by positivity
  linarith
-- @endregion

/-! ### Cauchy–Schwarz and the correlation coefficient -/

-- @region statistical_inference_intro.cauchy_schwarz
-- @provenance independent
/-- **The Cauchy–Schwarz inequality** `(Σ fᵢgᵢ)² ≤ (Σ fᵢ²)(Σ gᵢ²)`, by least squares.
If `Σ gᵢ² = 0`, every `gᵢ` is `0` and both sides vanish. Otherwise, for every `t`,
`0 ≤ Σ (fᵢ − t gᵢ)² = Σ fᵢ² − 2t Σ fᵢgᵢ + t² Σ gᵢ²`; the best choice `t = Σ fᵢgᵢ / Σ gᵢ²` gives
`0 ≤ Σ fᵢ² − (Σ fᵢgᵢ)² / Σ gᵢ²`. -/
theorem cauchy_schwarz {n : ℕ} (f g : Fin n → ℝ) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * ∑ i, g i ^ 2 := by
  set A := ∑ i, f i ^ 2
  set B := ∑ i, f i * g i
  set C := ∑ i, g i ^ 2
  have hC : 0 ≤ C := sum_nonneg fun i _ => sq_nonneg (g i)
  -- the sum of squares `Σ (fᵢ − t gᵢ)²`, expanded
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have h : ∑ i, (f i - t * g i) ^ 2 = A - 2 * t * B + t ^ 2 * C := by
      simp only [A, B, C, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [← h]
    exact sum_nonneg fun i _ => sq_nonneg _
  rcases hC.eq_or_lt with hC0 | hCpos
  · -- every `gᵢ = 0`, so `B = 0`
    have hg : ∀ i, g i = 0 := by
      intro i
      have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (g j)).1 hC0.symm i (mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hB : B = 0 := sum_eq_zero fun i _ => by rw [hg i, mul_zero]
    rw [hB, ← hC0]
    simp
  · -- the best `t`
    have h := key (B / C)
    have h' : 0 ≤ A * C - B ^ 2 := by
      have e : A - 2 * (B / C) * B + (B / C) ^ 2 * C = (A * C - B ^ 2) / C := by
        field_simp
        ring
      rw [e] at h
      exact (div_nonneg_iff.1 h).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hCpos)
    linarith
-- @endregion

-- @region statistical_inference_intro.cauchy_schwarz_library
-- @provenance library
/-- The same inequality from Mathlib: `Finset.sum_mul_sq_le_sq_mul_sq`. -/
theorem cauchy_schwarz_library {n : ℕ} (f g : Fin n → ℝ) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * ∑ i, g i ^ 2 :=
  sum_mul_sq_le_sq_mul_sq univ f g
-- @endregion

-- @region statistical_inference_intro.sxy
-- @provenance definition
/-- The **sum of products of deviations** `Sxy = Σ (xᵢ − x̄)(yᵢ − ȳ)`. With `y = x` it is
`Sxx = Σ (xᵢ − x̄)²`, which measures the spread of the `x`-values. -/
noncomputable def Sxy {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, (x i - mean x) * (y i - mean y)
-- @endregion

-- @region statistical_inference_intro.corr
-- @provenance definition
/-- The **correlation coefficient** `r = Sxy / √(Sxx · Syy)`. (If all the `x`-values or all the
`y`-values are equal, `r` is undefined; Lean's convention `a / 0 = 0` then gives `0`.) -/
noncomputable def corr {n : ℕ} (x y : Fin n → ℝ) : ℝ := Sxy x y / Real.sqrt (Sxy x x * Sxy y y)
-- @endregion

-- @region statistical_inference_intro.abs_corr_le_one
-- @provenance independent
/-- **The correlation coefficient lies between −1 and 1.** Apply Cauchy–Schwarz to the
deviations `fᵢ = xᵢ − x̄` and `gᵢ = yᵢ − ȳ`: `Sxy² ≤ Sxx · Syy`, so `|Sxy| ≤ √(Sxx · Syy)`. -/
theorem abs_corr_le_one {n : ℕ} (x y : Fin n → ℝ) : |corr x y| ≤ 1 := by
  have hcs : Sxy x y ^ 2 ≤ Sxy x x * Sxy y y := by
    have := cauchy_schwarz (fun i => x i - mean x) (fun i => y i - mean y)
    simpa [Sxy, sq] using this
  have habs : |Sxy x y| ≤ Real.sqrt (Sxy x x * Sxy y y) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  rw [corr, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases (Real.sqrt_nonneg (Sxy x x * Sxy y y)).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact zero_le_one
  · exact (div_le_one hpos).2 habs
-- @endregion

/-! ### The least-squares line -/

-- @region statistical_inference_intro.sse
-- @provenance definition
/-- The **sum of squared residuals** of the line `y = a + b x`: the residual of the `i`-th
point is the vertical distance `yᵢ − (a + b xᵢ)`. -/
noncomputable def sse {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) : ℝ := ∑ i, (y i - (a + b * x i)) ^ 2
-- @endregion

-- @region statistical_inference_intro.sse_eq
-- @provenance independent
/-- **Where the residuals of a line come from.** If the `x`-values are not all equal
(`Sxx ≠ 0`), then for every line `y = a + bx`,
`SSE(a, b) = Sxx (b − Sxy/Sxx)² + n (ȳ − a − b x̄)² + (Syy − Sxy²/Sxx)`.
Proof: centre the data. With `Xᵢ = xᵢ − x̄` and `Yᵢ = yᵢ − ȳ`, each residual is
`(Yᵢ − b Xᵢ) + (ȳ − a − b x̄)`; the cross terms vanish because `Σ Xᵢ = Σ Yᵢ = 0`; and
`Σ (Yᵢ − bXᵢ)² = Syy − 2b Sxy + b² Sxx` is a quadratic in `b`, completed to a square. -/
theorem sse_eq {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (hx : Sxy x x ≠ 0) (a b : ℝ) :
    sse x y a b = Sxy x x * (b - Sxy x y / Sxy x x) ^ 2 + n * (mean y - a - b * mean x) ^ 2 +
      (Sxy y y - Sxy x y ^ 2 / Sxy x x) := by
  -- centre the data
  set X : Fin n → ℝ := fun i => x i - mean x with hXdef
  set Y : Fin n → ℝ := fun i => y i - mean y with hYdef
  set d := mean y - a - b * mean x with hd
  have hX : ∑ i, X i = 0 := sum_sub_mean hn x
  have hY : ∑ i, Y i = 0 := sum_sub_mean hn y
  have hxx : Sxy x x = ∑ i, X i * X i := rfl
  have hxy : Sxy x y = ∑ i, X i * Y i := rfl
  have hyy : Sxy y y = ∑ i, Y i * Y i := rfl
  -- each residual is `(Yᵢ − b Xᵢ) + d`; expand its square
  have expand : sse x y a b = ∑ i, (Y i * Y i - 2 * b * (X i * Y i) + b ^ 2 * (X i * X i) +
      2 * d * Y i - 2 * d * b * X i + d ^ 2) :=
    sum_congr rfl fun i _ => by simp only [X, Y, d]; ring
  rw [expand]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [hX, hY, ← hxx, ← hxy, ← hyy]
  field_simp
  ring
-- @endregion

-- @region statistical_inference_intro.slope
-- @provenance definition
/-- The **least-squares slope** `b̂ = Sxy / Sxx`. -/
noncomputable def slope {n : ℕ} (x y : Fin n → ℝ) : ℝ := Sxy x y / Sxy x x
-- @endregion

-- @region statistical_inference_intro.intercept
-- @provenance definition
/-- The **least-squares intercept** `â = ȳ − b̂ x̄`, so that the line passes through the point
of means `(x̄, ȳ)`. -/
noncomputable def intercept {n : ℕ} (x y : Fin n → ℝ) : ℝ := mean y - slope x y * mean x
-- @endregion

-- @region statistical_inference_intro.least_squares
-- @provenance independent
/-- **The least-squares line is the best line:** no line `y = a + bx` has a smaller sum of
squared residuals than `y = â + b̂x`. By `sse_eq`, `SSE(a, b)` is a fixed amount plus two
squares (`Sxx > 0` as a sum of squares that is not zero), and both squares vanish at `(â, b̂)`. -/
theorem least_squares {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (hx : Sxy x x ≠ 0) (a b : ℝ) :
    sse x y (intercept x y) (slope x y) ≤ sse x y a b := by
  have hxx : 0 ≤ Sxy x x := sum_nonneg fun i _ => mul_self_nonneg _
  rw [sse_eq hn x y hx, sse_eq hn x y hx]
  have h1 : slope x y - Sxy x y / Sxy x x = 0 := by rw [slope]; ring
  have h2 : mean y - intercept x y - slope x y * mean x = 0 := by rw [intercept]; ring
  rw [h1, h2]
  have : 0 ≤ Sxy x x * (b - Sxy x y / Sxy x x) ^ 2 := by positivity
  have : 0 ≤ (n : ℝ) * (mean y - a - b * mean x) ^ 2 := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
  linarith
-- @endregion

-- @region statistical_inference_intro.min_sse
-- @provenance independent
/-- **What is left over.** The least-squares line leaves the residual sum of squares
`Syy − Sxy²/Sxx = Syy (1 − r²)`. Since it cannot be negative, this gives a second proof that
`r² ≤ 1`, and it is `0` exactly when the points lie on a line. -/
theorem min_sse {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (hx : Sxy x x ≠ 0) :
    sse x y (intercept x y) (slope x y) = Sxy y y - Sxy x y ^ 2 / Sxy x x := by
  rw [sse_eq hn x y hx]
  have h1 : slope x y - Sxy x y / Sxy x x = 0 := by rw [slope]; ring
  have h2 : mean y - intercept x y - slope x y * mean x = 0 := by rw [intercept]; ring
  rw [h1, h2]
  ring
-- @endregion

/-! ### Why larger samples vary less -/

open MeasureTheory ProbabilityTheory
-- @region statistical_inference_intro.variance_sample_mean
-- @provenance library
/-- **The variance of a sample mean is `σ²/n`.** If `X₁, …, Xₙ` are pairwise independent
measurements, each with finite variance `σ²`, then their mean `(X₁ + ⋯ + Xₙ)/n` has variance
`σ²/n`, so its standard deviation is `σ/√n`: four times the sample, half the spread. The proof
applies Mathlib's `ProbabilityTheory.IndepFun.variance_sum` (variances of independent variables
add) and `ProbabilityTheory.variance_const_mul` (`Var(cX) = c² Var(X)`). -/
theorem variance_sample_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (hn : 0 < n) (X : Fin n → Ω → ℝ) (σ : ℝ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hind : Set.Pairwise (univ : Finset (Fin n)) fun i j => X i ⟂ᵢ[μ] X j)
    (hvar : ∀ i, variance (X i) μ = σ ^ 2) :
    variance (fun ω => (1 / n : ℝ) * ∑ i, X i ω) μ = σ ^ 2 / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [variance_const_mul]
  have hsum : variance (fun ω => ∑ i, X i ω) μ = ∑ i, variance (X i) μ := by
    have e : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
      ext ω
      rw [Finset.sum_apply]
    rw [e]
    exact IndepFun.variance_sum (s := univ) (fun i _ => hL2 i) hind
  rw [hsum, sum_congr rfl fun i _ => hvar i, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
-- @endregion

-- @region statistical_inference_intro.central_limit_theorem
-- @provenance library
/-- **The central limit theorem** (in dimension 1). If `X 0, X 1, X 2, …` are independent and
identically distributed, with mean `μ` and finite variance `σ²`, then
`(X 0 + ⋯ + X (n − 1) − n μ) / √n` converges in distribution, as `n → ∞`, to a normal random
variable `Y` with mean `0` and variance `σ²`. This is why sample means are approximately normal and
margins of error use `1.96`. It applies Mathlib's
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`. -/
theorem central_limit_theorem {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      Filter.atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident
-- @endregion

end Lumenary.StatisticalInferenceIntro
