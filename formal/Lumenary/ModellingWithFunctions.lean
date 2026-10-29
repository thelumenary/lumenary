/-
The Lumenary — formal mathematics
Mathematical modelling with functions: recognising linear, quadratic and exponential models from
tables, fitting a line, doubling times, and two theorems about the limits of fitting data.

Proved here (`@provenance independent`): constant differences force a linear model, constant
second differences a quadratic one, and constant ratios an exponential one; two points with
different `x` determine exactly one line; for a fixed slope the least-squares intercept is
`mean(y) − m · mean(x)` (by an exact "sum of squares" identity); continuous growth at rate `r`
doubles in time `ln 2 / r`, and yearly compounding at rate `r` takes at least as long; and
infinitely many models fit the same data exactly yet take any value we like at a new point.

From Mathlib (`@provenance library`): a polynomial can be fitted exactly through any data with
distinct `x`-values (`Polynomial.exists_eval_eq_iff`, Lagrange interpolation), and
`Real.add_one_le_exp` (`x + 1 ≤ eˣ`).
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Lumenary.ModellingWithFunctions

open Real Finset

/-! ### Recognising a model from a table -/

-- @region modelling_with_functions.linear_of_const_diff
-- @provenance independent
/-- **Constant differences mean a linear model.** If a quantity measured at times
`0, 1, 2, …` always changes by the same amount `d`, then `u n = u 0 + n d`. Induction on `n`. -/
theorem linear_of_const_diff (u : ℕ → ℝ) (d : ℝ) (h : ∀ n, u (n + 1) - u n = d) (n : ℕ) :
    u n = u 0 + n * d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h n
    push_cast
    linarith
-- @endregion

-- @region modelling_with_functions.exponential_of_const_ratio
-- @provenance independent
/-- **Constant ratios mean an exponential model.** If each value is `b` times the one before,
then `u n = u 0 · bⁿ`. Induction on `n`. -/
theorem exponential_of_const_ratio (u : ℕ → ℝ) (b : ℝ) (h : ∀ n, u (n + 1) = b * u n) (n : ℕ) :
    u n = u 0 * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih, pow_succ]; ring
-- @endregion

-- @region modelling_with_functions.quadratic_of_const_second_diff
-- @provenance independent
/-- **Constant second differences mean a quadratic model.** If the differences of the
differences are always `c`, then `u n = u 0 + n (u 1 − u 0) + c · n(n − 1)/2`, a quadratic in `n`.
We prove the formula for `n` and `n + 1` together, by induction. -/
theorem quadratic_of_const_second_diff (u : ℕ → ℝ) (c : ℝ)
    (h : ∀ n, u (n + 2) - 2 * u (n + 1) + u n = c) (n : ℕ) :
    u n = u 0 + n * (u 1 - u 0) + c * (n * (n - 1) / 2) := by
  have key : ∀ n : ℕ, u n = u 0 + n * (u 1 - u 0) + c * (n * (n - 1) / 2) ∧
      u (n + 1) = u 0 + (n + 1) * (u 1 - u 0) + c * ((n + 1) * n / 2) := by
    intro n
    induction n with
    | zero => constructor <;> simp
    | succ n ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨by push_cast; linarith, ?_⟩
      have h2 := h n
      push_cast
      linear_combination h2 + 2 * h1 - h0
  exact (key n).1
-- @endregion

/-! ### Fitting lines -/

-- @region modelling_with_functions.line_through_two_points
-- @provenance independent
/-- **Two points with different `x` determine exactly one line** `y = m x + c`:
`m = (y₂ − y₁)/(x₂ − x₁)` and `c = y₁ − m x₁`. If two lines pass through both points, subtracting
gives `(m − m')(x₁ − x₂) = 0`, so `m = m'` and then `c = c'`. -/
theorem line_through_two_points {x₁ y₁ x₂ y₂ : ℝ} (hx : x₁ ≠ x₂) :
    ∃! p : ℝ × ℝ, p.1 * x₁ + p.2 = y₁ ∧ p.1 * x₂ + p.2 = y₂ := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine ⟨((y₂ - y₁) / (x₂ - x₁), y₁ - (y₂ - y₁) / (x₂ - x₁) * x₁), ⟨by ring, ?_⟩, ?_⟩
  · field_simp
    ring
  · rintro ⟨m, c⟩ ⟨h₁, h₂⟩
    have hm : m = (y₂ - y₁) / (x₂ - x₁) := by
      field_simp
      linear_combination h₂ - h₁
    simp only [Prod.mk.injEq]
    exact ⟨hm, by rw [← hm]; linarith⟩
-- @endregion

-- @region modelling_with_functions.least_squares_intercept
-- @provenance independent
/-- **The best intercept is set by the means.** For data `r₁, …, rₙ` (in a line fit,
`rᵢ = yᵢ − m xᵢ` for a chosen slope `m`) and any `c`,
`Σ (rᵢ − c)² = Σ (rᵢ − c̄)² + n (c − c̄)²`, where `c̄ = (Σ rᵢ)/n` is the mean.
So the sum of squared errors is smallest exactly at `c = c̄`, that is,
`c = mean(y) − m · mean(x)`. The proof expands the square; the cross term vanishes because
the deviations from the mean add up to zero. -/
theorem least_squares_intercept {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ) (c : ℝ) :
    ∑ i, (r i - c) ^ 2 =
      ∑ i, (r i - (∑ j, r j) / n) ^ 2 + n * (c - (∑ j, r j) / n) ^ 2 := by
  set cbar := (∑ j, r j) / n with hcbar
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  -- the deviations from the mean add up to zero
  have hdev : ∑ i, (r i - cbar) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hcbar]
    field_simp
    ring
  have hexpand : ∀ i, (r i - c) ^ 2 = (r i - cbar) ^ 2 + 2 * (cbar - c) * (r i - cbar) +
      (c - cbar) ^ 2 := fun i => by ring
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum, hdev, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
-- @endregion

-- @region modelling_with_functions.least_squares_min
-- @provenance independent
/-- **Corollary:** no intercept does better than the mean: `Σ (rᵢ − c̄)² ≤ Σ (rᵢ − c)²`. -/
theorem least_squares_min {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ) (c : ℝ) :
    ∑ i, (r i - (∑ j, r j) / n) ^ 2 ≤ ∑ i, (r i - c) ^ 2 := by
  rw [least_squares_intercept hn r c]
  have : 0 ≤ (n : ℝ) * (c - (∑ j, r j) / n) ^ 2 := by positivity
  linarith
-- @endregion

/-! ### Doubling times -/

-- @region modelling_with_functions.doubling_time
-- @provenance independent
/-- **Doubling time of continuous growth.** A quantity `A eʳᵗ` with `A > 0` and rate `r > 0`
doubles exactly when `t = ln 2 / r`: `A eʳᵗ = 2A ⇔ eʳᵗ = 2 ⇔ rt = ln 2`. At `r = 0.05` (5%) this
is about `13.9` time units: the "rule of 70" says `70/5 = 14`. -/
theorem doubling_time {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (t : ℝ) :
    A * exp (r * t) = 2 * A ↔ t = log 2 / r := by
  constructor
  · intro h
    have h1 : exp (r * t) = 2 := by
      have := mul_left_cancel₀ hA.ne' (h.trans (mul_comm 2 A))
      exact this
    have h2 : r * t = log 2 := by rw [← h1, log_exp]
    field_simp
    linarith
  · intro ht
    rw [ht, mul_div_cancel₀ _ hr.ne', exp_log (by norm_num)]
    ring
-- @endregion

-- @region modelling_with_functions.yearly_doubling_slower
-- @provenance independent
/-- **Yearly compounding doubles no faster than continuous growth at the same rate:**
`ln 2 / r ≤ ln 2 / ln(1 + r)` for `r > 0`. The key step is `ln(1 + r) ≤ r`, from Mathlib's
`Real.add_one_le_exp` (`1 + r ≤ eʳ`). -/
theorem yearly_doubling_slower {r : ℝ} (hr : 0 < r) : log 2 / r ≤ log 2 / log (1 + r) := by
  have hlog_pos : 0 < log (1 + r) := log_pos (by linarith)
  have hlog_le : log (1 + r) ≤ r := by
    have h := add_one_le_exp r
    calc log (1 + r) ≤ log (exp r) := log_le_log (by linarith) (by linarith)
      _ = r := log_exp r
  exact div_le_div_of_nonneg_left (log_nonneg (by norm_num)) hlog_pos hlog_le
-- @endregion

-- @region modelling_with_functions.add_one_le_exp_library
-- @provenance library
/-- `1 + x ≤ eˣ` for every real `x` (the tangent line at `0` lies below the graph). This applies
Mathlib's `Real.add_one_le_exp`. -/
theorem add_one_le_exp_library (x : ℝ) : x + 1 ≤ exp x :=
  add_one_le_exp x
-- @endregion

/-! ### What data cannot tell us -/

-- @region modelling_with_functions.perfect_fit_exists
-- @provenance library
/-- **A perfect fit is always available.** For any `n` data points `(xᵢ, yᵢ)` with distinct
`xᵢ`, some polynomial passes through all of them (Lagrange interpolation; its degree can be
taken below `n`). This applies Mathlib's `Polynomial.exists_eval_eq_iff`. So a model that fits
the data perfectly has not yet earned our trust. -/
theorem perfect_fit_exists {n : ℕ} (x y : Fin n → ℝ) (hx : Function.Injective x) :
    ∃ q : Polynomial ℝ, ∀ i, q.eval (x i) = y i :=
  (Polynomial.exists_eval_eq_iff x y).mpr fun i j hij => by rw [hx hij]
-- @endregion

-- @region modelling_with_functions.extrapolation_undetermined
-- @provenance independent
/-- **Data cannot decide extrapolation.** Let `f` be any model and `S` the finite set of
`x`-values where we have data. The models `f(x) + k · ∏_{s ∈ S} (x − s)` agree with `f` at every
data point, for every `k`. At a new point `x₀ ∉ S` the product is not zero, so by choosing `k`
we can make the model predict *any* value `v` there. -/
theorem extrapolation_undetermined (f : ℝ → ℝ) (S : Finset ℝ) {x₀ : ℝ} (hx₀ : x₀ ∉ S) (v : ℝ) :
    ∃ k : ℝ, (∀ x ∈ S, f x + k * ∏ s ∈ S, (x - s) = f x) ∧
      f x₀ + k * ∏ s ∈ S, (x₀ - s) = v := by
  have hprod : ∏ s ∈ S, (x₀ - s) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro s hs h
    exact hx₀ (sub_eq_zero.mp h ▸ hs)
  refine ⟨(v - f x₀) / ∏ s ∈ S, (x₀ - s), ?_, ?_⟩
  · intro x hx
    have : ∏ s ∈ S, (x - s) = 0 := Finset.prod_eq_zero hx (sub_self x)
    rw [this, mul_zero, add_zero]
  · field_simp
    ring
-- @endregion

end Lumenary.ModellingWithFunctions
