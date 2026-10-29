/-
The Lumenary — formal mathematics
Introductory calculus: limits, the derivative as a limit of difference quotients, the power
rule, critical points, Riemann sums and the fundamental theorem of calculus.

Proved here (`@provenance independent`): the difference quotient of `x²` and its limit `2a`,
hence `(x²)′ = 2x` straight from the definition; the power rule `(xⁿ⁺¹)′ = (n + 1)xⁿ` by
induction with the product rule; that `x³` has derivative `0` at `0` but no maximum or minimum
there; that `(x² − 1)/(x − 1) → 2` as `x → 1` although the function has no meaningful value at
`1`; and that the right Riemann sums of `x²` on `[0, 1]` equal `(n + 1)(2n + 1)/(6n²)` and tend
to `1/3` (Archimedes' area of the parabolic segment, in modern form).

From Mathlib (`@provenance library`): `hasDerivAt_pow`, Fermat's theorem on interior extrema
(`IsLocalExtr.hasDerivAt_eq_zero`), the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`), `integral_pow` and `integral_sin`.

Note: Mathlib's `HasDerivAt f f' a` means "`f` is differentiable at `a` with derivative `f'`",
and `𝓝[≠] 0` is "`h` tends to `0` with `h ≠ 0`". Lean defines `x / 0 = 0`, which matters below.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace Lumenary.IntroCalculus

open Filter Topology Finset

/-! ### The derivative of x² from the definition -/

-- @region intro_calculus.diff_quotient_sq
-- @provenance independent
/-- **The difference quotient of `x²`.** For `h ≠ 0`,
`((a + h)² − a²)/h = (2ah + h²)/h = 2a + h`. -/
theorem diff_quotient_sq (a h : ℝ) (hh : h ≠ 0) : ((a + h) ^ 2 - a ^ 2) / h = 2 * a + h := by
  field_simp
  ring
-- @endregion

-- @region intro_calculus.tendsto_diff_quotient_sq
-- @provenance independent
/-- **Its limit is `2a`.** As `h → 0` with `h ≠ 0`, the quotient equals `2a + h`, and
`2a + h → 2a`. The value at `h = 0` itself is never used. -/
theorem tendsto_diff_quotient_sq (a : ℝ) :
    Tendsto (fun h => ((a + h) ^ 2 - a ^ 2) / h) (𝓝[≠] 0) (𝓝 (2 * a)) := by
  have hlin : Tendsto (fun h : ℝ => 2 * a + h) (𝓝[≠] 0) (𝓝 (2 * a)) := by
    have : Tendsto (fun h : ℝ => 2 * a + h) (𝓝 0) (𝓝 (2 * a + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine tendsto_nhdsWithin_congr (fun h hh => ?_) hlin
  exact (diff_quotient_sq a h hh).symm
-- @endregion

-- @region intro_calculus.has_deriv_at_sq
-- @provenance independent
/-- **`(x²)′ = 2a` at every point `a`**, from the limit definition: Mathlib's `HasDerivAt` is
equivalent (`hasDerivAt_iff_tendsto_slope_zero`) to the difference quotients tending to the
derivative, and we computed that limit above. -/
theorem hasDerivAt_sq (a : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * a) a := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (tendsto_diff_quotient_sq a).congr (fun t => ?_)
  simp [smul_eq_mul, div_eq_inv_mul]
-- @endregion

/-! ### The power rule -/

-- @region intro_calculus.power_rule
-- @provenance independent
/-- **The power rule** `(xⁿ⁺¹)′ = (n + 1) xⁿ`, by induction on `n`.
For `n = 0`, `(x¹)′ = 1`. For the step write `x^(n+2) = x^(n+1) · x` and use the product rule
`(uv)′ = u′v + uv′`: the derivative is `(n + 1)xⁿ · x + x^(n+1) · 1 = (n + 2) x^(n+1)`.
(We write the exponent as `n + 1` so that the rule never needs `n − 1`.) -/
theorem power_rule (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (n + 1)) ((n + 1) * x ^ n) x := by
  induction n with
  | zero => simpa using hasDerivAt_id' x
  | succ k ih =>
    have h := ih.mul (hasDerivAt_id x)
    have hf : (fun y : ℝ => y ^ (k + 1 + 1)) = (fun y : ℝ => y ^ (k + 1)) * id := by
      funext y
      simp [pow_succ]
    rw [hf]
    convert h using 1
    push_cast
    simp only [id]
    ring
-- @endregion

-- @region intro_calculus.power_rule_library
-- @provenance library
/-- The power rule from Mathlib, `hasDerivAt_pow`: `(xⁿ)′ = n xⁿ⁻¹` (with natural-number
subtraction, so for `n = 0` it reads `(x⁰)′ = 0 · x^0 = 0`, which is still correct). -/
theorem power_rule_library (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ n) (n * x ^ (n - 1)) x :=
  hasDerivAt_pow n x
-- @endregion

/-! ### Critical points -/

-- @region intro_calculus.fermat
-- @provenance library
/-- **Fermat's theorem on interior extrema:** if `f` has a local maximum or minimum at `a` and is
differentiable there, then `f′(a) = 0`. This applies Mathlib's
`IsLocalExtr.hasDerivAt_eq_zero`. -/
theorem fermat {f : ℝ → ℝ} {a f' : ℝ} (hext : IsLocalExtr f a) (hd : HasDerivAt f f' a) :
    f' = 0 :=
  hext.hasDerivAt_eq_zero hd
-- @endregion

-- @region intro_calculus.cube_deriv_zero
-- @provenance independent
/-- `x³` has derivative `3 · 0² = 0` at `0` (the power rule with `n = 2`). -/
theorem cube_deriv_zero : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
  have h := power_rule 2 0
  norm_num at h
  exact h
-- @endregion

-- @region intro_calculus.cube_not_extremum
-- @provenance independent
/-- **The converse of Fermat's theorem is false.** `x³` has `f′(0) = 0`, but `0` is neither a
local maximum nor a local minimum: however small an interval around `0` we take, it contains a
point `t > 0` with `t³ > 0 = f(0)` and the point `−t` with `(−t)³ < 0`. -/
theorem cube_not_extremum : ¬ IsLocalExtr (fun x : ℝ => x ^ 3) 0 := by
  rintro (hmin | hmax)
  · -- A local minimum would need `x³ ≥ 0` near `0`; `x = −ε/2` breaks it.
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hmin
    have hd : dist (-(ε / 2)) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]
      linarith
    have := h hd
    simp only at this
    nlinarith [pow_pos (half_pos hε) 3]
  · -- A local maximum would need `x³ ≤ 0` near `0`; `x = ε/2` breaks it.
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hmax
    have hd : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    have := h hd
    simp only at this
    nlinarith [pow_pos (half_pos hε) 3]
-- @endregion

/-! ### A limit is not a value -/

-- @region intro_calculus.limit_not_value
-- @provenance independent
/-- **The limit at a point need not be the value there.** `f(x) = (x² − 1)/(x − 1)` tends to `2`
as `x → 1`, because `f(x) = x + 1` for `x ≠ 1`. At `x = 1` the formula reads `0/0`, which is
meaningless on paper; Lean's convention `0/0 = 0` gives `f(1) = 0` — a value that has nothing to
do with the limit `2`. -/
theorem limit_not_value :
    Tendsto (fun x : ℝ => (x ^ 2 - 1) / (x - 1)) (𝓝[≠] 1) (𝓝 2) ∧
      (fun x : ℝ => (x ^ 2 - 1) / (x - 1)) 1 = 0 := by
  constructor
  · have hlin : Tendsto (fun x : ℝ => x + 1) (𝓝[≠] 1) (𝓝 2) := by
      have : Tendsto (fun x : ℝ => x + 1) (𝓝 1) (𝓝 (1 + 1)) :=
        tendsto_id.add tendsto_const_nhds
      norm_num at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine tendsto_nhdsWithin_congr (fun x hx => ?_) hlin
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  · norm_num
-- @endregion

/-! ### Riemann sums and the area under a parabola -/

-- @region intro_calculus.sum_squares
-- @provenance independent
/-- `0² + 1² + ⋯ + n² = n(n + 1)(2n + 1)/6`, by induction on `n`. -/
theorem sum_squares (n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
-- @endregion

-- @region intro_calculus.right_sum
-- @provenance definition
/-- The **right Riemann sum** of `f(x) = x²` on `[0, 1]` with `n` strips of width `1/n`: the
strip over `[k/n, (k + 1)/n]` has height `f((k + 1)/n)`. -/
noncomputable def rightSum (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (((k : ℝ) + 1) / n) ^ 2 * (1 / n)
-- @endregion

-- @region intro_calculus.right_sum_formula
-- @provenance independent
/-- **A closed form for the Riemann sum:** for `n ≥ 1`,
`rightSum n = (1² + 2² + ⋯ + n²)/n³ = (n + 1)(2n + 1)/(6n²)`. -/
theorem rightSum_formula (n : ℕ) (hn : n ≠ 0) :
    rightSum n = ((n : ℝ) + 1) * (2 * n + 1) / (6 * (n : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : ∑ k ∈ range n, ((k : ℝ) + 1) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
    have h := sum_squares n
    rw [sum_range_succ'] at h
    simpa using h
  have hsum : rightSum n = (∑ k ∈ range n, ((k : ℝ) + 1) ^ 2) / (n : ℝ) ^ 3 := by
    rw [rightSum, sum_div]
    refine sum_congr rfl (fun k _ => ?_)
    field_simp
  rw [hsum, key]
  field_simp
-- @endregion

-- @region intro_calculus.right_sum_tendsto
-- @provenance independent
/-- **The Riemann sums converge to `1/3`.** For `n ≥ 1`,
`(n + 1)(2n + 1)/(6n²) = (1 + 1/n)(2 + 1/n)/6`, and `1/n → 0`, so the limit is
`(1 · 2)/6 = 1/3`: the area under `y = x²` from `0` to `1`. -/
theorem rightSum_tendsto : Tendsto rightSum atTop (𝓝 (1 / 3)) := by
  have hlim : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) / 6) atTop
      (𝓝 ((1 + 0) * (2 + 0) / 6)) :=
    ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).mul
      (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat)).div_const 6
  norm_num at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [rightSum_formula n hn]
  field_simp
-- @endregion

/-! ### The fundamental theorem of calculus -/

-- @region intro_calculus.ftc_square
-- @provenance library
/-- **The fundamental theorem in action:** `∫₀² x² dx = 8/3`. Since `F(x) = x³/3` has
`F′(x) = x²`, the integral is `F(2) − F(0) = 8/3`. This applies Mathlib's fundamental theorem
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem ftc_square : ∫ x in (0 : ℝ)..2, x ^ 2 = 8 / 3 := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 2, HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
    intro x _
    have h := (hasDerivAt_pow 3 x).div_const 3
    convert h using 1
    norm_num
  have hint : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume 0 2 :=
    (continuous_pow 2).intervalIntegrable 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  norm_num
-- @endregion

-- @region intro_calculus.integral_sq_unit
-- @provenance library
/-- `∫₀¹ x² dx = 1/3`, the limit of the Riemann sums above, from Mathlib's `integral_pow`. -/
theorem integral_sq_unit : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  rw [integral_pow]
  norm_num
-- @endregion

-- @region intro_calculus.integral_sin_signed
-- @provenance library
/-- **Integrals are signed.** `∫₀^{2π} sin x dx = cos 0 − cos 2π = 0`: the area above the axis
on `[0, π]` cancels the area below it on `[π, 2π]`. This applies Mathlib's `integral_sin`. -/
theorem integral_sin_signed : ∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin x = 0 := by
  rw [integral_sin]
  simp
-- @endregion

end Lumenary.IntroCalculus
