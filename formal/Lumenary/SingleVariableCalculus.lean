/-
The Lumenary — formal mathematics
Calculus of one variable: ε–δ continuity, the mean value theorem and its consequences, the
fundamental theorem of calculus, series, Taylor's theorem and a smooth function that is not
the sum of its Taylor series.

What is proved here and what Mathlib provides. Mathlib develops one-variable calculus in full
generality (`HasDerivAt`, `intervalIntegral`, `HasSum`, `taylorWithinEval`). The *independent*
declarations below re-prove lesson results from more basic library facts, mirroring the human
proofs: the ε–δ continuity of `x ↦ x²`, the mean value theorem from Rolle's theorem, "zero
derivative means constant" and "positive derivative means increasing" from the mean value
theorem, two integrals computed with the fundamental theorem, absolute convergence implies
convergence, and the flatness of `exp (-1/x)` at `0`. The *library* declarations cite Mathlib's
own versions of the chain rule, the mean value theorem, Taylor's theorem with Lagrange
remainder, the exponential series and the `p`-series test.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

namespace Lumenary.SingleVariableCalculus

open Set Filter Topology

/-! ### Limits and continuity -/

-- @region single_variable_calculus.continuous_at_iff_eps_delta
-- @provenance library
/-- Mathlib defines continuity with neighbourhood filters; for real functions this is exactly
the ε–δ definition of the lesson. This applies Mathlib's `Metric.continuousAt_iff` and
`Real.dist_eq` (the distance on `ℝ` is `|x - y|`). -/
theorem continuousAt_iff_eps_delta (f : ℝ → ℝ) (a : ℝ) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε := by
  simp only [Metric.continuousAt_iff, Real.dist_eq]
-- @endregion

-- @region single_variable_calculus.sq_eps_delta
-- @provenance independent
/-- The squaring function is continuous at every point, proved directly with ε and δ as in the
lesson: take `δ = min 1 (ε / (2|a| + 1))`. If `|x - a| < δ` then `|x + a| ≤ |x - a| + 2|a|
< 2|a| + 1`, so `|x² - a²| = |x - a| |x + a| < δ (2|a| + 1) ≤ ε`. -/
theorem sq_eps_delta (a ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |x ^ 2 - a ^ 2| < ε := by
  have hpos : 0 < 2 * |a| + 1 := by positivity
  refine ⟨min 1 (ε / (2 * |a| + 1)), lt_min one_pos (div_pos hε hpos), fun x hx => ?_⟩
  have h1 : |x - a| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - a| < ε / (2 * |a| + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hsum : |x + a| < 2 * |a| + 1 :=
    calc |x + a| = |(x - a) + 2 * a| := by ring_nf
      _ ≤ |x - a| + |2 * a| := abs_add_le _ _
      _ = |x - a| + 2 * |a| := by rw [abs_mul, abs_two]
      _ < 1 + 2 * |a| := by linarith
      _ = 2 * |a| + 1 := by ring
  calc |x ^ 2 - a ^ 2| = |x - a| * |x + a| := by rw [← abs_mul]; ring_nf
    _ ≤ |x - a| * (2 * |a| + 1) := by
        exact mul_le_mul_of_nonneg_left hsum.le (abs_nonneg _)
    _ < ε / (2 * |a| + 1) * (2 * |a| + 1) := by
        exact mul_lt_mul_of_pos_right h2 hpos
    _ = ε := div_mul_cancel₀ ε hpos.ne'
-- @endregion

/-! ### Derivatives and the mean value theorem -/

-- @region single_variable_calculus.chain_rule
-- @provenance library
/-- The chain rule: if `f` has derivative `f'` at `x` and `g` has derivative `g'` at `f x`,
then `g ∘ f` has derivative `g' · f'` at `x`. This applies Mathlib's `HasDerivAt.comp`. -/
theorem chain_rule {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' (f x)) : HasDerivAt (g ∘ f) (g' * f') x :=
  hg.comp x hf
-- @endregion

-- @region single_variable_calculus.mvt_from_rolle
-- @provenance independent
/-- **The mean value theorem**, derived from Rolle's theorem exactly as in the lesson. Tilt
the graph: `g x = f x - m (x - a)` with `m = (f b - f a)/(b - a)` has `g a = g b`, so Rolle's
theorem (Mathlib's `exists_hasDerivAt_eq_zero`) gives `c` with `g' c = f' c - m = 0`. -/
theorem mvt_from_rolle {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  set m := (f b - f a) / (b - a) with hm
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  -- The tilted function and its derivative.
  let g : ℝ → ℝ := fun x => f x - m * (x - a)
  have hgc : ContinuousOn g (Icc a b) :=
    hfc.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hgab : g a = g b := by
    simp only [g, sub_self, mul_zero, sub_zero, hm]
    field_simp
    ring
  have hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (f' x - m) x := by
    intro x hx
    have hlin : HasDerivAt (fun x => m * (x - a)) m x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul m
    exact (hff' x hx).sub hlin
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hgc hgab hgg'
  exact ⟨c, hc, sub_eq_zero.mp hc0⟩
-- @endregion

-- @region single_variable_calculus.mvt
-- @provenance library
/-- Mathlib's own **mean value theorem**, `exists_hasDerivAt_eq_slope`. Same statement as
`mvt_from_rolle`; Mathlib proves it from Cauchy's mean value theorem. -/
theorem mvt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hfc hff'
-- @endregion

-- @region single_variable_calculus.const_of_deriv_zero
-- @provenance independent
/-- A function on `ℝ` whose derivative is zero everywhere is constant. Proof from the mean
value theorem: for `x < y`, some `c` has `0 = f' c = (f y - f x)/(y - x)`, so `f y = f x`. -/
theorem const_of_deriv_zero {f : ℝ → ℝ} (hf : ∀ x, HasDerivAt f 0 x) (x y : ℝ) :
    f x = f y := by
  -- It suffices to treat `x < y`; the case `x = y` is trivial and `x > y` is symmetric.
  have key : ∀ u v : ℝ, u < v → f u = f v := by
    intro u v huv
    obtain ⟨c, -, hc⟩ := mvt_from_rolle (f' := fun _ => 0) huv
      (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    have : f v - f u = 0 := by
      have := hc.symm
      rwa [div_eq_zero_iff, or_iff_left hvu] at this
    linarith
  rcases lt_trichotomy x y with h | rfl | h
  · exact key x y h
  · rfl
  · exact (key y x h).symm
-- @endregion

-- @region single_variable_calculus.strict_mono_of_deriv_pos
-- @provenance independent
/-- A function whose derivative is positive everywhere is strictly increasing. Proof from the
mean value theorem: for `x < y`, `f y - f x = f'(c) (y - x)` with `f'(c) > 0` and `y - x > 0`. -/
theorem strictMono_of_deriv_pos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 < f' x) : StrictMono f := by
  intro x y hxy
  obtain ⟨c, -, hc⟩ := mvt_from_rolle hxy
    (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hdiff : f y - f x = f' c * (y - x) := by
    rw [hc]; field_simp
  have : 0 < f y - f x := by rw [hdiff]; exact mul_pos (hpos c) hyx
  linarith
-- @endregion

-- @region single_variable_calculus.lhopital
-- @provenance library
/-- **L'Hôpital's rule**, two-sided `0/0` form: if `f` and `g` have derivatives `f'`, `g'` near
`a`, `g'` does not vanish near `a`, `f, g → 0` at `a`, and `f'/g' → l`, then `f/g → l` as
`x → a` with `x ≠ a`. This applies Mathlib's `HasDerivAt.lhopital_zero_nhds`, which is proved
from Cauchy's mean value theorem as in the lesson. -/
theorem lhopital {f g f' g' : ℝ → ℝ} {a l : ℝ}
    (hff' : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x) (hgg' : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in 𝓝 a, g' x ≠ 0) (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝 a) (𝓝 l)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 l) :=
  HasDerivAt.lhopital_zero_nhds hff' hgg' hg' hfa hga hdiv
-- @endregion

/-! ### Integrals and the fundamental theorem of calculus -/

-- @region single_variable_calculus.ftc
-- @provenance library
/-- **Fundamental theorem of calculus** (evaluation form): if `F' = f` on `[a, b]` and `f` is
integrable there, then `∫ₐᵇ f = F b - F a`. This applies Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem ftc {F f : ℝ → ℝ} {a b : ℝ} (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hint : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
-- @endregion

-- @region single_variable_calculus.integral_sq
-- @provenance independent
/-- `∫₀¹ x² dx = 1/3`, computed with the fundamental theorem and the antiderivative `x³/3`. -/
theorem integral_sq : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  have hF : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 3 / 3) (x ^ 2) x := by
    intro x _
    have := (hasDerivAt_pow 3 x).div_const 3
    convert this using 1
    push_cast
    ring
  rw [ftc hF ((continuous_pow 2).intervalIntegrable 0 1)]
  norm_num
-- @endregion

-- @region single_variable_calculus.integral_x_exp
-- @provenance independent
/-- `∫₀¹ x eˣ dx = 1`. Integration by parts *finds* the antiderivative `(x - 1) eˣ`; the
fundamental theorem then *checks* it: `((x - 1) eˣ)' = eˣ + (x - 1) eˣ = x eˣ`. -/
theorem integral_x_exp : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  have hF : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => (x - 1) * Real.exp x) (x * Real.exp x) x := by
    intro x _
    have := ((hasDerivAt_id' x).sub_const 1).mul (Real.hasDerivAt_exp x)
    convert this using 1
    ring
  have hcont : Continuous fun x : ℝ => x * Real.exp x := by fun_prop
  rw [ftc hF (hcont.intervalIntegrable 0 1)]
  simp
-- @endregion

/-! ### Series -/

-- @region single_variable_calculus.summable_of_abs
-- @provenance independent
/-- **An absolutely convergent series converges.** The lesson's proof: `0 ≤ aₙ + |aₙ| ≤ 2|aₙ|`,
so `∑ (aₙ + |aₙ|)` converges by comparison, and `aₙ = (aₙ + |aₙ|) - |aₙ|` is a difference of two
convergent series. (Mathlib states the general fact as `Summable.of_norm`.) -/
theorem summable_of_abs {a : ℕ → ℝ} (h : Summable fun n => |a n|) : Summable a := by
  have hsum : Summable fun n => a n + |a n| := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (h.mul_left 2)
    · linarith [neg_abs_le (a n)]
    · linarith [le_abs_self (a n)]
  have : a = fun n => (a n + |a n|) - |a n| := by
    funext n; ring
  rw [this]
  exact hsum.sub h
-- @endregion

-- @region single_variable_calculus.partial_sums_converge_of_abs
-- @provenance independent
/-- The same theorem in the lesson's language of partial sums: if `∑ |aₙ|` converges, then the
partial sums `a₀ + ⋯ + a_{N-1}` converge to a limit. (In Mathlib, `Summable` means
*unconditional* convergence, which for real series is the same as absolute convergence; so
`Summable` gives convergent partial sums, via `HasSum.tendsto_sum_nat`, but a conditionally
convergent series such as `∑ (-1)ⁿ/(n+1)` is *not* `Summable`.) -/
theorem partial_sums_converge_of_abs {a : ℕ → ℝ} (h : Summable fun n => |a n|) :
    ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) :=
  ⟨_, (summable_of_abs h).hasSum.tendsto_sum_nat⟩
-- @endregion

-- @region single_variable_calculus.p_series
-- @provenance library
/-- The `p`-series test: `∑ 1/nᵖ` converges if and only if `p > 1`. This applies Mathlib's
`Real.summable_one_div_nat_rpow` (proved there with Cauchy condensation). -/
theorem p_series (p : ℝ) : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  Real.summable_one_div_nat_rpow
-- @endregion

/-! ### Taylor's theorem and the exponential series -/

-- @region single_variable_calculus.taylor_lagrange
-- @provenance library
/-- **Taylor's theorem with Lagrange remainder.** If `f` is `n` times continuously
differentiable on the closed interval between `x₀` and `x`, and its `n`-th derivative is
differentiable inside, then `f x - Pₙ(x) = f⁽ⁿ⁺¹⁾(ξ) (x - x₀)ⁿ⁺¹/(n+1)!` for some `ξ` strictly
between. This applies Mathlib's `taylor_mean_remainder_lagrange`. (Mathlib's derivatives here
are taken *within* the interval, which agrees with the ordinary ones for smooth `f`.) -/
theorem taylor_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ ξ ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) ξ * (x - x₀) ^ (n + 1) / (n + 1).factorial :=
  taylor_mean_remainder_lagrange hx hf hf'
-- @endregion

-- @region single_variable_calculus.exp_series
-- @provenance library
/-- `eˣ = ∑ xⁿ/n!` for every real `x`. This applies Mathlib's
`NormedSpace.expSeries_div_hasSum_exp` together with `Real.exp_eq_exp_ℝ`, which identifies the
real exponential with the exponential series. -/
theorem exp_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x
-- @endregion

/-! ### A smooth function that is not the sum of its Taylor series -/

-- @region single_variable_calculus.flat_iterated_deriv_zero
-- @provenance independent
/-- Mathlib's `expNegInvGlue` is `exp (-1/x)` for `x > 0` and `0` for `x ≤ 0`; it is smooth
(`expNegInvGlue.contDiff`). **Every derivative of it at `0` is `0`**, so its Taylor series at
`0` is the zero series. Proof: on `(-∞, 0)` the function is locally zero, so each iterated
derivative vanishes there; iterated derivatives of a smooth function are continuous, so the
value at `0` is the limit from the left, which is `0`. -/
theorem flat_iteratedDeriv_zero (n : ℕ) : iteratedDeriv n expNegInvGlue 0 = 0 := by
  have hcont : Continuous (iteratedDeriv n expNegInvGlue) :=
    (expNegInvGlue.contDiff (n := ⊤)).continuous_iteratedDeriv n (by exact_mod_cast le_top)
  -- The iterated derivative vanishes at every negative point.
  have hneg : ∀ x : ℝ, x < 0 → iteratedDeriv n expNegInvGlue x = 0 := by
    intro x hx
    have hloc : expNegInvGlue =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      exact expNegInvGlue.zero_of_nonpos hy.le
    rw [hloc.iteratedDeriv_eq n]
    simp
  -- Take the limit from the left.
  have hlim : Tendsto (iteratedDeriv n expNegInvGlue) (𝓝[<] 0)
      (𝓝 (iteratedDeriv n expNegInvGlue 0)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (iteratedDeriv n expNegInvGlue) (𝓝[<] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hneg x hx).symm
  exact tendsto_nhds_unique hlim hzero
-- @endregion

-- @region single_variable_calculus.flat_pos
-- @provenance library
/-- …and yet `expNegInvGlue x > 0` for every `x > 0`: the function is not the sum of its
(zero) Taylor series on any interval `(0, r)`. This applies Mathlib's
`expNegInvGlue.pos_of_pos`. -/
theorem flat_pos {x : ℝ} (hx : 0 < x) : 0 < expNegInvGlue x :=
  expNegInvGlue.pos_of_pos hx
-- @endregion

end Lumenary.SingleVariableCalculus
