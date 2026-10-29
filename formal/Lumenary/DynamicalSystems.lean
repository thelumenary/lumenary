/-
The Lumenary — formal mathematics
Dynamical systems and chaos: fixed points and periodic orbits of the logistic map, their
stability, the attracting fixed point theorem, contractions, expansion of the doubling map, and
a Lyapunov function for a planar linear system.

What is proved here and what Mathlib provides. Mathlib's dynamics library supplies the language
of fixed points (`Function.IsFixedPt`), periodic points (`Function.IsPeriodicPt`,
`Function.minimalPeriod`), iteration (`f^[n]`), flows and ω-limit sets, and the Banach fixed point
theorem (`ContractingWith`). The *independent* declarations below prove the lesson's concrete
results: the fixed points of `x ↦ r x (1 - x)` and the derivative `2 - r` at the non-zero one,
so that it is attracting exactly for `1 < r < 3`; the explicit period-2 orbit for `r > 3` and
its multiplier `4 + 2r - r²`, so that it is attracting exactly for `3 < r < 1 + √6`; the
attracting fixed point theorem (if `|f'| ≤ K < 1` near a fixed point, orbits converge to it,
via the mean value inequality and the estimate `|fⁿ(x) - x*| ≤ Kⁿ |x - x*|`); the exponential
separation of nearby orbits of the doubling map; and the decay of `V = x² + y²` along a spiral
sink. Not formalised: Hartman–Grobman, Poincaré–Bendixson, period doubling cascades and
Feigenbaum universality, Sharkovskii's theorem, and any proof of chaos for the logistic map.
-/
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Lumenary.DynamicalSystems

open Filter Topology Set Function

/-! ### The logistic map -/

-- @region dynamical_systems.logistic
-- @provenance definition
/-- The **logistic map** `f_r(x) = r x (1 - x)`, a model of a population with limited resources
(`x` is the population as a fraction of its maximum, `r` the growth rate). -/
def logistic (r x : ℝ) : ℝ := r * x * (1 - x)
-- @endregion

-- @region dynamical_systems.logistic_fixed_points
-- @provenance independent
/-- **Fixed points of the logistic map.** For `r ≠ 0`, `f_r(x) = x` exactly when `x = 0` or
`x = 1 - 1/r`: the equation `r x (1 - x) = x` factors as `x (r - 1 - r x) = 0`. -/
theorem logistic_fixed_points {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    logistic r x = x ↔ x = 0 ∨ x = 1 - 1 / r := by
  unfold logistic
  constructor
  · intro h
    have h' : x * (r - 1 - r * x) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · right; field_simp; linarith
  · rintro (rfl | rfl)
    · ring
    · field_simp; ring
-- @endregion

-- @region dynamical_systems.logistic_deriv_at_fixed
-- @provenance independent
/-- **The multiplier of the non-zero fixed point.** `f_r'(x) = r (1 - 2x)`, which at
`x* = 1 - 1/r` equals `r (1 - 2 + 2/r) = 2 - r`. -/
theorem logistic_deriv_at_fixed {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (logistic r) (2 - r) (1 - 1 / r) := by
  have h : HasDerivAt (fun x => r * x * (1 - x))
      (r * 1 * (1 - (1 - 1 / r)) + r * (1 - 1 / r) * (0 - 1)) (1 - 1 / r) :=
    (((hasDerivAt_id' _).const_mul r).mul ((hasDerivAt_const _ (1 : ℝ)).sub (hasDerivAt_id' _)))
  refine h.congr_deriv ?_
  field_simp
  ring
-- @endregion

-- @region dynamical_systems.logistic_stable_iff
-- @provenance independent
/-- **When is `1 - 1/r` attracting?** Its multiplier `2 - r` satisfies `|2 - r| < 1` exactly when
`1 < r < 3`. (At `r = 3` the multiplier passes through `-1`: a period-doubling bifurcation.) -/
theorem logistic_stable_iff (r : ℝ) : |2 - r| < 1 ↔ 1 < r ∧ r < 3 := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith
-- @endregion

-- @region dynamical_systems.period_two_orbit
-- @provenance independent
/-- **The period-2 orbit of the logistic map.** For `r > 3`, put `s = √((r - 3)(r + 1)) > 0` and
`p± = (r + 1 ± s)/(2r)`. Then `f_r(p₊) = p₋` and `f_r(p₋) = p₊`, and `p₊ ≠ p₋`: the two points
form an orbit of period exactly 2. Both identities reduce, after clearing denominators, to
`s² = (r - 3)(r + 1)`. -/
theorem period_two_orbit {r : ℝ} (hr : 3 < r) :
    let s := Real.sqrt ((r - 3) * (r + 1))
    logistic r ((r + 1 + s) / (2 * r)) = (r + 1 - s) / (2 * r) ∧
      logistic r ((r + 1 - s) / (2 * r)) = (r + 1 + s) / (2 * r) ∧
      (r + 1 + s) / (2 * r) ≠ (r + 1 - s) / (2 * r) := by
  intro s
  have hr0 : r ≠ 0 := by linarith
  have hpos : 0 < (r - 3) * (r + 1) := by nlinarith
  have hs : s ^ 2 = (r - 3) * (r + 1) := Real.sq_sqrt hpos.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  unfold logistic
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination (-1) * hs
  · field_simp
    linear_combination (-1) * hs
  · intro h
    field_simp at h
    linarith
-- @endregion

-- @region dynamical_systems.period_two_minimal
-- @provenance independent
/-- In Mathlib's language: for `r > 3`, `p₊` is a periodic point of `f_r` with period `2` that is
not fixed, so its **minimal period** is `2` (`Function.minimalPeriod_eq_prime`, as `2` is
prime). -/
theorem period_two_minimal {r : ℝ} (hr : 3 < r) :
    minimalPeriod (logistic r) ((r + 1 + Real.sqrt ((r - 3) * (r + 1))) / (2 * r)) = 2 := by
  obtain ⟨h1, h2, hne⟩ := period_two_orbit hr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply minimalPeriod_eq_prime
  · show (logistic r)^[2] _ = _
    simp only [iterate_succ, iterate_zero, comp_apply, id]
    rw [h1, h2]
  · intro hfix
    exact hne (hfix.symm.trans h1)
-- @endregion

-- @region dynamical_systems.two_cycle_multiplier
-- @provenance independent
/-- **Stability of the 2-cycle.** The multiplier of the period-2 orbit, `(f_r²)'(p₊) =
f_r'(p₊) f_r'(p₋) = r² (1 - 2p₊)(1 - 2p₋)`, equals `4 + 2r - r²`. It lies in `(-1, 1)` exactly
when `3 < r < 1 + √6 ≈ 3.449`, where the 2-cycle in turn doubles. -/
theorem two_cycle_multiplier {r : ℝ} (hr : 3 < r) :
    let s := Real.sqrt ((r - 3) * (r + 1))
    r * (1 - 2 * ((r + 1 + s) / (2 * r))) * (r * (1 - 2 * ((r + 1 - s) / (2 * r)))) =
      4 + 2 * r - r ^ 2 := by
  intro s
  have hr0 : r ≠ 0 := by linarith
  have hpos : 0 < (r - 3) * (r + 1) := by nlinarith
  have hs : s ^ 2 = (r - 3) * (r + 1) := Real.sq_sqrt hpos.le
  field_simp
  linear_combination (-1) * hs
-- @endregion

/-! ### Attracting fixed points and contractions -/

-- @region dynamical_systems.iterate_contraction
-- @provenance independent
/-- **The basic estimate.** If `f` fixes `a`, maps the interval `I = [a - δ, a + δ]` into itself
and pulls every point of `I` towards `a` by a factor `K` (`|f x - a| ≤ K |x - a|`), then
`|fⁿ(x) - a| ≤ Kⁿ |x - a|` for `x ∈ I`. Induction on `n`. -/
theorem iterate_contraction {f : ℝ → ℝ} {a δ K : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hpull : ∀ x ∈ Icc (a - δ) (a + δ), |f x - a| ≤ K * |x - a|) :
    ∀ n : ℕ, ∀ x ∈ Icc (a - δ) (a + δ),
      f^[n] x ∈ Icc (a - δ) (a + δ) ∧ |f^[n] x - a| ≤ K ^ n * |x - a| := by
  have hmem : ∀ x, x ∈ Icc (a - δ) (a + δ) ↔ |x - a| ≤ δ := fun x => by
    rw [abs_le, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  intro n
  induction n with
  | zero => intro x hx; simp [hx]
  | succ n ih =>
    intro x hx
    obtain ⟨hin, hbound⟩ := ih x hx
    rw [iterate_succ_apply']
    have step := hpull _ hin
    have hδ : |f^[n] x - a| ≤ δ := (hmem _).mp hin
    refine ⟨(hmem _).mpr ?_, ?_⟩
    · calc |f (f^[n] x) - a| ≤ K * |f^[n] x - a| := step
        _ ≤ 1 * δ := mul_le_mul hK1 hδ (abs_nonneg _) zero_le_one
        _ = δ := one_mul δ
    · calc |f (f^[n] x) - a| ≤ K * |f^[n] x - a| := step
        _ ≤ K * (K ^ n * |x - a|) := mul_le_mul_of_nonneg_left hbound hK0
        _ = K ^ (n + 1) * |x - a| := by ring
-- @endregion

-- @region dynamical_systems.attracting_fixed_point
-- @provenance independent
/-- **Attracting fixed point theorem.** Let `f(a) = a`, and suppose `f` is differentiable on
`I = [a - δ, a + δ]` with `|f'| ≤ K < 1` there. Then every orbit starting in `I` converges to `a`.
Proof: the mean value inequality gives `|f x - a| = |f x - f a| ≤ K |x - a|` on `I`; then
`iterate_contraction` gives `|fⁿ(x) - a| ≤ Kⁿ |x - a| → 0`. (If `f` is C¹ with `|f'(a)| < 1`,
continuity of `f'` provides such a `δ` and `K`.) -/
theorem attracting_fixed_point {f : ℝ → ℝ} {a δ K : ℝ} (hfix : f a = a) (hδ : 0 ≤ δ)
    (hK0 : 0 ≤ K) (hK1 : K < 1) (hdiff : ∀ x ∈ Icc (a - δ) (a + δ), DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Icc (a - δ) (a + δ), |deriv f x| ≤ K) {x : ℝ}
    (hx : x ∈ Icc (a - δ) (a + δ)) : Tendsto (fun n => f^[n] x) atTop (𝓝 a) := by
  have ha : a ∈ Icc (a - δ) (a + δ) := ⟨by linarith, by linarith⟩
  have hpull : ∀ y ∈ Icc (a - δ) (a + δ), |f y - a| ≤ K * |y - a| := by
    intro y hy
    have := (convex_Icc (a - δ) (a + δ)).norm_image_sub_le_of_norm_deriv_le hdiff
      (fun z hz => by rw [Real.norm_eq_abs]; exact hderiv z hz) ha hy
    simpa [Real.norm_eq_abs, hfix] using this
  have hbound := iterate_contraction hK0 hK1.le hpull
  -- `Kⁿ |x - a| → 0`, and `|fⁿ x - a|` is squeezed below it.
  have hlim : Tendsto (fun n : ℕ => K ^ n * |x - a|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const |x - a|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [Real.norm_eq_abs]
  exact (hbound n x hx).2
-- @endregion

-- @region dynamical_systems.banach_fixed_point
-- @provenance library
/-- **Banach's fixed point theorem**: a contraction of a non-empty complete metric space has a
unique fixed point, and every orbit converges to it. This applies Mathlib's
`ContractingWith.tendsto_iterate_fixedPoint` (and `ContractingWith.fixedPoint_isFixedPt`). -/
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} (hf : ContractingWith K f) (x : X) :
    IsFixedPt f (ContractingWith.fixedPoint f hf) ∧
      Tendsto (fun n => f^[n] x) atTop (𝓝 (ContractingWith.fixedPoint f hf)) :=
  ⟨ContractingWith.fixedPoint_isFixedPt hf, hf.tendsto_iterate_fixedPoint x⟩
-- @endregion

/-! ### Expansion: the doubling map -/

-- @region dynamical_systems.doubling_separates
-- @provenance independent
/-- **Nearby orbits of the doubling map separate exponentially.** For the lift `D(x) = 2x` of the
doubling map `x ↦ 2x mod 1`, two orbits starting at distance `d` are at distance `2ⁿ d` after `n`
steps. So an initial uncertainty of `10⁻¹⁰` grows to order `1` within about 33 steps: the
Lyapunov exponent is `ln 2`. -/
theorem doubling_separates (x y : ℝ) (n : ℕ) :
    (fun z : ℝ => 2 * z)^[n] x - (fun z : ℝ => 2 * z)^[n] y = 2 ^ n * (x - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ← mul_sub, ih]
    ring
-- @endregion

/-! ### A Lyapunov function for a planar linear system -/

-- @region dynamical_systems.lyapunov_decay
-- @provenance independent
/-- **A Lyapunov function for the spiral sink** `x' = -x + y`, `y' = -x - y`. Along any solution,
`V = x² + y²` satisfies `V' = 2x(-x + y) + 2y(-x - y) = -2V`, so `V(t) = V(0) e^{-2t}`: every
solution spirals into the origin. Proof: `V(t) e^{2t}` has derivative `0`, hence is constant. -/
theorem lyapunov_decay {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (-x t + y t) t) (hy : ∀ t, HasDerivAt y (-x t - y t) t) (t : ℝ) :
    x t ^ 2 + y t ^ 2 = (x 0 ^ 2 + y 0 ^ 2) * Real.exp (-2 * t) := by
  set W : ℝ → ℝ := fun s => (x s ^ 2 + y s ^ 2) * Real.exp (2 * s) with hW
  have hWd : ∀ s, HasDerivAt W 0 s := by
    intro s
    have h1 := (((hx s).pow 2).add ((hy s).pow 2)).mul
      (((hasDerivAt_id' s).const_mul 2).exp)
    convert h1 using 1
    simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
    ring
  have hconst : W t = W 0 :=
    is_const_of_deriv_eq_zero (fun s => (hWd s).differentiableAt) (fun s => (hWd s).deriv) t 0
  have hexp : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [hW, mul_zero, Real.exp_zero, mul_one] at hconst
  calc x t ^ 2 + y t ^ 2 = (x t ^ 2 + y t ^ 2) * (Real.exp (2 * t) * Real.exp (-2 * t)) := by
        rw [hexp, mul_one]
    _ = ((x t ^ 2 + y t ^ 2) * Real.exp (2 * t)) * Real.exp (-2 * t) := by ring
    _ = (x 0 ^ 2 + y 0 ^ 2) * Real.exp (-2 * t) := by rw [hconst]
-- @endregion

end Lumenary.DynamicalSystems
