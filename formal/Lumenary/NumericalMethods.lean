/-
The Lumenary — formal mathematics
Numerical methods: the spacing of binary floating-point numbers (machine epsilon), the
amplification of rounding errors by cancellation, bisection, Newton's method for square roots,
the error identity behind quadratic convergence, and the exactness and error of the trapezoidal
and Simpson rules.

What is proved here and what Mathlib provides. We work with real numbers and a *model* of
floating point — the computed value is `x (1 + δ)` with `|δ| ≤ u` — rather than with Lean's
hardware `Float` type, whose operations are not available to proofs. The *independent*
declarations prove: that no binary64 number lies strictly between `1` and `1 + 2⁻⁵²`; the
cancellation bound; that bisection keeps a sign change in intervals of width `(b − a)/2ⁿ` and so
locates a root (with the intermediate value theorem from Mathlib); Heron's error identity
`x' − √a = (x − √a)²/(2x)`; the algebraic step of Newton's convergence proof; and that Simpson's
rule integrates every cubic exactly but not `x⁴`. The *library* declarations cite Mathlib's
error bound for the composite trapezoidal rule, its Taylor theorem with Lagrange remainder, and
an algebraic form of quadratic convergence for Newton's method on polynomials.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Dynamics.Newton

namespace Lumenary.NumericalMethods

open Set Real

/-! ### Floating-point numbers and machine epsilon -/

-- @region numerical_methods.is_binary64
-- @provenance definition
/-- A positive **binary64 number** (an IEEE 754 "double"), ignoring the limits on the exponent:
`m · 2ᵉ` with an integer *significand* `m` of exactly 53 bits, `2⁵² ≤ m < 2⁵³`, and an integer
exponent `e`. -/
def IsBinary64 (x : ℝ) : Prop :=
  ∃ m e : ℤ, 2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ x = m * (2 : ℝ) ^ e
-- @endregion

-- @region numerical_methods.one_add_eps_is_binary64
-- @provenance independent
/-- `1` and `1 + 2⁻⁵²` are both binary64 numbers: `1 = 2⁵² · 2⁻⁵²` and
`1 + 2⁻⁵² = (2⁵² + 1) · 2⁻⁵²`. -/
theorem one_add_eps_is_binary64 : IsBinary64 1 ∧ IsBinary64 (1 + 2 ^ (-52 : ℤ)) := by
  refine ⟨⟨2 ^ 52, -52, le_refl _, by norm_num, ?_⟩, ⟨2 ^ 52 + 1, -52, by norm_num, by norm_num, ?_⟩⟩
  · norm_num
  · norm_num
-- @endregion

-- @region numerical_methods.machine_epsilon
-- @provenance independent
/-- **Machine epsilon.** No binary64 number lies strictly between `1` and `1 + 2⁻⁵²`, so the gap
between `1` and the next larger double is `ε = 2⁻⁵² ≈ 2.2 × 10⁻¹⁶`.
Proof: if `1 < m 2ᵉ < 1 + 2⁻⁵² < 2` with `2⁵² ≤ m < 2⁵³`, then `2⁵³⁺ᵉ > 1` and `2⁵²⁺ᵉ < 2`, which
forces `e = −52`; but then `2⁵² < m < 2⁵² + 1`, impossible for an integer `m`. -/
theorem machine_epsilon (x : ℝ) (hx : IsBinary64 x) : ¬ (1 < x ∧ x < 1 + 2 ^ (-52 : ℤ)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨m, e, hm1, hm2, rfl⟩ := hx
  have two_pos : (0 : ℝ) < 2 := by norm_num
  have hm1' : (2 : ℝ) ^ (52 : ℤ) ≤ m := by exact_mod_cast hm1
  have hm2' : (m : ℝ) < 2 ^ (53 : ℤ) := by exact_mod_cast hm2
  have hpow : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
  have heps : (2 : ℝ) ^ (-52 : ℤ) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by norm_num)
  -- Lower bound on `e`: `1 < m 2ᵉ < 2⁵³ · 2ᵉ = 2^(53 + e)`.
  have hlo : (1 : ℝ) < 2 ^ (53 + e) := by
    rw [zpow_add₀ two_pos.ne']
    calc (1 : ℝ) < m * 2 ^ e := h1
      _ ≤ 2 ^ (53 : ℤ) * 2 ^ e := by gcongr
  have he1 : 0 < 53 + e := by
    by_contra hc
    rw [not_lt] at hc
    have : (2 : ℝ) ^ (53 + e) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hc
    linarith
  -- Upper bound on `e`: `2^(52 + e) = 2⁵² · 2ᵉ ≤ m 2ᵉ < 1 + 2⁻⁵² < 2 = 2¹`.
  have hhi : (2 : ℝ) ^ (52 + e) < 2 ^ (1 : ℤ) := by
    rw [zpow_add₀ two_pos.ne', zpow_one]
    calc (2 : ℝ) ^ (52 : ℤ) * 2 ^ e ≤ m * 2 ^ e := by gcongr
      _ < 1 + 2 ^ (-52 : ℤ) := h2
      _ < 2 := by linarith
  have he2 : 52 + e < 1 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hhi
  have he : e = -52 := by omega
  subst he
  -- Now `2⁵² < m < 2⁵² + 1` after multiplying through by `2⁵²`.
  have key : (2 : ℝ) ^ (52 : ℤ) * 2 ^ (-52 : ℤ) = 1 := by
    rw [← zpow_add₀ two_pos.ne']; norm_num
  have hmlo : (2 : ℝ) ^ (52 : ℤ) < m := by
    by_contra hc
    rw [not_lt] at hc
    have : (m : ℝ) * 2 ^ (-52 : ℤ) ≤ 2 ^ (52 : ℤ) * 2 ^ (-52 : ℤ) := by gcongr
    linarith
  have hmhi : (m : ℝ) < 2 ^ (52 : ℤ) + 1 := by
    by_contra hc
    rw [not_lt] at hc
    have : (2 ^ (52 : ℤ) + 1) * (2 : ℝ) ^ (-52 : ℤ) ≤ m * 2 ^ (-52 : ℤ) := by gcongr
    rw [add_mul, key, one_mul] at this
    linarith
  have hz1 : (2 : ℤ) ^ 52 < m := by exact_mod_cast hmlo
  have hz2 : m < (2 : ℤ) ^ 52 + 1 := by exact_mod_cast hmhi
  omega
-- @endregion

-- @region numerical_methods.rounds_to
-- @provenance definition
/-- The **standard model of floating-point arithmetic**: `x̂` is `x` with a relative error of at
most `u`, i.e. `x̂ = x (1 + δ)` for some `|δ| ≤ u`. For binary64 with rounding to nearest,
`u = 2⁻⁵³`, half of machine epsilon. -/
def RoundsTo (u x xhat : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ xhat = x * (1 + δ)
-- @endregion

-- @region numerical_methods.cancellation_bound
-- @provenance independent
/-- **Cancellation amplifies relative error.** If `x̂` and `ŷ` approximate `x` and `y` with
relative errors at most `u`, then the exact difference `x̂ − ŷ` is within `u (|x| + |y|)` of
`x − y`: `(x̂ − ŷ) − (x − y) = x δ₁ − y δ₂`. Dividing by `|x − y|`, the relative error of the
difference can be as large as `u (|x| + |y|)/|x − y|`, which is huge when `x ≈ y`. -/
theorem cancellation_bound {u x y xhat yhat : ℝ} (hx : RoundsTo u x xhat)
    (hy : RoundsTo u y yhat) : |(xhat - yhat) - (x - y)| ≤ u * (|x| + |y|) := by
  obtain ⟨d₁, hd₁, rfl⟩ := hx
  obtain ⟨d₂, hd₂, rfl⟩ := hy
  calc |(x * (1 + d₁) - y * (1 + d₂)) - (x - y)| = |x * d₁ + -(y * d₂)| := by ring_nf
    _ ≤ |x * d₁| + |-(y * d₂)| := abs_add_le _ _
    _ = |x| * |d₁| + |y| * |d₂| := by rw [abs_neg, abs_mul, abs_mul]
    _ ≤ |x| * u + |y| * u := by gcongr
    _ = u * (|x| + |y|) := by ring
-- @endregion

/-! ### Bisection -/

-- @region numerical_methods.bisect_step
-- @provenance definition
/-- One step of **bisection** on an interval `[a, b]` (stored as a pair): look at the midpoint
`m`; keep `[m, b]` if `f m ≤ 0` and `[a, m]` otherwise, so a sign change is kept. -/
noncomputable def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f ((p.1 + p.2) / 2) ≤ 0 then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)
-- @endregion

-- @region numerical_methods.bisect
-- @provenance definition
/-- The interval after `n` steps of bisection, starting from `[a, b]`. -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => bisectStep f (bisect f a b n)
-- @endregion

-- @region numerical_methods.bisect_width
-- @provenance independent
/-- **Bisection halves the interval**: after `n` steps its width is `(b − a)/2ⁿ`. -/
theorem bisect_width (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n := by
  induction n with
  | zero => simp [bisect]
  | succ k ih =>
    simp only [bisect, bisectStep]
    split_ifs <;> simp only [pow_succ] <;> linear_combination ih / 2
-- @endregion

-- @region numerical_methods.bisect_sign
-- @provenance independent
/-- **The loop invariant of bisection**: if `f a ≤ 0 ≤ f b`, then after every step the left end
still has `f ≤ 0` and the right end `f ≥ 0`. -/
theorem bisect_sign (f : ℝ → ℝ) (a b : ℝ) (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    f (bisect f a b n).1 ≤ 0 ∧ 0 ≤ f (bisect f a b n).2 := by
  induction n with
  | zero => exact ⟨ha, hb⟩
  | succ k ih =>
    simp only [bisect, bisectStep]
    split_ifs with h
    · exact ⟨h, ih.2⟩
    · exact ⟨ih.1, (lt_of_not_ge h).le⟩
-- @endregion

-- @region numerical_methods.bisection_converges
-- @provenance independent
/-- **Bisection always works for a continuous function with a sign change.** If `f` is
continuous, `a ≤ b` and `f a ≤ 0 ≤ f b`, then for every `n` there is a root `c` of `f` within
`(b − a)/2ⁿ⁺¹` of the `n`-th midpoint. The root comes from the intermediate value theorem
(Mathlib's `intermediate_value_Icc`) applied to the current interval. -/
theorem bisection_converges (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b)
    (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    ∃ c, f c = 0 ∧
      |((bisect f a b n).1 + (bisect f a b n).2) / 2 - c| ≤ (b - a) / 2 ^ (n + 1) := by
  set p := bisect f a b n with hp
  have hw : p.2 - p.1 = (b - a) / 2 ^ n := bisect_width f a b n
  have hs := bisect_sign f a b ha hb n
  have hle : p.1 ≤ p.2 := by
    have : 0 ≤ (b - a) / 2 ^ n := div_nonneg (by linarith) (by positivity)
    linarith
  obtain ⟨c, ⟨hc1, hc2⟩, hfc⟩ :=
    intermediate_value_Icc hle hf.continuousOn ⟨hs.1, hs.2⟩
  refine ⟨c, hfc, ?_⟩
  rw [abs_le, pow_succ]
  constructor <;>
  · rw [div_mul_eq_div_div] at *
    linarith
-- @endregion

/-! ### Newton's method -/

-- @region numerical_methods.heron_error
-- @provenance independent
/-- **Heron's method is Newton's method for `x² = a`**: `x' = (x + a/x)/2`. Its error satisfies
`x' − √a = (x − √a)² / (2x)` exactly: the new error is proportional to the *square* of the old
one. -/
theorem heron_error {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    (x + a / x) / 2 - √a = (x - √a) ^ 2 / (2 * x) := by
  have hs : √a ^ 2 = a := sq_sqrt ha
  field_simp
  linear_combination (-1 : ℝ) * hs
-- @endregion

-- @region numerical_methods.heron_ge_sqrt
-- @provenance independent
/-- From any positive start, every Heron iterate is at least `√a` (an instance of the AM–GM
inequality, read off from `heron_error`: the right-hand side is a square over a positive
number). -/
theorem heron_ge_sqrt {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) : √a ≤ (x + a / x) / 2 := by
  have h := heron_error ha hx
  have : 0 ≤ (x - √a) ^ 2 / (2 * x) := by positivity
  linarith
-- @endregion

-- @region numerical_methods.heron_quadratic
-- @provenance independent
/-- **Quadratic convergence of Heron's method.** If `x ≥ √a > 0`, the new error is at most the
old error squared, divided by `2√a`. So once the error is below `√a`, the number of correct
digits roughly doubles at every step. -/
theorem heron_quadratic {a x : ℝ} (ha : 0 < a) (hx : √a ≤ x) :
    |(x + a / x) / 2 - √a| ≤ (x - √a) ^ 2 / (2 * √a) := by
  have hs : 0 < √a := sqrt_pos.mpr ha
  have hx0 : 0 < x := lt_of_lt_of_le hs hx
  rw [heron_error ha.le hx0, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith
-- @endregion

-- @region numerical_methods.newton_error_step
-- @provenance independent
/-- **The algebraic heart of Newton's convergence proof.** Suppose `f(r) = 0` and Taylor's
theorem at `x` gives `0 = f(r) = f(x) + f'(x)(r − x) + c (r − x)²` (with `c = f''(ξ)/2`). If
`f'(x) ≠ 0`, the Newton step `x' = x − f(x)/f'(x)` satisfies `x' − r = (c / f'(x)) (x − r)²`. -/
theorem newton_error_step {x r fx dfx c : ℝ} (hd : dfx ≠ 0)
    (htaylor : fx + dfx * (r - x) + c * (r - x) ^ 2 = 0) :
    (x - fx / dfx) - r = c / dfx * (x - r) ^ 2 := by
  have hfx : fx = -(dfx * (r - x) + c * (r - x) ^ 2) := by linarith
  rw [hfx]
  field_simp
  ring
-- @endregion

-- @region numerical_methods.taylor_lagrange
-- @provenance library
/-- **Taylor's theorem with the Lagrange remainder**, as Mathlib states it
(`taylor_mean_remainder_lagrange`): if `f` is `n` times continuously differentiable on the
interval between `x₀` and `x`, and its `n`-th derivative is differentiable inside, then
`f(x) − Tₙ(x) = f⁽ⁿ⁺¹⁾(ξ)(x − x₀)ⁿ⁺¹/(n + 1)!` for some `ξ` strictly between. With `n = 1` this
supplies the constant `c = f''(ξ)/2` in `newton_error_step`. -/
theorem taylor_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1).factorial :=
  taylor_mean_remainder_lagrange hx hf hf'
-- @endregion

open Polynomial in
-- @region numerical_methods.newton_algebraic
-- @provenance library
/-- **Quadratic convergence, algebraically.** For a polynomial `P` over a commutative ring, if
`P(x)` is nilpotent and `P'(x)` is invertible, then after `n` Newton steps `P(x)^(2ⁿ)` divides
the new value of `P`: the "error" is raised to the power `2ⁿ`. This is Mathlib's
`Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`, the engine of Hensel's lemma. -/
theorem newton_algebraic {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {P : R[X]}
    {x : S} (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x (derivative P))) (n : ℕ) :
    (aeval x P) ^ (2 ^ n) ∣ aeval (P.newtonMap^[n] x) P :=
  aeval_pow_two_pow_dvd_aeval_iterate_newtonMap h h' n
-- @endregion

/-! ### Numerical integration -/

-- @region numerical_methods.simpson_exact_cubic
-- @provenance independent
/-- **Simpson's rule integrates cubics exactly**:
`∫ₐᵇ p = (b − a)/6 · (p(a) + 4 p((a + b)/2) + p(b))` for `p(x) = c₃x³ + c₂x² + c₁x + c₀`.
Proof: an antiderivative `P` gives `∫ₐᵇ p = P(b) − P(a)` (the fundamental theorem of calculus,
Mathlib's `integral_eq_sub_of_hasDerivAt`), and the two sides agree as polynomials in `a, b`. -/
theorem simpson_exact_cubic (c₃ c₂ c₁ c₀ a b : ℝ) :
    ∫ x in a..b, (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) =
      (b - a) / 6 * ((c₃ * a ^ 3 + c₂ * a ^ 2 + c₁ * a + c₀) +
        4 * (c₃ * ((a + b) / 2) ^ 3 + c₂ * ((a + b) / 2) ^ 2 + c₁ * ((a + b) / 2) + c₀) +
        (c₃ * b ^ 3 + c₂ * b ^ 2 + c₁ * b + c₀)) := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt
      (fun x => c₃ * x ^ 4 / 4 + c₂ * x ^ 3 / 3 + c₁ * x ^ 2 / 2 + c₀ * x)
      (c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) x := by
    intro x _
    have h := ((((hasDerivAt_pow 4 x).const_mul c₃).div_const 4).add
      (((hasDerivAt_pow 3 x).const_mul c₂).div_const 3)).add
      (((hasDerivAt_pow 2 x).const_mul c₁).div_const 2) |>.add ((hasDerivAt_id x).const_mul c₀)
    convert h using 1
    · ext y; simp
    · push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring
-- @endregion

-- @region numerical_methods.simpson_not_exact_quartic
-- @provenance independent
/-- …but not quartics: on `[0, 1]`, `∫ x⁴ = 1/5`, while Simpson's rule gives
`(1/6)(0 + 4 · (1/2)⁴ + 1) = 5/24`. So the degree of exactness of Simpson's rule is exactly `3`,
which is why its error involves the fourth derivative. -/
theorem simpson_not_exact_quartic :
    ∫ x in (0 : ℝ)..1, x ^ 4 = 1 / 5 ∧
      (1 - 0) / 6 * ((0 : ℝ) ^ 4 + 4 * ((0 + 1) / 2) ^ 4 + 1 ^ 4) = 5 / 24 := by
  constructor
  · rw [integral_pow]; norm_num
  · norm_num
-- @endregion

-- @region numerical_methods.trapezoid_error
-- @provenance library
/-- **The error of the composite trapezoidal rule** with `N` strips is at most
`|b − a|³ ζ / (12 N²)` when `|f''| ≤ ζ` on the interval — that is, `(b − a) h² ζ / 12` with
`h = (b − a)/N`: the `O(h²)` of the lesson. This applies Mathlib's
`trapezoidal_error_le_of_c2`, whose proof is the lesson's proof (differentiate the error of one
strip twice). -/
theorem trapezoid_error {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiffOn ℝ 2 f (uIcc a b)) {ζ : ℝ}
    (hζ : ∀ x, |iteratedDerivWithin 2 f (uIcc a b) x| ≤ ζ) {N : ℕ} (hN : 0 < N) :
    |trapezoidal_error f N a b| ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) :=
  trapezoidal_error_le_of_c2 hf hζ hN
-- @endregion

end Lumenary.NumericalMethods
