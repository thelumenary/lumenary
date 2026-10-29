/-
The Lumenary — formal mathematics
Exponential and logarithmic functions: why the laws of exponents force a⁰ = 1, a⁻ˣ = 1/aˣ and
the values at fractions; the laws of logarithms; logarithms as inverse functions; the
irrationality of log₂ 3; exponential versus polynomial growth; and the number e.

Proved here (`@provenance independent`): for any function `E : ℝ → ℝ` that is not identically
zero and satisfies the law `E(x + y) = E(x)·E(y)`, the values are positive, `E 0 = 1`,
`E(−x) = 1/E(x)`, `E(n x) = E(x)ⁿ` for integers `n`, and `E` agrees with Mathlib's real power
`a ^ q` at every rational `q` (where `a = E 1`) — so the laws alone determine the values at
fractions; the laws of logarithms, derived from `exp(x + y) = exp x · exp y`; `x ↦ bˣ` is a
bijection onto `(0, ∞)` for `b > 0`, `b ≠ 1`; `log₂ 3` is irrational; Bernoulli's inequality,
`n² < 2ⁿ` for `n ≥ 5`, and `(1 + 1/n)ⁿ ≥ 2`.

From Mathlib (`@provenance library`): `Real.rpow_add`, `Real.exp_add`, `Real.log_mul`,
`Real.tendsto_exp_div_pow_atTop` (eˣ/xⁿ → ∞) and `Real.tendsto_one_add_div_pow_exp`
((1 + t/n)ⁿ → eᵗ). Mathlib defines `exp` by its power series, `log` as its inverse on
`(0, ∞)`, and `a ^ x = exp (x · log a)` for `a > 0`; `Real.logb b x = log x / log b`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Lumenary.ExponentialLogarithmicFunctions

open Real Filter Topology

/-! ### The laws of exponents force the definitions -/

section Laws

variable {E : ℝ → ℝ}

-- @region exponential_logarithmic_functions.law_zero
-- @provenance independent
/-- **Why `a⁰ = 1`.** If `E(x + y) = E(x)·E(y)` for all `x, y` and `E` is not the zero function,
then `E 0 = 1`: pick `x` with `E x ≠ 0`; then `E x = E(x + 0) = E x · E 0`, and cancelling the
non-zero number `E x` leaves `E 0 = 1`. -/
theorem law_zero (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) : E 0 = 1 := by
  obtain ⟨x, hx⟩ := hE
  have h : E x * E 0 = E x * 1 := by rw [← hadd, add_zero, mul_one]
  exact mul_left_cancel₀ hx h
-- @endregion

-- @region exponential_logarithmic_functions.law_neg
-- @provenance independent
/-- **Why `a⁻ˣ = 1/aˣ`.** `E(x)·E(−x) = E(x + (−x)) = E 0 = 1`, so `E(−x)` is the reciprocal of
`E(x)` (and in particular `E x` is never zero). -/
theorem law_neg (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) (x : ℝ) :
    E (-x) = (E x)⁻¹ := by
  have h : E x * E (-x) = 1 := by rw [← hadd, add_neg_cancel, law_zero hadd hE]
  exact eq_inv_of_mul_eq_one_right h
-- @endregion

-- @region exponential_logarithmic_functions.law_pos
-- @provenance independent
/-- **Powers of a positive base are positive.** `E x = E(x/2 + x/2) = E(x/2)² ≥ 0`, and
`E x ≠ 0` because `E x · E(−x) = 1`. So `E x > 0`. -/
theorem law_pos (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) (x : ℝ) :
    0 < E x := by
  have hsq : E x = E (x / 2) * E (x / 2) := by rw [← hadd]; ring_nf
  have hne : E x ≠ 0 := by
    intro h0
    have h1 : E x * E (-x) = 1 := by rw [← hadd, add_neg_cancel, law_zero hadd hE]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hnn : 0 ≤ E x := by rw [hsq]; exact mul_self_nonneg _
  exact lt_of_le_of_ne hnn (Ne.symm hne)
-- @endregion

-- @region exponential_logarithmic_functions.law_nat
-- @provenance independent
/-- **Whole-number multiples:** `E(n·x) = E(x)ⁿ`, by induction on `n`:
`E((n + 1)x) = E(nx + x) = E(x)ⁿ · E(x)`. -/
theorem law_nat (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) (x : ℝ) (n : ℕ) :
    E (n * x) = E x ^ n := by
  induction n with
  | zero => simp [law_zero hadd hE]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, pow_succ]
-- @endregion

-- @region exponential_logarithmic_functions.law_int
-- @provenance independent
/-- **Integer multiples:** `E(n·x) = E(x)ⁿ` for every integer `n`, negative ones included,
combining `law_nat` with `law_neg`. -/
theorem law_int (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) (x : ℝ) (n : ℤ) :
    E (n * x) = E x ^ n := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast]
    exact law_nat hadd hE x m
  | negSucc m =>
    rw [Int.cast_negSucc, zpow_negSucc, neg_mul, law_neg hadd hE, ← law_nat hadd hE x (m + 1)]
-- @endregion

-- @region exponential_logarithmic_functions.law_rat
-- @provenance independent
/-- **The values at fractions are forced.** Let `a = E 1`. For every rational `q`, `E q` equals
Mathlib's real power `a ^ q`. Write `q = m/n` with `n > 0`: then `E(q)ⁿ = E(n·q) = E(m) = aᵐ`,
so `E q` is a positive `n`-th root of `aᵐ`. A positive number has only one positive `n`-th
root, and `a ^ q` is one, so the two agree. -/
theorem law_rat (hadd : ∀ x y, E (x + y) = E x * E y) (hE : ∃ x, E x ≠ 0) (q : ℚ) :
    E q = E 1 ^ (q : ℝ) := by
  have ha : 0 < E 1 := law_pos hadd hE 1
  have hn : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  -- `E(q)ⁿ = aᵐ`
  have h1 : E q ^ q.den = E 1 ^ q.num := by
    rw [← law_nat hadd hE, ← law_int hadd hE, mul_one]
    congr 1
    exact_mod_cast q.den_mul_eq_num
  -- `(a ^ q)ⁿ = aᵐ`
  have h2 : (E 1 ^ (q : ℝ)) ^ q.den = E 1 ^ q.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_intCast]
    congr 1
    exact_mod_cast q.mul_den_eq_num
  rw [← h2] at h1
  exact (pow_left_inj₀ (law_pos hadd hE q).le (Real.rpow_pos_of_pos ha _).le q.den_nz).mp h1
-- @endregion

end Laws

-- @region exponential_logarithmic_functions.rpow_add_library
-- @provenance library
/-- **The law of exponents for real powers:** `a^(x + y) = aˣ · aʸ` for `a > 0` and all real
`x, y`. This applies Mathlib's `Real.rpow_add`. So Mathlib's `x ↦ a ^ x` is a function `E` of the
kind studied above, and `law_rat` shows it is the *only* such function with `E 1 = a` at the
rationals. -/
theorem rpow_add_library {a : ℝ} (ha : 0 < a) (x y : ℝ) : a ^ (x + y) = a ^ x * a ^ y :=
  Real.rpow_add ha x y
-- @endregion

-- @region exponential_logarithmic_functions.exp_add_library
-- @provenance library
/-- **`exp` turns addition into multiplication:** `e^(x + y) = eˣ · eʸ`. This applies
`Real.exp_add`. -/
theorem exp_add_library (x y : ℝ) : exp (x + y) = exp x * exp y :=
  Real.exp_add x y
-- @endregion

/-! ### Logarithms -/

-- @region exponential_logarithmic_functions.log_mul_from_exp
-- @provenance independent
/-- **The product law for logarithms**, derived from the exponential law. Both sides have the
same exponential — `exp(log x + log y) = exp(log x)·exp(log y) = xy = exp(log(xy))` — and `exp`
is injective, so they are equal. -/
theorem log_mul_from_exp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log (x * y) = log x + log y := by
  apply Real.exp_injective
  rw [Real.exp_add, Real.exp_log hx, Real.exp_log hy, Real.exp_log (mul_pos hx hy)]
-- @endregion

-- @region exponential_logarithmic_functions.log_rpow_from_exp
-- @provenance independent
/-- **The power law for logarithms:** `log(xʳ) = r·log x` for `x > 0`. Mathlib defines
`xʳ = exp(log x · r)`, so `exp(log(xʳ)) = xʳ = exp(r · log x)`; injectivity of `exp` finishes. -/
theorem log_rpow_from_exp {x : ℝ} (hx : 0 < x) (r : ℝ) : log (x ^ r) = r * log x := by
  apply Real.exp_injective
  rw [Real.exp_log (Real.rpow_pos_of_pos hx r), Real.rpow_def_of_pos hx, mul_comm]
-- @endregion

-- @region exponential_logarithmic_functions.log_mul_library
-- @provenance library
/-- The product law as stated in Mathlib, for all non-zero `x, y` (using `log |x|` for negative
numbers). This applies `Real.log_mul`. -/
theorem log_mul_library {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
  Real.log_mul hx hy
-- @endregion

-- @region exponential_logarithmic_functions.rpow_bijective
-- @provenance independent
/-- **`x ↦ bˣ` is a bijection from `ℝ` onto `(0, ∞)`** for `b > 0`, `b ≠ 1`: every `y > 0` is
`bˣ` for exactly one `x`, namely `x = log_b y`. Existence is `Real.rpow_logb`; uniqueness:
if `b^x₁ = b^x₂`, take logarithms to get `x₁ log b = x₂ log b`, and `log b ≠ 0`. -/
theorem rpow_bijective {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) {y : ℝ} (hy : 0 < y) :
    ∃! x : ℝ, b ^ x = y := by
  refine ⟨logb b y, Real.rpow_logb hb hb1 hy, ?_⟩
  intro x hx
  have hlogb : log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb hb1
  have h : x * log b = log y := by rw [← log_rpow_from_exp hb x, hx]
  rw [Real.logb, ← h]
  field_simp
-- @endregion

-- @region exponential_logarithmic_functions.solve_two_pow
-- @provenance independent
/-- **Solving an exponential equation:** `2ˣ = 10` has the solution `x = log 10 / log 2`
(about `3.32`). Indeed `2^(log 10 / log 2) = exp(log 2 · log 10 / log 2) = exp(log 10) = 10`. -/
theorem solve_two_pow : (2 : ℝ) ^ (log 10 / log 2) = 10 := by
  have h2 : log 2 ≠ 0 := by positivity
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_div_cancel₀ _ h2,
    Real.exp_log (by norm_num)]
-- @endregion

-- @region exponential_logarithmic_functions.two_pow_ne_three_pow
-- @provenance independent
/-- **No power of 2 is a power of 3** (except `2⁰ = 3⁰`): if `q ≥ 1` then `2ᵖ ≠ 3^q`.
A power of 3 is odd. A power of 2 is even unless `p = 0`, and then `2⁰ = 1 < 3 ≤ 3^q`. -/
theorem two_pow_ne_three_pow (p q : ℕ) (hq : 0 < q) : 2 ^ p ≠ 3 ^ q := by
  intro h
  have hodd : 3 ^ q % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : 3 ≤ 3 ^ q := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hq) 3
    simp at h
    omega
  · have heven : 2 ^ p % 2 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hp)
      rw [pow_succ, Nat.mul_mod_left]
    omega
-- @endregion

-- @region exponential_logarithmic_functions.irrational_logb_two_three
-- @provenance independent
/-- **`log₂ 3` is irrational.** Suppose `log₂ 3 = m/n` with integers `m` and `n > 0`. Then
`2^(m/n) = 3`, so `2ᵐ = 3ⁿ`. Since `log₂ 3 > 0`, `m > 0`, and this contradicts
`two_pow_ne_three_pow`. -/
theorem irrational_logb_two_three : Irrational (logb 2 3) := by
  rintro ⟨q, hq⟩
  have hpos : 0 < logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have hq0 : (0 : ℝ) < q := hq ▸ hpos
  have hnum : 0 < q.num := Rat.num_pos.mpr (by exact_mod_cast hq0)
  -- `2 ^ q = 3`
  have h3 : (2 : ℝ) ^ (q : ℝ) = 3 := by
    rw [hq]; exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  -- raise both sides to the power `n = q.den`
  have hpow : (2 : ℝ) ^ (q.num.toNat) = 3 ^ q.den := by
    have hm : ((q.num.toNat : ℕ) : ℝ) = (q : ℝ) * q.den := by
      have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
      have h2 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast h1
      rw [h2]
      exact_mod_cast q.mul_den_eq_num.symm
    rw [← h3, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hm]
  have hnat : 2 ^ (q.num.toNat) = 3 ^ q.den := by exact_mod_cast hpow
  exact two_pow_ne_three_pow _ _ q.den_pos hnat
-- @endregion

/-! ### Growth -/

-- @region exponential_logarithmic_functions.bernoulli
-- @provenance independent
/-- **Bernoulli's inequality:** `(1 + h)ⁿ ≥ 1 + n h` for `h ≥ −1`. Induction on `n`:
`(1 + h)ⁿ⁺¹ = (1 + h)ⁿ(1 + h) ≥ (1 + nh)(1 + h) = 1 + (n + 1)h + nh² ≥ 1 + (n + 1)h`,
using `1 + h ≥ 0` in the first step. (Mathlib: `one_add_mul_le_pow`.) -/
theorem bernoulli {h : ℝ} (hh : -1 ≤ h) (n : ℕ) : 1 + n * h ≤ (1 + h) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ 1 + h := by linarith
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc 1 + ((n + 1 : ℕ) : ℝ) * h ≤ 1 + (n + 1) * h + n * h ^ 2 := by
          push_cast; nlinarith [sq_nonneg h]
      _ = (1 + n * h) * (1 + h) := by ring
      _ ≤ (1 + h) ^ n * (1 + h) := mul_le_mul_of_nonneg_right ih h1
      _ = (1 + h) ^ (n + 1) := by rw [pow_succ]
-- @endregion

-- @region exponential_logarithmic_functions.e_ge_two
-- @provenance independent
/-- **A first estimate for e:** `(1 + 1/n)ⁿ ≥ 2` for every `n ≥ 1`, by Bernoulli's inequality
with `h = 1/n`: `(1 + 1/n)ⁿ ≥ 1 + n · (1/n) = 2`. -/
theorem e_ge_two (n : ℕ) (hn : 1 ≤ n) : 2 ≤ (1 + 1 / (n : ℝ)) ^ n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : (-1 : ℝ) ≤ 1 / n := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h := bernoulli hh n
  have h1 : (n : ℝ) * (1 / n) = 1 := by field_simp
  linarith
-- @endregion

-- @region exponential_logarithmic_functions.sq_lt_two_pow
-- @provenance independent
/-- **Doubling beats squaring:** `n² < 2ⁿ` for every `n ≥ 5`. Induction: true at `n = 5`
(`25 < 32`); and if `n² < 2ⁿ` with `n ≥ 5`, then
`(n + 1)² = n² + 2n + 1 < n² + n² < 2ⁿ + 2ⁿ = 2ⁿ⁺¹`, because `2n + 1 < n²` once `n ≥ 3`. -/
theorem sq_lt_two_pow (n : ℕ) (hn : 5 ≤ n) : n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : 2 * n + 1 < n ^ 2 := by nlinarith
    calc (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
      _ < n ^ 2 + n ^ 2 := by omega
      _ < 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
-- @endregion

-- @region exponential_logarithmic_functions.exp_beats_powers
-- @provenance library
/-- **The exponential function eventually exceeds every power:** `eˣ / xⁿ → ∞` as `x → ∞`, for
every natural number `n`. This applies Mathlib's `Real.tendsto_exp_div_pow_atTop`. -/
theorem exp_beats_powers (n : ℕ) : Tendsto (fun x : ℝ => exp x / x ^ n) atTop atTop :=
  Real.tendsto_exp_div_pow_atTop n
-- @endregion

-- @region exponential_logarithmic_functions.compound_interest_limit
-- @provenance library
/-- **Compound interest and e:** `(1 + t/n)ⁿ → eᵗ` as `n → ∞`; with `t = 1` this is
`(1 + 1/n)ⁿ → e`. This applies Mathlib's `Real.tendsto_one_add_div_pow_exp`. -/
theorem compound_interest_limit (t : ℝ) :
    Tendsto (fun n : ℕ => (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
  Real.tendsto_one_add_div_pow_exp t
-- @endregion

end Lumenary.ExponentialLogarithmicFunctions
