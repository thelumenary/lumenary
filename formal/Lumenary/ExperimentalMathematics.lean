/-
The Lumenary — formal mathematics
Experimental mathematics: conjectures, counterexamples, integer relations and proofs.

What is proved here. Two famous conjectures refuted by computation, with the refutations
machine-checked: Fermat's claim that every `2^(2^n) + 1` is prime (Euler's factor 641, proved
here by Euler's own argument, without computing `2³²`), and Euler's sum-of-powers conjecture for
fifth powers (Lander and Parkin's counterexample). The notion of an integer relation, with a
relation that exists (for `φ², φ, 1`) and a proof that none exists for `√2, 1` — which needs
irrationality, not search. The analytic heart of the Bailey–Borwein–Plouffe formula: after
partial fractions, `∫₀¹ (16y - 16)/(y⁴ - 2y³ + 4y - 4) dy = π`, proved with the fundamental
theorem of calculus (`independent`). A bounded Collatz check, honestly separated from the
Collatz conjecture, which is only *stated*. Euler's evaluation `Σ 1/n² = π²/6`, first guessed
from numerics, is applied from Mathlib (`hasSum_zeta_two`). Not formalised: the step from the
BBP series to the integral (an exchange of sum and integral), PSLQ/LLL, and π(x) < li(x).
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp

namespace Lumenary.ExperimentalMathematics

open Real

/-! ### Fermat numbers and Euler's 641 -/

-- @region experimental_mathematics.fermat
-- @provenance definition
/-- The Fermat numbers `Fₙ = 2^(2^n) + 1`: 3, 5, 17, 257, 65537, … -/
def fermat (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1
-- @endregion

-- @region experimental_mathematics.fermat_prime_le_four
-- @provenance independent
/-- The evidence Fermat had: `F₀, …, F₄` are all prime (checked here by `norm_num`'s
certified primality test). -/
theorem fermat_prime_le_four (n : ℕ) (hn : n ≤ 4) : (fermat n).Prime := by
  interval_cases n <;> norm_num [fermat]
-- @endregion

-- @region experimental_mathematics.euler_641
-- @provenance independent
/-- **Euler (1732): `641 ∣ 2³² + 1`**, by Euler's argument rather than by computing `2³²`.
Since `641 = 5·2⁷ + 1 = 5⁴ + 2⁴`, modulo 641 we have `5·2⁷ = -1` and `5⁴ = -2⁴`. Hence
`2³² = 2⁴·2²⁸ = -5⁴·2²⁸ = -(5·2⁷)⁴ = -1`. -/
theorem euler_641 : (2 : ZMod 641) ^ 32 + 1 = 0 := by
  have h1 : (5 : ZMod 641) * 2 ^ 7 = -1 := by decide
  have h2 : (5 : ZMod 641) ^ 4 = -(2 ^ 4) := by decide
  calc (2 : ZMod 641) ^ 32 + 1 = -(5 ^ 4) * 2 ^ 28 + 1 := by rw [h2]; ring
    _ = -((5 * 2 ^ 7) ^ 4) + 1 := by ring
    _ = 0 := by rw [h1]; ring
-- @endregion

-- @region experimental_mathematics.fermat_conjecture_false
-- @provenance independent
/-- **Fermat's conjecture is false**: not every Fermat number is prime, because
`F₅ = 641 · 6700417`. Five cases of evidence did not make a theorem. -/
theorem fermat_conjecture_false : ¬ ∀ n, (fermat n).Prime := by
  intro h
  have h5 : fermat 5 = 641 * 6700417 := by norm_num [fermat]
  have := h 5
  rw [h5] at this
  exact Nat.not_prime_mul (by norm_num) (by norm_num) this
-- @endregion

/-! ### Euler's sum-of-powers conjecture -/

-- @region experimental_mathematics.euler_conjecture_five
-- @provenance definition
/-- Euler's sum-of-powers conjecture for fifth powers (1769): no fifth power is a sum of four
positive fifth powers. Defined as a proposition — stating it is not asserting it. -/
def EulerConjectureFive : Prop :=
  ∀ a b c d e : ℕ, 0 < a → 0 < b → 0 < c → 0 < d → a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 ≠ e ^ 5
-- @endregion

-- @region experimental_mathematics.lander_parkin
-- @provenance independent
/-- **Lander and Parkin (1966)**, found by a computer search on a CDC 6600:
`27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵`. -/
theorem lander_parkin : 27 ^ 5 + 84 ^ 5 + 110 ^ 5 + 133 ^ 5 = 144 ^ 5 := by norm_num
-- @endregion

-- @region experimental_mathematics.euler_conjecture_five_false
-- @provenance independent
/-- Hence Euler's conjecture for fifth powers is false. One counterexample suffices. -/
theorem euler_conjecture_five_false : ¬ EulerConjectureFive := fun h =>
  h 27 84 110 133 144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) lander_parkin
-- @endregion

/-! ### Integer relations -/

-- @region experimental_mathematics.is_integer_relation
-- @provenance definition
/-- An **integer relation** for real numbers `x₀, …, xₙ₋₁` is a non-zero integer vector `a`
with `a₀x₀ + ⋯ + aₙ₋₁xₙ₋₁ = 0`. Algorithms such as PSLQ search for them numerically. -/
def IsIntegerRelation {n : ℕ} (x : Fin n → ℝ) (a : Fin n → ℤ) : Prop :=
  a ≠ 0 ∧ ∑ i, (a i : ℝ) * x i = 0
-- @endregion

-- @region experimental_mathematics.golden_relation
-- @provenance independent
/-- `(1, -1, -1)` is an integer relation for `(φ², φ, 1)`: the golden ratio satisfies
`φ² - φ - 1 = 0` (Mathlib's `goldenRatio_sq`). -/
theorem golden_relation :
    IsIntegerRelation ![goldenRatio ^ 2, goldenRatio, 1] ![1, -1, -1] := by
  refine ⟨fun h => by simpa using congrFun h 0, ?_⟩
  simp [Fin.sum_univ_three, goldenRatio_sq]
-- @endregion

-- @region experimental_mathematics.no_relation_sqrt_two
-- @provenance independent
/-- **No integer relation exists for `(√2, 1)`.** If `a₀√2 + a₁ = 0` with `a₀ ≠ 0` then `√2` would
be rational; if `a₀ = 0` then `a₁ = 0` too. Absence of relations is an irrationality statement:
a search can only rule out relations up to a size bound, while this needs a proof
(Mathlib's `irrational_sqrt_two`). -/
theorem no_relation_sqrt_two (a : Fin 2 → ℤ) : ¬ IsIntegerRelation ![√2, 1] a := by
  rintro ⟨hne, hsum⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hsum
  by_cases h0 : a 0 = 0
  · have h1 : a 1 = 0 := by
      rw [h0] at hsum
      simpa using hsum
    exact hne (funext fun i => by fin_cases i <;> simp [h0, h1])
  · have hq : √2 = ((-(a 1) / a 0 : ℚ) : ℝ) := by
      have ha0 : (a 0 : ℝ) ≠ 0 := by exact_mod_cast h0
      push_cast
      field_simp
      linarith
    exact irrational_sqrt_two ⟨_, hq.symm⟩
-- @endregion

/-! ### The Bailey–Borwein–Plouffe formula: the integral -/

-- @region experimental_mathematics.bbp_integrand
-- @provenance definition
/-- The integrand to which the BBP series reduces after writing `1/(8k+j)` as an integral,
summing the geometric series and substituting `y = √2 x`. -/
noncomputable def bbpIntegrand (y : ℝ) : ℝ := (16 * y - 16) / (y ^ 4 - 2 * y ^ 3 + 4 * y - 4)
-- @endregion

-- @region experimental_mathematics.bbp_partial_fractions
-- @provenance independent
/-- Partial fractions: since `y⁴ - 2y³ + 4y - 4 = (y² - 2)(y² - 2y + 2)`,
`(16y - 16)/(y⁴ - 2y³ + 4y - 4) = 4y/(y² - 2) - (4y - 8)/(y² - 2y + 2)` whenever `y² ≠ 2`. -/
theorem bbp_partial_fractions (y : ℝ) (hy : y ^ 2 ≠ 2) :
    bbpIntegrand y = 4 * y / (y ^ 2 - 2) - (4 * y - 8) / (y ^ 2 - 2 * y + 2) := by
  have h1 : y ^ 2 - 2 ≠ 0 := sub_ne_zero.2 hy
  have h2 : y ^ 2 - 2 * y + 2 ≠ 0 := by nlinarith [sq_nonneg (y - 1)]
  have h3 : y ^ 4 - 2 * y ^ 3 + 4 * y - 4 = (y ^ 2 - 2) * (y ^ 2 - 2 * y + 2) := by ring
  rw [bbpIntegrand, h3, div_sub_div _ _ h1 h2]
  congr 1
  ring
-- @endregion

-- @region experimental_mathematics.bbp_integral
-- @provenance independent
/-- **`∫₀¹ (16y - 16)/(y⁴ - 2y³ + 4y - 4) dy = π`.** An antiderivative on `[0, 1]` is
`F(y) = 2 log(2 - y²) - 2 log(y² - 2y + 2) + 4 arctan(y - 1)`; its derivative is the integrand
by `bbp_partial_fractions`, and `F(1) - F(0) = 0 - 4 arctan(-1) = π`. Together with the
(unformalised) conversion of the series into this integral, this proves the BBP formula
`π = Σₖ 16⁻ᵏ (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))`. -/
theorem bbp_integral : ∫ y in (0 : ℝ)..1, bbpIntegrand y = π := by
  set F : ℝ → ℝ := fun y => 2 * log (2 - y ^ 2) - 2 * log (y ^ 2 - 2 * y + 2)
    + 4 * arctan (y - 1) with hF
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (bbpIntegrand y) y := by
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    obtain ⟨hy0, hy1⟩ := hy
    have hA : 0 < 2 - y ^ 2 := by nlinarith
    have hB : 0 < y ^ 2 - 2 * y + 2 := by nlinarith [sq_nonneg (y - 1)]
    have dA : HasDerivAt (fun y : ℝ => 2 - y ^ 2) (-(2 * y)) y := by
      simpa using (hasDerivAt_pow 2 y).const_sub (2 : ℝ)
    have dB : HasDerivAt (fun y : ℝ => y ^ 2 - 2 * y + 2) (2 * y - 2) y := by
      have := ((hasDerivAt_pow 2 y).sub ((hasDerivAt_id y).const_mul 2)).add_const (2 : ℝ)
      simpa using this
    have dC : HasDerivAt (fun y : ℝ => arctan (y - 1)) (1 / (1 + (y - 1) ^ 2) * 1) y :=
      ((hasDerivAt_id y).sub_const 1).arctan
    have dF := (((dA.log hA.ne').const_mul 2).sub ((dB.log hB.ne').const_mul 2)).add
      (dC.const_mul 4)
    convert dF using 1
    rw [bbp_partial_fractions y (by nlinarith)]
    have hC : 1 + (y - 1) ^ 2 = y ^ 2 - 2 * y + 2 := by ring
    have hA' : 2 - y ^ 2 ≠ 0 := hA.ne'
    have hA'' : y ^ 2 - 2 ≠ 0 := by linarith
    have hB' : y ^ 2 - 2 * y + 2 ≠ 0 := hB.ne'
    rw [hC]
    field_simp
    ring
  have hcont : ContinuousOn bbpIntegrand (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    obtain ⟨hy0, hy1⟩ := hy
    have h3 : y ^ 4 - 2 * y ^ 3 + 4 * y - 4 = (y ^ 2 - 2) * (y ^ 2 - 2 * y + 2) := by ring
    rw [h3]
    apply mul_ne_zero <;> nlinarith [sq_nonneg (y - 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hF]
  norm_num [arctan_neg, arctan_one]
  ring
-- @endregion

/-! ### Euler's numerical discovery, now a theorem -/

-- @region experimental_mathematics.basel
-- @provenance library
/-- **The Basel problem (Euler, 1734/35):** `Σ_{n ≥ 1} 1/n² = π²/6`. Euler first computed the sum
to several decimals with acceleration techniques and recognised `π²/6`; this applies Mathlib's
`hasSum_zeta_two`. (The `n = 0` term is `1/0 = 0` in Lean's conventions.) -/
theorem basel : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
-- @endregion

/-! ### A bounded check is not a conjecture -/

-- @region experimental_mathematics.collatz_step
-- @provenance definition
/-- One step of the Collatz map: halve even numbers, send odd `n` to `3n + 1`. -/
def collatzStep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1
-- @endregion

-- @region experimental_mathematics.collatz_conjecture
-- @provenance definition
/-- The **Collatz conjecture**: every positive integer reaches `1`. Stated, not asserted — it is
open. -/
def CollatzConjecture : Prop := ∀ n, 0 < n → ∃ k, collatzStep^[k] n = 1
-- @endregion

-- @region experimental_mathematics.reaches_one
-- @provenance definition
/-- A bounded search: does `n` reach `1` within `fuel` steps? -/
def reachesOne : ℕ → ℕ → Bool
  | 0, n => n == 1
  | fuel + 1, n => n == 1 || reachesOne fuel (collatzStep n)
-- @endregion

-- @region experimental_mathematics.reaches_one_sound
-- @provenance independent
/-- The search is sound: if it says yes, `n` really reaches `1`. Induction on the fuel. -/
theorem reachesOne_sound (fuel n : ℕ) (h : reachesOne fuel n = true) :
    ∃ k, collatzStep^[k] n = 1 := by
  induction fuel generalizing n with
  | zero => exact ⟨0, by simpa [reachesOne] using h⟩
  | succ fuel ih =>
    simp only [reachesOne, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih _ h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
-- @endregion

-- @region experimental_mathematics.collatz_up_to_500
-- @provenance independent
/-- **An exhaustive check with a stated bound:** every `n` with `1 ≤ n ≤ 500` reaches `1`.
The bounded search is run by the kernel (`decide +kernel`) and turned into a theorem by
`reachesOne_sound`. This says nothing about `n > 500`; `CollatzConjecture` stays open. -/
theorem collatz_up_to_500 (n : ℕ) (h0 : 0 < n) (h : n ≤ 500) :
    ∃ k, collatzStep^[k] n = 1 := by
  have hall : ∀ m < 500, reachesOne 150 (m + 1) = true := by decide +kernel
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact reachesOne_sound 150 _ (hall m (by omega))
-- @endregion

end Lumenary.ExperimentalMathematics
