/-
The Lumenary — formal mathematics
Recurrences and generating functions: second-order linear recurrences and their characteristic
roots, Binet's formula, the Tower of Hanoi and a divide-and-conquer recurrence, formal power
series (the generating function of the Fibonacci numbers, and a divergent series that is still
invertible), Catalan numbers, and big-O estimates.

What is proved here and what Mathlib provides. The *independent* declarations follow the
lesson's proofs: geometric sequences `rⁿ` solve `aₙ₊₂ = p aₙ₊₁ + q aₙ` exactly when `r` is a
root of `x² − p x − q`; solutions are determined by two initial values (a two-step induction);
hence every solution is `A rⁿ + B sⁿ` when the roots are distinct, which gives Binet's formula.
The Fibonacci generating function identity `(1 − X − X²) F(X) = X` is checked coefficient by
coefficient in Mathlib's ring of formal power series `ℚ⟦X⟧`, where no question of convergence
arises. The *library* declarations cite Mathlib's general theory of linear recurrences
(`LinearRecurrence`), its own Binet formula `Real.coe_fib_eq`, the geometric series in `S⟦X⟧`,
and the Catalan number formula `catalan_eq_centralBinom_div`.
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Lumenary.RecurrencesGeneratingFunctions

open Real Filter Asymptotics

/-! ### Second-order linear recurrences -/

-- @region recurrences_generating_functions.is_sol
-- @provenance definition
/-- `IsSol p q a` says that the real sequence `a` satisfies the second-order linear recurrence
with constant coefficients `aₙ₊₂ = p · aₙ₊₁ + q · aₙ` for every `n`. Its characteristic
polynomial is `x² − p x − q`. -/
def IsSol (p q : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n, a (n + 2) = p * a (n + 1) + q * a n
-- @endregion

-- @region recurrences_generating_functions.is_sol_geom
-- @provenance independent
/-- **Guess an exponential.** If `r` is a root of the characteristic polynomial, `r² = p r + q`,
then `aₙ = rⁿ` solves the recurrence: `rⁿ⁺² = rⁿ · r² = rⁿ (p r + q) = p rⁿ⁺¹ + q rⁿ`. -/
theorem isSol_geom {p q r : ℝ} (hr : r ^ 2 = p * r + q) : IsSol p q (fun n => r ^ n) := by
  intro n
  calc r ^ (n + 2) = r ^ n * r ^ 2 := by ring
    _ = r ^ n * (p * r + q) := by rw [hr]
    _ = p * r ^ (n + 1) + q * r ^ n := by ring
-- @endregion

-- @region recurrences_generating_functions.is_sol_add_smul
-- @provenance independent
/-- **Linearity.** If `a` and `b` solve the recurrence, so does every combination `A a + B b`.
So the solutions form a vector space. -/
theorem isSol_add_smul {p q : ℝ} {a b : ℕ → ℝ} (ha : IsSol p q a) (hb : IsSol p q b)
    (A B : ℝ) : IsSol p q (fun n => A * a n + B * b n) := by
  intro n
  simp only
  rw [ha n, hb n]
  ring
-- @endregion

-- @region recurrences_generating_functions.is_sol_unique
-- @provenance independent
/-- **Two initial values determine a solution.** If `a` and `b` solve the same recurrence and
agree at `0` and `1`, they agree everywhere. The induction carries *two* consecutive values at
once: from `aₙ = bₙ` and `aₙ₊₁ = bₙ₊₁` the recurrence gives `aₙ₊₂ = bₙ₊₂`. -/
theorem isSol_unique {p q : ℝ} {a b : ℕ → ℝ} (ha : IsSol p q a) (hb : IsSol p q b)
    (h0 : a 0 = b 0) (h1 : a 1 = b 1) : ∀ n, a n = b n := by
  have key : ∀ n, a n = b n ∧ a (n + 1) = b (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [ha k, hb k, ih.1, ih.2]
  exact fun n => (key n).1
-- @endregion

-- @region recurrences_generating_functions.distinct_roots
-- @provenance independent
/-- **The characteristic-root theorem (distinct roots).** If `r ≠ s` are roots of
`x² − p x − q`, every solution has the form `aₙ = A rⁿ + B sⁿ`, with `A` and `B` fixed by the
initial values: `A = (a₁ − s a₀)/(r − s)` and `B = (r a₀ − a₁)/(r − s)`.
Proof: the right-hand side solves the recurrence (`isSol_geom`, `isSol_add_smul`) and has the
right values at `0` and `1`, so it equals `a` by `isSol_unique`. -/
theorem distinct_roots {p q r s : ℝ} (hrs : r ≠ s) (hr : r ^ 2 = p * r + q)
    (hs : s ^ 2 = p * s + q) {a : ℕ → ℝ} (ha : IsSol p q a) (n : ℕ) :
    a n = (a 1 - s * a 0) / (r - s) * r ^ n + (r * a 0 - a 1) / (r - s) * s ^ n := by
  have hne : r - s ≠ 0 := sub_ne_zero.mpr hrs
  refine isSol_unique ha (isSol_add_smul (isSol_geom hr) (isSol_geom hs) _ _) ?_ ?_ n
  · field_simp
    ring
  · field_simp
    ring
-- @endregion

-- @region recurrences_generating_functions.is_sol_repeated
-- @provenance independent
/-- **A repeated root.** If the characteristic polynomial is `(x − r)² = x² − 2r x + r²`, then
besides `rⁿ` the sequence `n rⁿ` is a solution of `aₙ₊₂ = 2r aₙ₊₁ − r² aₙ`. -/
theorem isSol_repeated (r : ℝ) : IsSol (2 * r) (-r ^ 2) (fun n => (n : ℝ) * r ^ n) := by
  intro n
  push_cast
  ring
-- @endregion

-- @region recurrences_generating_functions.three_pow_is_sol
-- @provenance independent
/-- `aₙ = 3ⁿ` solves `aₙ₊₂ = 5aₙ₊₁ − 6aₙ`, because `3` is a root of `x² − 5x + 6 = (x − 2)(x − 3)`:
`3² = 5 · 3 − 6`. An instance of `isSol_geom`. -/
theorem three_pow_isSol : IsSol 5 (-6) (fun n => (3 : ℝ) ^ n) :=
  isSol_geom (by norm_num)
-- @endregion

/-! ### Fibonacci numbers and Binet's formula -/

-- @region recurrences_generating_functions.fib_is_sol
-- @provenance independent
/-- The Fibonacci numbers (Mathlib's `Nat.fib`, with `F₀ = 0`, `F₁ = 1`) solve
`Fₙ₊₂ = Fₙ₊₁ + Fₙ`, i.e. `IsSol 1 1`. -/
theorem fib_isSol : IsSol 1 1 (fun n => (Nat.fib n : ℝ)) := by
  intro n
  simp only [one_mul]
  rw [Nat.fib_add_two, Nat.cast_add, add_comm]
-- @endregion

-- @region recurrences_generating_functions.binet
-- @provenance independent
/-- **Binet's formula**, `Fₙ = (φⁿ − ψⁿ)/√5` with `φ = (1 + √5)/2` and `ψ = (1 − √5)/2`, proved
as in the lesson: `φ` and `ψ` are the distinct roots of `x² − x − 1`, so `distinct_roots`
applies with `F₀ = 0` and `F₁ = 1`, and `φ − ψ = √5`. -/
theorem binet (n : ℕ) : (Nat.fib n : ℝ) = (goldenRatio ^ n - goldenConj ^ n) / √5 := by
  have hφ : goldenRatio ^ 2 = 1 * goldenRatio + 1 := by rw [goldenRatio_sq]; ring
  have hψ : goldenConj ^ 2 = 1 * goldenConj + 1 := by rw [goldenConj_sq]; ring
  have hne : goldenRatio ≠ goldenConj := by
    intro h
    have : goldenRatio - goldenConj = 0 := by rw [h, sub_self]
    rw [goldenRatio_sub_goldenConj] at this
    exact absurd this (by positivity)
  rw [distinct_roots hne hφ hψ fib_isSol n, goldenRatio_sub_goldenConj]
  simp only [Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one, mul_zero, sub_zero,
    zero_sub]
  ring
-- @endregion

-- @region recurrences_generating_functions.binet_library
-- @provenance library
/-- Binet's formula as it appears in Mathlib: `Real.coe_fib_eq`. Mathlib proves it with its
general `LinearRecurrence` theory, the same argument as `binet` above. -/
theorem binet_library (n : ℕ) : (Nat.fib n : ℝ) = (goldenRatio ^ n - goldenConj ^ n) / √5 :=
  Real.coe_fib_eq n
-- @endregion

-- @region recurrences_generating_functions.geom_sol_iff_root
-- @provenance library
/-- Mathlib's version of "guess an exponential", for a linear recurrence `E` of any order over
a commutative ring without zero divisors: `qⁿ` is a solution exactly when `q` is a root of the
characteristic polynomial. This applies `LinearRecurrence.geom_sol_iff_root_charPoly`. -/
theorem geom_sol_iff_root (E : LinearRecurrence ℝ) (q : ℝ) :
    E.IsSolution (fun n => q ^ n) ↔ E.charPoly.IsRoot q :=
  E.geom_sol_iff_root_charPoly q
-- @endregion

-- @region recurrences_generating_functions.fib_le_gold_pow
-- @provenance independent
/-- `Fₙ ≤ φⁿ` for every `n`, by a two-step induction that uses only `φ² = φ + 1`:
`Fₙ₊₂ = Fₙ₊₁ + Fₙ ≤ φⁿ⁺¹ + φⁿ = φⁿ (φ + 1) = φⁿ⁺²`. -/
theorem fib_le_gold_pow (n : ℕ) : (Nat.fib n : ℝ) ≤ goldenRatio ^ n := by
  have key : ∀ n, (Nat.fib n : ℝ) ≤ goldenRatio ^ n ∧
      (Nat.fib (n + 1) : ℝ) ≤ goldenRatio ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp [one_lt_goldenRatio.le]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      calc (Nat.fib (k + 2) : ℝ) = Nat.fib (k + 1) + Nat.fib k := by
            rw [Nat.fib_add_two, Nat.cast_add, add_comm]
        _ ≤ goldenRatio ^ (k + 1) + goldenRatio ^ k := add_le_add ih.2 ih.1
        _ = goldenRatio ^ k * (goldenRatio + 1) := by ring
        _ = goldenRatio ^ (k + 2) := by rw [← goldenRatio_sq]; ring
  exact (key n).1
-- @endregion

/-! ### Two recurrences from algorithms -/

-- @region recurrences_generating_functions.hanoi
-- @provenance definition
/-- The number of moves the recursive solution of the Tower of Hanoi makes with `n` discs:
move `n − 1` discs aside, move the largest disc, move the `n − 1` discs back on top. -/
def hanoi : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * hanoi n + 1
-- @endregion

-- @region recurrences_generating_functions.hanoi_eq
-- @provenance independent
/-- The Hanoi recurrence `Hₙ₊₁ = 2Hₙ + 1`, `H₀ = 0` has solution `Hₙ = 2ⁿ − 1`, stated without
subtraction as `Hₙ + 1 = 2ⁿ`: adding `1` turns the recurrence into `Hₙ₊₁ + 1 = 2 (Hₙ + 1)`. -/
theorem hanoi_eq (n : ℕ) : hanoi n + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc hanoi (k + 1) + 1 = 2 * (hanoi k + 1) := by simp only [hanoi]; ring
      _ = 2 ^ (k + 1) := by rw [ih]; ring
-- @endregion

-- @region recurrences_generating_functions.split_cost
-- @provenance definition
/-- The cost recurrence of a divide-and-conquer algorithm such as mergesort, with the halves
rounded down: `T(n) = 2 T(⌊n/2⌋) + n` for `n ≥ 2`, and `T(0) = T(1) = 0`. Lean accepts the
definition because `⌊n/2⌋ < n` when `n ≥ 2` (checked by `omega`). -/
def splitCost (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else 2 * splitCost (n / 2) + n
decreasing_by omega
-- @endregion

-- @region recurrences_generating_functions.split_cost_pow_two
-- @provenance independent
/-- **Unrolling a divide-and-conquer recurrence.** On powers of two, `T(2ᵏ) = k · 2ᵏ`: each of
the `k` levels of the recursion costs `2ᵏ` in total. So `T(n) = n log₂ n` when `n = 2ᵏ`. -/
theorem splitCost_pow_two (k : ℕ) : splitCost (2 ^ k) = k * 2 ^ k := by
  induction k with
  | zero => simp [splitCost]
  | succ k ih =>
    have hgt : ¬ 2 ^ (k + 1) ≤ 1 := by
      have : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; simp
    rw [splitCost]
    simp only [hgt, ite_false]
    rw [hhalf, ih]
    ring
-- @endregion

/-! ### Formal power series -/

section FormalPowerSeries

open PowerSeries

-- @region recurrences_generating_functions.geometric_series
-- @provenance library
/-- **The geometric series as an identity of formal power series**: in `ℚ⟦X⟧`,
`(1 + X + X² + ⋯)(1 − X) = 1`. No convergence is involved: the coefficients of the product are
finite sums. This applies Mathlib's `PowerSeries.mk_one_mul_one_sub_eq_one`. -/
theorem geometric_series : (mk 1 : ℚ⟦X⟧) * (1 - X) = 1 :=
  mk_one_mul_one_sub_eq_one ℚ
-- @endregion

-- @region recurrences_generating_functions.fib_gf
-- @provenance independent
/-- **The generating function of the Fibonacci numbers.** With `F(X) = Σ Fₙ Xⁿ` in `ℚ⟦X⟧`,
`(1 − X − X²) F(X) = X`, i.e. `F(X) = X / (1 − X − X²)`. Coefficient by coefficient: the
coefficient of `Xⁿ⁺²` is `Fₙ₊₂ − Fₙ₊₁ − Fₙ = 0`, and those of `1` and `X` are `F₀ = 0` and
`F₁ − F₀ = 1`. -/
theorem fib_gf :
    (1 - X - X ^ 2 : ℚ⟦X⟧) * mk (fun n => (Nat.fib n : ℚ)) = X := by
  ext n
  rw [sub_mul, sub_mul, one_mul, map_sub, map_sub, coeff_mk]
  rcases n with _ | _ | n
  · simp
  · simp [coeff_X, pow_two, mul_assoc]
  · rw [pow_two, mul_assoc, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_mk,
      coeff_mk, coeff_X, Nat.fib_add_two]
    simp only [Nat.cast_add, show n + 1 + 1 ≠ 1 by omega, ite_false]
    ring
-- @endregion

-- @region recurrences_generating_functions.factorial_series_is_unit
-- @provenance independent
/-- **A formal power series need not converge to be useful.** The series `Σ n! Xⁿ` converges
only at `X = 0`, yet it is invertible in `ℚ⟦X⟧`, because its constant term `0! = 1` is
invertible (Mathlib's criterion `PowerSeries.isUnit_iff_constantCoeff`). -/
theorem factorial_series_isUnit : IsUnit (mk (fun n => (Nat.factorial n : ℚ))) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp
-- @endregion

end FormalPowerSeries

/-! ### Catalan numbers -/

-- @region recurrences_generating_functions.catalan_formula
-- @provenance library
/-- **The Catalan formula** `Cₙ = C(2n, n)/(n + 1)`. Mathlib *defines* `catalan` by Segner's
recurrence `Cₙ₊₁ = Σᵢ Cᵢ Cₙ₋ᵢ` (`catalan_succ`) and proves this closed form in
`catalan_eq_centralBinom_div`; `Nat.centralBinom n` is `C(2n, n)`, and the division is exact. -/
theorem catalan_formula (n : ℕ) : catalan n = n.centralBinom / (n + 1) :=
  catalan_eq_centralBinom_div n
-- @endregion

-- @region recurrences_generating_functions.catalan_five
-- @provenance independent
/-- A computation: `C₅ = 42` (the number of balanced strings of five pairs of brackets, and of
triangulations of a convex heptagon), evaluated from the closed form `C(10, 5)/6 = 252/6`. -/
theorem catalan_five : catalan 5 = 42 := by
  rw [catalan_formula]
  decide
-- @endregion

/-! ### Growth rates -/

-- @region recurrences_generating_functions.quadratic_is_big_o
-- @provenance independent
/-- `3n² + 5n = O(n²)`: for `n ≥ 1`, `5n ≤ 5n²`, so `3n² + 5n ≤ 8n²`. The constant `8` and the
threshold `1` are witnesses; big-O hides both. -/
theorem quadratic_isBigO :
    (fun n : ℕ => (3 * (n : ℝ) ^ 2 + 5 * n)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  refine IsBigO.of_bound 8 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ n := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  nlinarith
-- @endregion

-- @region recurrences_generating_functions.fib_is_big_o
-- @provenance independent
/-- `Fₙ = O(φⁿ)`, from `fib_le_gold_pow` with constant `1`. (Binet's formula shows more:
`Fₙ = Θ(φⁿ)`, since `|ψⁿ| ≤ 1`.) -/
theorem fib_isBigO :
    (fun n : ℕ => (Nat.fib n : ℝ)) =O[atTop] (fun n : ℕ => goldenRatio ^ n) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul]
  exact fib_le_gold_pow n
-- @endregion

-- @region recurrences_generating_functions.poly_is_little_o_exp
-- @provenance library
/-- **Polynomials lose to exponentials**: `nᵏ = o(rⁿ)` for every `k` and every `r > 1`. This
applies Mathlib's `isLittleO_pow_const_const_pow_of_one_lt`. -/
theorem poly_isLittleO_exp (k : ℕ) {r : ℝ} (hr : 1 < r) :
    (fun n : ℕ => (n : ℝ) ^ k) =o[atTop] (fun n : ℕ => r ^ n) :=
  isLittleO_pow_const_const_pow_of_one_lt k hr
-- @endregion

end Lumenary.RecurrencesGeneratingFunctions
