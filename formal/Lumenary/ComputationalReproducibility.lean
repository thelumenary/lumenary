/-
The Lumenary — formal mathematics
Computational reproducibility: what it takes for a computation to count as evidence, and how
to turn a computation into a theorem.

What is proved here. (1) The classical error bound for floating-point recursive summation in the
standard model `fl(a + b) = (a + b)(1 + δ)`, `|δ| ≤ u`: the computed sum of `n + 1` numbers is
within `((1 + u)ⁿ - 1) · Σ |xᵢ|` of the true sum (`independent`). (2) Interval arithmetic is
sound: the interval sum and product of two intervals contain every sum and product of their
points (`independent`). (3) A numerical value made rigorous: `1.41421356 < √2 < 1.41421357`.
(4) Certificates: a Bézout identity certifies a gcd (`independent`), and Lucas's theorem turns a
primitive root into a primality certificate (Mathlib's `lucas_primality`), used here to certify
that 65537 is prime by two modular exponentiations. Floating-point hardware itself is not
modelled: the standard model is an assumption that IEEE 754 arithmetic satisfies.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Lumenary.ComputationalReproducibility

open Finset

/-! ### Floating-point summation in the standard model -/

-- @region computational_reproducibility.fsum
-- @provenance definition
/-- Recursive (left-to-right) summation in floating point, in the *standard model*: each
addition is exact up to a relative error, `fl(a + b) = (a + b)(1 + δ)`. The sequence `δ`
records the rounding error committed at each step; for IEEE double precision `|δ k| ≤ 2⁻⁵³`. -/
def fsum (x δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => (fsum x δ n + x (n + 1)) * (1 + δ (n + 1))
-- @endregion

-- @region computational_reproducibility.fsum_error
-- @provenance independent
/-- **Error bound for recursive summation.** If every rounding error satisfies `|δ k| ≤ u`, the
computed sum of `x 0, …, x n` differs from the exact sum by at most
`((1 + u)ⁿ - 1) · Σ |xᵢ|`. (For `n u < 1` this is at most `γₙ Σ |xᵢ|` with `γₙ = nu/(1 - nu)`,
the form in Higham's book.) Induction on `n`: the new error is the old one, amplified by
`1 + δ`, plus the rounding error `(sₙ + xₙ₊₁) δ` of the new addition. -/
theorem fsum_error (x δ : ℕ → ℝ) (u : ℝ) (hu : 0 ≤ u) (hδ : ∀ k, |δ k| ≤ u) (n : ℕ) :
    |fsum x δ n - ∑ i ∈ range (n + 1), x i| ≤
      ((1 + u) ^ n - 1) * ∑ i ∈ range (n + 1), |x i| := by
  induction n with
  | zero => simp [fsum]
  | succ n ih =>
    rw [sum_range_succ (fun i => x i) (n + 1), sum_range_succ (fun i => |x i|) (n + 1)]
    set s := ∑ i ∈ range (n + 1), x i with hs
    set A := ∑ i ∈ range (n + 1), |x i| with hA
    set e := fsum x δ n - s with he
    have hA0 : 0 ≤ A := sum_nonneg fun i _ => abs_nonneg (x i)
    have hsA : |s| ≤ A := abs_sum_le_sum_abs _ _
    have hpow : 1 ≤ (1 + u) ^ n := one_le_pow₀ (by linarith)
    have hd : |δ (n + 1)| ≤ u := hδ (n + 1)
    have h1d : |1 + δ (n + 1)| ≤ 1 + u := by
      calc |1 + δ (n + 1)| ≤ |(1 : ℝ)| + |δ (n + 1)| := abs_add_le _ _
        _ ≤ 1 + u := by rw [abs_one]; linarith
    have hsx : |s + x (n + 1)| ≤ A + |x (n + 1)| := by
      calc |s + x (n + 1)| ≤ |s| + |x (n + 1)| := abs_add_le _ _
        _ ≤ A + |x (n + 1)| := by linarith
    have key : fsum x δ (n + 1) - (s + x (n + 1)) =
        e * (1 + δ (n + 1)) + (s + x (n + 1)) * δ (n + 1) := by
      simp only [fsum, he]; ring
    rw [key]
    calc |e * (1 + δ (n + 1)) + (s + x (n + 1)) * δ (n + 1)|
        ≤ |e| * |1 + δ (n + 1)| + |s + x (n + 1)| * |δ (n + 1)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (((1 + u) ^ n - 1) * A) * (1 + u) + (A + |x (n + 1)|) * u :=
          add_le_add
            (mul_le_mul ih h1d (abs_nonneg _) (mul_nonneg (sub_nonneg.2 hpow) hA0))
            (mul_le_mul hsx hd (abs_nonneg _) (by positivity))
      _ ≤ ((1 + u) ^ (n + 1) - 1) * (A + |x (n + 1)|) := by
          have hx := abs_nonneg (x (n + 1))
          have hp : (1 + u) ^ (n + 1) = (1 + u) ^ n * (1 + u) := pow_succ _ _
          rw [hp]
          nlinarith [mul_nonneg hx (sub_nonneg.2 hpow), mul_nonneg hu hx,
            mul_nonneg (mul_nonneg hx (sub_nonneg.2 hpow)) hu]
-- @endregion

/-! ### Interval arithmetic -/

-- @region computational_reproducibility.ival
-- @provenance definition
/-- A closed interval with rational endpoints (in practice: floating-point numbers, which are
rationals). A real number `x` lies in `I` when `I.lo ≤ x ≤ I.hi`. -/
structure Ival where
  /-- The lower endpoint. -/
  lo : ℚ
  /-- The upper endpoint. -/
  hi : ℚ
-- @endregion

-- @region computational_reproducibility.ival_mem
-- @provenance definition
/-- Membership of a real number in an interval. -/
def Ival.Mem (I : Ival) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
-- @endregion

-- @region computational_reproducibility.ival_add
-- @provenance definition
/-- Interval addition: add the endpoints. -/
def Ival.add (I J : Ival) : Ival := ⟨I.lo + J.lo, I.hi + J.hi⟩
-- @endregion

-- @region computational_reproducibility.ival_mul
-- @provenance definition
/-- Interval multiplication: the smallest and largest of the four endpoint products. -/
def Ival.mul (I J : Ival) : Ival :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
-- @endregion

-- @region computational_reproducibility.add_mem
-- @provenance independent
/-- **Soundness of interval addition**: if `x ∈ I` and `y ∈ J` then `x + y ∈ I + J`. -/
theorem Ival.add_mem {I J : Ival} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Ival.Mem, Ival.add, Rat.cast_add]
  constructor <;> linarith
-- @endregion

-- @region computational_reproducibility.mul_mem
-- @provenance independent
/-- **Soundness of interval multiplication** (the "fundamental theorem of interval arithmetic"
for `×`): if `x ∈ [a, b]` and `y ∈ [c, d]` then `x y` lies between the least and the greatest
of `ac, ad, bc, bd`. For the lower bound: if `y ≥ 0` then `xy ≥ ay`, and `ay ≥ ac` or `ay ≥ ad`
according to the sign of `a`; if `y ≤ 0` argue with `b` instead. The upper bound is symmetric. -/
theorem Ival.mul_mem {I J : Ival} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Ival.Mem, Ival.mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  set a : ℝ := (I.lo : ℝ)
  set b : ℝ := (I.hi : ℝ)
  set c : ℝ := (J.lo : ℝ)
  set d : ℝ := (J.hi : ℝ)
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · rcases le_total 0 a with ha | ha
      · exact min_le_of_left_le (min_le_of_left_le (by nlinarith))
      · exact min_le_of_left_le (min_le_of_right_le (by nlinarith))
    · rcases le_total 0 b with hb | hb
      · exact min_le_of_right_le (min_le_of_left_le (by nlinarith))
      · exact min_le_of_right_le (min_le_of_right_le (by nlinarith))
  · rcases le_total 0 y with hy0 | hy0
    · rcases le_total 0 b with hb | hb
      · exact le_max_of_le_right (le_max_of_le_right (by nlinarith))
      · exact le_max_of_le_right (le_max_of_le_left (by nlinarith))
    · rcases le_total 0 a with ha | ha
      · exact le_max_of_le_left (le_max_of_le_right (by nlinarith))
      · exact le_max_of_le_left (le_max_of_le_left (by nlinarith))
-- @endregion

/-! ### A numerical value as a theorem -/

-- @region computational_reproducibility.sqrt_two_bounds
-- @provenance independent
/-- The numerical claim "`√2 = 1.41421356…`" as a theorem with explicit bounds. The proof is
exact rational arithmetic: `1.41421356² < 2 < 1.41421357²`. -/
theorem sqrt_two_bounds : (1.41421356 : ℝ) < √2 ∧ √2 < 1.41421357 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
-- @endregion

/-! ### Certificates -/

-- @region computational_reproducibility.gcd_certificate
-- @provenance independent
/-- **A Bézout identity certifies a gcd.** If `d ≥ 0` divides `a` and `b`, and `d = a x + b y`
for some integers `x, y`, then `d = gcd(a, b)`. A program that outputs `(d, x, y)` can thus be
checked with two divisions and two multiplications, without trusting the program. -/
theorem gcd_certificate {a b d x y : ℤ} (hd : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hbez : a * x + b * y = d) : d = Int.gcd a b := by
  have h1 : d ∣ (Int.gcd a b : ℤ) := Int.dvd_coe_gcd hda hdb
  have h2 : (Int.gcd a b : ℤ) ∣ d := by
    rw [← hbez]
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) _)
  exact Int.dvd_antisymm hd (Int.natCast_nonneg _) h1 h2
-- @endregion

-- @region computational_reproducibility.lucas_certificate
-- @provenance library
/-- **Lucas's primality certificate.** If `a^(p-1) = 1` in `ZMod p` but `a^((p-1)/q) ≠ 1` for
every prime `q ∣ p - 1`, then `p` is prime. Checking the certificate `(a, factorisation of p - 1)`
needs only modular exponentiations. This applies Mathlib's `lucas_primality`. -/
theorem lucas_certificate (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : p.Prime :=
  lucas_primality p a ha hd
-- @endregion

-- @region computational_reproducibility.prime_65537
-- @provenance independent
/-- `65537 = 2¹⁶ + 1` is prime, certified by `a = 3`: since `p - 1 = 2¹⁶`, the only prime
`q` is `2`, and the certificate consists of `3^(2¹⁶) ≡ 1` and `3^(2¹⁵) ≡ -1 (mod 65537)`.
The two exponentiations are evaluated exactly by the kernel's arithmetic on natural numbers. -/
theorem prime_65537 : Nat.Prime 65537 := by
  have hcast : ∀ n : ℕ, (3 : ZMod 65537) ^ n = ((3 ^ n % 65537 : ℕ) : ZMod 65537) := by
    intro n; rw [ZMod.natCast_mod]; push_cast; rfl
  apply lucas_certificate 65537 3
  · have h : 3 ^ 65536 % 65537 = 1 := by decide +kernel
    rw [hcast, h]; rfl
  · intro q hq hdvd
    have h2 : q = 2 := by
      have : q ∣ 2 ^ 16 := by simpa using hdvd
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow this)
    subst h2
    have h : 3 ^ 32768 % 65537 = 65536 := by decide +kernel
    rw [hcast, h]; decide
-- @endregion

end Lumenary.ComputationalReproducibility
