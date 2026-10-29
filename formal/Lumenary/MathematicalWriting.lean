/-
The Lumenary — formal mathematics
Mathematical writing: what a proof assistant forces a writer to make explicit.

A formal statement must declare every symbol and its type, state every hypothesis, fix the order
of the quantifiers, and say whether a claim is proved, cited or merely stated. This module
illustrates each point with small, genuine theorems:

* the domain is part of the statement (`x² = 4 → x = 2` holds in `ℕ` but not in `ℤ`);
* quantifier order changes meaning (`∀ n, ∃ m, n < m` is true, `∃ m, ∀ n, n < m` is false);
* hypotheses matter (Euclid's lemma needs primality: a counterexample without it, and the
  library theorem `Nat.Prime.dvd_mul` with it);
* a carefully structured proof of Euclid's theorem on primes, with the common misstatement of
  it ("the product of the first primes plus one is prime") refuted;
* the status of a claim: Goldbach's conjecture is *defined* as a proposition (`def … : Prop`),
  not asserted, and only a finite range is proved, by computation.

Provenance: everything is proved here (`independent`) except Euclid's lemma and Euclid's theorem
in their library form (`Nat.Prime.dvd_mul`, `Nat.exists_infinite_primes`).
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

namespace Lumenary.MathematicalWriting

/-! ### The domain is part of the statement -/

-- @region mathematical_writing.sq_eq_four_nat
-- @provenance independent
/-- Over the natural numbers, `x² = 4` forces `x = 2`. (If `x ≥ 3` then `x² ≥ 9`; the cases
`x = 0, 1, 2` are checked one by one.) -/
theorem sq_eq_four_nat (x : ℕ) (h : x ^ 2 = 4) : x = 2 := by
  have hx : x ≤ 2 := by
    by_contra hc
    have h3 : 3 ≤ x := by omega
    have : 3 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left h3 2
    omega
  interval_cases x <;> simp_all
-- @endregion

-- @region mathematical_writing.sq_eq_four_int
-- @provenance independent
/-- Over the integers the same sentence is false: `x = -2` is a counterexample. Writing
"if `x² = 4` then `x = 2`" without saying where `x` lives leaves the reader to guess which of
these two statements is meant. -/
theorem sq_eq_four_int : ¬ ∀ x : ℤ, x ^ 2 = 4 → x = 2 := by
  intro h
  have := h (-2) (by norm_num)
  norm_num at this
-- @endregion

/-! ### Quantifier order -/

-- @region mathematical_writing.forall_exists_gt
-- @provenance independent
/-- "For every number there is a bigger one": true (take `n + 1`). -/
theorem forall_exists_gt : ∀ n : ℕ, ∃ m : ℕ, n < m :=
  fun n => ⟨n + 1, Nat.lt_succ_self n⟩
-- @endregion

-- @region mathematical_writing.not_exists_forall_gt
-- @provenance independent
/-- "There is a number bigger than every number": false (it would be bigger than itself).
The same words in a different order — so in prose, the order of "for every" and "there is"
must be unmistakable. -/
theorem not_exists_forall_gt : ¬ ∃ m : ℕ, ∀ n : ℕ, n < m :=
  fun ⟨m, hm⟩ => lt_irrefl m (hm m)
-- @endregion

/-! ### Every hypothesis matters -/

-- @region mathematical_writing.dvd_mul_needs_prime
-- @provenance independent
/-- Without primality, "if `a ∣ bc` then `a ∣ b` or `a ∣ c`" is false: `6 ∣ 4 · 9`, but `6` divides
neither `4` nor `9`. -/
theorem dvd_mul_needs_prime : ¬ ∀ a b c : ℕ, a ∣ b * c → a ∣ b ∨ a ∣ c := by
  intro h
  have h' := h 6 4 9 (by norm_num)
  revert h'
  decide
-- @endregion

-- @region mathematical_writing.euclid_lemma
-- @provenance library
/-- **Euclid's lemma**, with its hypothesis: if a prime divides a product, it divides a factor.
This applies Mathlib's `Nat.Prime.dvd_mul`. -/
theorem euclid_lemma {p a b : ℕ} (hp : p.Prime) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.1 h
-- @endregion

/-! ### A structured proof, and a common misstatement -/

-- @region mathematical_writing.exists_prime_gt
-- @provenance independent
/-- **Euclid's theorem, written with its structure visible.** For every `n` there is a prime
`p > n`.

*Proof.* Let `N = n! + 1`. Since `N ≥ 2`, it has a smallest prime factor `p`. Suppose, for a
contradiction, that `p ≤ n`. Then `p ∣ n!`, and `p ∣ N`, so `p ∣ N - n! = 1`, which is impossible
for a prime. Hence `p > n`. ∎

Note what the proof does **not** claim: `N` itself need not be prime. -/
theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ p.Prime := by
  -- Step 1: `N = n! + 1` is not `1`, so its smallest prime factor `p` is prime.
  have hN : n.factorial + 1 ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  have hprime : (n.factorial + 1).minFac.Prime := Nat.minFac_prime hN
  refine ⟨(n.factorial + 1).minFac, ?_, hprime⟩
  -- Step 2: suppose `p ≤ n`, for a contradiction.
  by_contra hle
  have hle' : (n.factorial + 1).minFac ≤ n := by omega
  -- Step 3: then `p` divides both `n!` and `n! + 1`, hence divides `1`.
  have h1 : (n.factorial + 1).minFac ∣ n.factorial := Nat.dvd_factorial hprime.pos hle'
  have h2 : (n.factorial + 1).minFac ∣ n.factorial + 1 := Nat.minFac_dvd _
  have h3 : (n.factorial + 1).minFac ∣ 1 := (Nat.dvd_add_right h1).1 h2
  -- Step 4: but a prime does not divide `1`.
  exact hprime.one_lt.ne' (Nat.dvd_one.1 h3)
-- @endregion

-- @region mathematical_writing.exists_infinite_primes
-- @provenance library
/-- The same theorem from Mathlib, `Nat.exists_infinite_primes` (with `≤` rather than `<`). -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
-- @endregion

-- @region mathematical_writing.primorial_plus_one_not_prime
-- @provenance independent
/-- **The common misstatement is false.** A frequently written version of Euclid's proof claims
that "the product of the first `k` primes, plus one, is prime". It is not:
`2 · 3 · 5 · 7 · 11 · 13 + 1 = 30031 = 59 · 509`. The correct claim is that this number has a
prime factor outside the list. -/
theorem primorial_plus_one_not_prime :
    2 * 3 * 5 * 7 * 11 * 13 + 1 = 59 * 509 ∧ ¬ Nat.Prime (2 * 3 * 5 * 7 * 11 * 13 + 1) := by
  constructor
  · norm_num
  · norm_num
-- @endregion

/-! ### Stating a conjecture without claiming it -/

-- @region mathematical_writing.goldbach_conjecture
-- @provenance definition
/-- **Goldbach's conjecture**, *stated* but not asserted: every even number greater than `2` is a
sum of two primes. Making it a `def … : Prop` records the statement precisely while claiming
nothing about its truth — the formal counterpart of writing "Conjecture" rather than "Theorem". -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n
-- @endregion

-- @region mathematical_writing.goldbach_up_to
-- @provenance independent
/-- **What is actually proved: a finite range.** Every even `n` with `2 < n ≤ 60` is a sum of
two primes, checked by computation (`decide`). This is evidence for the conjecture, and a
theorem about these finitely many cases — nothing more. -/
theorem goldbach_up_to_60 :
    ∀ n : ℕ, 2 < n → n ≤ 60 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have key : ∀ n < 61, 2 < n → n % 2 = 0 →
      ∃ p < n, Nat.Prime p ∧ Nat.Prime (n - p) := by
    decide
  intro n h2 h60 heven
  obtain ⟨p, hpn, hp, hq⟩ := key n (by omega) h2 (Nat.even_iff.1 heven)
  exact ⟨p, n - p, hp, hq, by omega⟩
-- @endregion

end Lumenary.MathematicalWriting
