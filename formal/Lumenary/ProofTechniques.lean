/-
The Lumenary — formal mathematics
Proof techniques: direct proof, proof by cases, contrapositive, contradiction, ordinary and
strong induction, and the well-ordering principle.

Proved here (`@provenance independent`), mirroring the lesson's human proofs: odd + odd is even
(direct); `n(n + 1)` is even (cases); if `n²` is even then `n` is even (contrapositive); Euclid's
theorem that every finite set of primes misses a prime (contradiction); `a² = 2b²` forces `b = 0`,
i.e. √2 is irrational (infinite descent, a form of strong induction); Gauss's formula
`1 + 2 + ⋯ + n = n(n + 1)/2` and `1 + 3 + ⋯ + (2n − 1) = n²` (induction); every amount of at least
8 is a sum of 3s and 5s (strong induction); a fake theorem whose inductive step works but whose
base case fails; and the cycle "ordinary induction ⇒ strong induction ⇒ well-ordering ⇒ ordinary
induction".

From the library (`@provenance library`): `Int.even_pow`, `Nat.exists_infinite_primes`,
`Finset.sum_range_id_mul_two` and `Nat.strong_induction_on`. In Lean, ordinary induction on `ℕ`
is not an axiom added later: it is the *recursor* that comes with the inductive definition of `ℕ`.
-/
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Lumenary.ProofTechniques

open Finset

/-! ### Direct proof and proof by cases -/

-- @region proof_techniques.odd_add_odd
-- @provenance independent
/-- **Direct proof.** The sum of two odd integers is even: if `m = 2a + 1` and `n = 2b + 1`, then
`m + n = 2(a + b + 1)`. (Mathlib's `Even k` means `k = r + r` for some `r`.) -/
theorem odd_add_odd {m n : ℤ} (hm : Odd m) (hn : Odd n) : Even (m + n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  exact ⟨a + b + 1, by ring⟩
-- @endregion

-- @region proof_techniques.dvd_trans
-- @provenance independent
/-- **Direct proof.** Divisibility is transitive: if `b = a·k` and `c = b·l` then `c = a·(k·l)`. -/
theorem dvd_trans {a b c : ℤ} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨l, rfl⟩ := hbc
  exact ⟨k * l, by ring⟩
-- @endregion

-- @region proof_techniques.even_mul_succ
-- @provenance independent
/-- **Proof by cases.** For every integer `n`, the product `n(n + 1)` is even.
Case 1: `n = 2k` is even, so `n(n + 1) = 2·(k(n + 1))`.
Case 2: `n = 2k + 1` is odd, so `n + 1 = 2(k + 1)` and `n(n + 1) = 2·(n(k + 1))`. -/
theorem even_mul_succ (n : ℤ) : Even (n * (n + 1)) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n + 1), by rw [hk]; ring⟩
  · exact ⟨n * (k + 1), by rw [hk]; ring⟩
-- @endregion

/-! ### Contrapositive -/

-- @region proof_techniques.odd_sq_of_odd
-- @provenance independent
/-- The square of an odd integer is odd: `(2k + 1)² = 2(2k² + 2k) + 1`. -/
theorem odd_sq_of_odd {n : ℤ} (h : Odd n) : Odd (n ^ 2) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨2 * k ^ 2 + 2 * k, by ring⟩
-- @endregion

-- @region proof_techniques.even_of_even_sq
-- @provenance independent
/-- **Proof by contrapositive.** If `n²` is even, then `n` is even. We prove the contrapositive
instead: if `n` is not even, it is odd, so `n²` is odd (`odd_sq_of_odd`), hence not even. -/
theorem even_of_even_sq (n : ℤ) (h : Even (n ^ 2)) : Even n := by
  by_contra hn
  have hodd : Odd (n ^ 2) := odd_sq_of_odd (Int.not_even_iff_odd.mp hn)
  exact (Int.not_even_iff_odd.mpr hodd) h
-- @endregion

-- @region proof_techniques.even_of_even_sq_library
-- @provenance library
/-- The same theorem from Mathlib's `Int.even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0`. -/
theorem even_of_even_sq_library (n : ℤ) (h : Even (n ^ 2)) : Even n :=
  (Int.even_pow.mp h).1
-- @endregion

/-! ### Contradiction: Euclid's theorem -/

-- @region proof_techniques.exists_prime_not_mem
-- @provenance independent
/-- **Euclid's theorem.** Every finite set `S` of primes misses some prime.
Let `N = (∏ p ∈ S, p) + 1` and let `q` be the smallest factor of `N` that is bigger than `1`
(it is prime). If `q` were in `S`, it would divide both the product and `N`, hence their
difference `1` — a contradiction. Note that `N` itself need not be prime. -/
theorem exists_prime_not_mem (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ q, q.Prime ∧ q ∉ S := by
  have hpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  have hN : (∏ p ∈ S, p) + 1 ≠ 1 := by omega
  refine ⟨Nat.minFac ((∏ p ∈ S, p) + 1), Nat.minFac_prime hN, fun hmem => ?_⟩
  have hdvd_prod : Nat.minFac ((∏ p ∈ S, p) + 1) ∣ ∏ p ∈ S, p := Finset.dvd_prod_of_mem _ hmem
  have hdvd_N := Nat.minFac_dvd ((∏ p ∈ S, p) + 1)
  have hdvd_one : Nat.minFac ((∏ p ∈ S, p) + 1) ∣ 1 := (Nat.dvd_add_right hdvd_prod).mp hdvd_N
  exact (Nat.minFac_prime hN).one_lt.ne' (Nat.dvd_one.mp hdvd_one)
-- @endregion

-- @region proof_techniques.exists_infinite_primes
-- @provenance library
/-- There are primes as large as we like: Mathlib's `Nat.exists_infinite_primes`, proved with
the smallest prime factor of `n! + 1`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
-- @endregion

-- @region proof_techniques.sq_eq_two_mul_sq
-- @provenance independent
/-- **√2 is irrational**, in the form: if `a² = 2b²` for natural numbers `a, b`, then `b = 0`.
Proof by *infinite descent* (strong induction on `b`): `a²` is even, so `a = 2c`; then `b² = 2c²`,
so `b = 2d`; then `c² = 2d²` is a smaller solution, and by the induction hypothesis `d = 0`, so
`b = 0`. (Evenness of a square is Mathlib's `Nat.even_pow`; the lesson proves it as Theorem 4.) -/
theorem sq_eq_two_mul_sq (a b : ℕ) (h : a ^ 2 = 2 * b ^ 2) : b = 0 := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    have ha : Even a := (Nat.even_pow.mp ⟨b ^ 2, by rw [h]; ring⟩).1
    obtain ⟨c, rfl⟩ := ha
    have hb2 : b ^ 2 = 2 * c ^ 2 := by nlinarith
    have hb : Even b := (Nat.even_pow.mp ⟨c ^ 2, by rw [hb2]; ring⟩).1
    obtain ⟨d, rfl⟩ := hb
    have hc : c ^ 2 = 2 * d ^ 2 := by nlinarith
    by_contra hne
    have hd : d = 0 := ih d (by omega) c hc
    omega
-- @endregion

/-! ### Induction -/

-- @region proof_techniques.gauss_sum
-- @provenance independent
/-- **Gauss's formula, by induction:** `2·(0 + 1 + ⋯ + n) = n(n + 1)`.
Base case: both sides are `0`. Inductive step: if `2·(0 + ⋯ + n) = n(n + 1)`, then
`2·(0 + ⋯ + n + (n + 1)) = n(n + 1) + 2(n + 1) = (n + 1)(n + 2)`. -/
theorem gauss_sum (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc 2 * ∑ i ∈ range (n + 1 + 1), i
        = 2 * ∑ i ∈ range (n + 1), i + 2 * (n + 1) := by rw [sum_range_succ, mul_add]
      _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
      _ = (n + 1) * (n + 1 + 1) := by ring
-- @endregion

-- @region proof_techniques.gauss_sum_library
-- @provenance library
/-- Mathlib's version, `Finset.sum_range_id_mul_two : (∑ i ∈ range n, i) * 2 = n * (n - 1)`. -/
theorem gauss_sum_library (n : ℕ) : (∑ i ∈ range n, i) * 2 = n * (n - 1) :=
  sum_range_id_mul_two n
-- @endregion

-- @region proof_techniques.sum_odd
-- @provenance independent
/-- **The odd numbers add up to squares:** `1 + 3 + ⋯ + (2n − 1) = n²`, by induction.
The inductive step is `n² + (2n + 1) = (n + 1)²`. -/
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ih]; ring
-- @endregion

-- @region proof_techniques.stamps
-- @provenance independent
/-- **Strong induction.** Every whole number `n ≥ 8` is a sum of 3s and 5s.
The cases `8 = 3 + 5`, `9 = 3 + 3 + 3` and `10 = 5 + 5` start things off; for `n ≥ 11` the
number `n − 3 ≥ 8` is smaller, so (strong induction hypothesis) it is `3a + 5b`, and then
`n = 3(a + 1) + 5b`. The step reaches back *three* places, which ordinary induction cannot do
directly. -/
theorem stamps (n : ℕ) (hn : 8 ≤ n) : ∃ a b : ℕ, n = 3 * a + 5 * b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 8 ∨ n = 9 ∨ n = 10 ∨ 11 ≤ n by omega) with h | h | h | h
    · exact ⟨1, 1, by omega⟩
    · exact ⟨3, 0, by omega⟩
    · exact ⟨0, 2, by omega⟩
    · obtain ⟨a, b, hab⟩ := ih (n - 3) (by omega) (by omega)
      exact ⟨a + 1, b, by omega⟩
-- @endregion

/-! ### Why the base case matters -/

-- @region proof_techniques.false_step_holds
-- @provenance independent
/-- A **fake induction**: *if* `n² + n + 1` were even, *then* `(n + 1)² + (n + 1) + 1` would be
even too, because the second number is the first plus `2(n + 1)`. The inductive step is fine… -/
theorem false_step_holds (n : ℕ) (h : Even (n ^ 2 + n + 1)) :
    Even ((n + 1) ^ 2 + (n + 1) + 1) := by
  have e : (n + 1) ^ 2 + (n + 1) + 1 = (n ^ 2 + n + 1) + 2 * (n + 1) := by ring
  rw [e]
  exact h.add (even_two_mul (n + 1))
-- @endregion

-- @region proof_techniques.never_even
-- @provenance independent
/-- …but the base case fails, and in fact the claim is false for **every** `n`: `n² + n = n(n + 1)`
is even (it is a product of consecutive numbers), so `n² + n + 1` is odd. -/
theorem never_even (n : ℕ) : ¬ Even (n ^ 2 + n + 1) := by
  have h : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  have e : n ^ 2 + n + 1 = n * (n + 1) + 1 := by ring
  rw [e, Nat.even_add_one]
  exact not_not.mpr h
-- @endregion

/-! ### Three equivalent principles -/

-- @region proof_techniques.ordinary_induction
-- @provenance definition
/-- The principle of **ordinary induction** for `ℕ`, stated as a proposition. -/
def OrdinaryInduction : Prop :=
  ∀ P : ℕ → Prop, P 0 → (∀ n, P n → P (n + 1)) → ∀ n, P n
-- @endregion

-- @region proof_techniques.strong_induction
-- @provenance definition
/-- The principle of **strong induction**: if `P n` follows whenever `P k` holds for all `k < n`,
then `P n` holds for every `n`. (No separate base case: for `n = 0` there are no `k < 0`.) -/
def StrongInduction : Prop :=
  ∀ P : ℕ → Prop, (∀ n, (∀ k < n, P k) → P n) → ∀ n, P n
-- @endregion

-- @region proof_techniques.well_ordering
-- @provenance definition
/-- The **well-ordering principle**: every non-empty set of natural numbers has a least element. -/
def WellOrdering : Prop :=
  ∀ S : Set ℕ, S.Nonempty → ∃ m ∈ S, ∀ k ∈ S, m ≤ k
-- @endregion

-- @region proof_techniques.ordinary_induction_holds
-- @provenance library
/-- Ordinary induction holds: it is the recursor `Nat.rec` that comes with the definition of `ℕ`. -/
theorem ordinaryInduction_holds : OrdinaryInduction :=
  fun _ h0 hs n => Nat.rec h0 hs n
-- @endregion

-- @region proof_techniques.strong_of_ordinary
-- @provenance independent
/-- **Ordinary ⇒ strong induction.** Apply ordinary induction to the stronger statement
`Q n := ∀ k < n, P k`. `Q 0` is vacuous; and if `Q n` holds then `P n` holds by the hypothesis,
so `Q (n + 1)` holds. Finally `P n` follows from `Q (n + 1)`.
(All three principles are theorems about `ℕ` in Lean; what these proofs show is that each one can
be *derived* from the previous one, using only basic arithmetic facts.) -/
theorem strong_of_ordinary (ind : OrdinaryInduction) : StrongInduction := by
  intro P h n
  have hQ : ∀ m, ∀ k < m, P k := by
    refine ind (fun m => ∀ k < m, P k) (fun k hk => absurd hk (Nat.not_lt_zero k)) ?_
    intro m hm k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · exact hm k hlt
    · rw [heq]; exact h m hm
  exact hQ (n + 1) n (Nat.lt_succ_self n)
-- @endregion

-- @region proof_techniques.well_ordering_of_strong
-- @provenance independent
/-- **Strong induction ⇒ well-ordering.** Suppose `S` had no least element. By strong induction,
no `n` is in `S`: if all `k < n` are outside `S` and `n ∈ S`, then `n` would be the least element.
So `S` is empty, contradicting the hypothesis. -/
theorem wellOrdering_of_strong (sind : StrongInduction) : WellOrdering := by
  intro S hne
  by_contra hno
  push Not at hno
  have hout : ∀ n, n ∉ S := by
    refine sind (fun n => n ∉ S) ?_
    intro n ih hn
    obtain ⟨k, hkS, hkn⟩ := hno n hn
    exact ih k hkn hkS
  obtain ⟨x, hx⟩ := hne
  exact hout x hx
-- @endregion

-- @region proof_techniques.ordinary_of_well_ordering
-- @provenance independent
/-- **Well-ordering ⇒ ordinary induction.** If `P 0` and `P n → P (n + 1)`, but `P` failed
somewhere, let `m` be the *least* failure. `m ≠ 0` because `P 0` holds, so `m = j + 1`; and `j < m`
means `P j` holds, hence `P (j + 1) = P m` holds — a contradiction. -/
theorem ordinary_of_wellOrdering (wo : WellOrdering) : OrdinaryInduction := by
  intro P h0 hs n
  by_contra hn
  obtain ⟨m, hm, hmin⟩ := wo {k | ¬ P k} ⟨n, hn⟩
  cases m with
  | zero => exact hm h0
  | succ j =>
    have hj : P j := by
      by_contra hj
      have := hmin j hj
      omega
    exact hm (hs j hj)
-- @endregion

end Lumenary.ProofTechniques
