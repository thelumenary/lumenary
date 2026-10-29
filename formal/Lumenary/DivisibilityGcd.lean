/-
The Lumenary — formal mathematics
Divisibility, Euclid's algorithm, Bézout's identity and unique factorisation.

Proved here (`@provenance independent`), following the lesson: a common divisor of `a` and `b`
divides every combination `ax + by`; division with remainder is unique; `a, b` and `b, a mod b`
have the same common divisors; our own implementation of **Euclid's algorithm** terminates and
computes the greatest common divisor; the **extended** algorithm produces Bézout coefficients;
**Euclid's lemma** (a prime dividing a product divides a factor), proved from our Bézout identity;
and the **fundamental theorem of arithmetic** — existence by strong induction, uniqueness (up to
order) by induction using Euclid's lemma; and the rule that a fraction in lowest terms has a
terminating decimal exactly when its denominator has no prime factors other than 2 and 5. We also check that unique factorisation genuinely
fails among the "Hilbert numbers" `1, 5, 9, 13, …`: `441 = 9 · 49 = 21 · 21`.

From the library (`@provenance library`): `Int.mul_ediv_add_emod`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`
(division with remainder), `Nat.gcd_eq_gcd_ab` (Bézout), `Nat.Prime.dvd_mul` (Euclid's lemma) and
`Nat.primeFactorsList_unique` (unique factorisation).
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Lumenary.DivisibilityGcd

/-! ### Divisibility and division with remainder -/

-- @region divisibility_gcd.dvd_linear_combination
-- @provenance independent
/-- If `d ∣ a` and `d ∣ b`, then `d` divides every integer combination `a·x + b·y`:
from `a = d·k` and `b = d·l` we get `a·x + b·y = d·(k·x + l·y)`. -/
theorem dvd_linear_combination {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) (x y : ℤ) :
    d ∣ a * x + b * y := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  exact ⟨k * x + l * y, by ring⟩
-- @endregion

-- @region divisibility_gcd.division_algorithm
-- @provenance library
/-- **Division with remainder** (existence): for `b > 0`, every integer `a` is `b·q + r` with
`0 ≤ r < b`. This assembles core Lean's `Int.mul_ediv_add_emod`, `Int.emod_nonneg` and
`Int.emod_lt_of_pos`, with `q = a / b` and `r = a % b`. -/
theorem division_algorithm (a b : ℤ) (hb : 0 < b) :
    ∃ q r : ℤ, a = b * q + r ∧ 0 ≤ r ∧ r < b :=
  ⟨a / b, a % b, (Int.mul_ediv_add_emod a b).symm, Int.emod_nonneg a hb.ne', Int.emod_lt_of_pos a hb⟩
-- @endregion

-- @region divisibility_gcd.division_unique
-- @provenance independent
/-- **Division with remainder** (uniqueness): if `b·q + r = b·q' + r'` with both remainders in
`[0, b)`, then `q = q'` and `r = r'`. Indeed `b·(q − q') = r' − r` lies strictly between `−b` and
`b`, and the only multiple of `b` there is `0`. -/
theorem division_unique {b q r q' r' : ℤ} (hb : 0 < b)
    (h : b * q + r = b * q' + r') (hr : 0 ≤ r) (hrb : r < b) (hr' : 0 ≤ r') (hrb' : r' < b) :
    q = q' ∧ r = r' := by
  have hq : q = q' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : b * q + b ≤ b * q' := by nlinarith
      linarith
    · have : b * q' + b ≤ b * q := by nlinarith
      linarith
  subst hq
  exact ⟨rfl, by linarith⟩
-- @endregion

/-! ### Euclid's algorithm -/

-- @region divisibility_gcd.common_divisors_mod
-- @provenance independent
/-- **The key step of Euclid's algorithm**: `a, b` and `b, a mod b` have exactly the same common
divisors, because `a = b·(a / b) + (a mod b)`. -/
theorem common_divisors_mod (a b d : ℕ) : (d ∣ a ∧ d ∣ b) ↔ (d ∣ b ∧ d ∣ a % b) := by
  have e : b * (a / b) + a % b = a := Nat.div_add_mod a b
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    rw [← e] at ha
    exact (Nat.dvd_add_right (Dvd.dvd.mul_right hb _)).mp ha
  · rintro ⟨hb, hr⟩
    refine ⟨?_, hb⟩
    rw [← e]
    exact Nat.dvd_add (Dvd.dvd.mul_right hb _) hr
-- @endregion

-- @region divisibility_gcd.euclid
-- @provenance definition
/-- **Euclid's algorithm**: `euclid a 0 = a`, and otherwise `euclid a b = euclid b (a mod b)`.
It terminates because the second argument strictly decreases (`a mod b < b`), and a decreasing
sequence of natural numbers cannot go on for ever. Lean checks this (`termination_by`). -/
def euclid : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)
-- @endregion

-- @region divisibility_gcd.euclid_spec
-- @provenance independent
/-- **Euclid's algorithm computes a greatest common divisor**: its output divides both inputs,
and every common divisor of the inputs divides the output. Proof by induction following the
recursion: when `b = 0` the output is `a`; otherwise apply `common_divisors_mod`. -/
theorem euclid_spec (a b : ℕ) :
    (euclid a b ∣ a ∧ euclid a b ∣ b) ∧ ∀ d, d ∣ a → d ∣ b → d ∣ euclid a b := by
  induction a, b using euclid.induct with
  | case1 a =>
    rw [euclid]
    exact ⟨⟨dvd_refl a, dvd_zero a⟩, fun d ha _ => ha⟩
  | case2 a b ih =>
    rw [euclid]
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih
    refine ⟨(common_divisors_mod a (b + 1) _).mpr ⟨h1, h2⟩, fun d ha hdb => ?_⟩
    exact h3 d hdb ((common_divisors_mod a (b + 1) d).mp ⟨ha, hdb⟩).2
-- @endregion

-- @region divisibility_gcd.euclid_eq_gcd
-- @provenance independent
/-- Our `euclid` agrees with Lean's `Nat.gcd`: two numbers that divide each other are equal. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := euclid_spec a b
  exact Nat.dvd_antisymm (Nat.dvd_gcd h1 h2) (h3 _ (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))
-- @endregion

-- @region divisibility_gcd.gcd_1071_462
-- @provenance independent
/-- The lesson's worked example: `gcd(1071, 462) = 21` (`1071 = 2·462 + 147`, `462 = 3·147 + 21`,
`147 = 7·21`), computed by Lean's kernel. -/
theorem gcd_1071_462 : euclid 1071 462 = 21 := by
  rw [euclid_eq_gcd]
  rfl
-- @endregion

/-! ### Bézout's identity -/

-- @region divisibility_gcd.xgcd
-- @provenance definition
/-- The **extended Euclidean algorithm**: integers `(x, y)` with `a·x + b·y = gcd(a, b)`.
If `b = 0` take `(1, 0)`. Otherwise, from `b·x' + (a mod b)·y' = g` and
`a mod b = a − b·(a / b)` we get `a·y' + b·(x' − (a / b)·y') = g`. -/
def xgcd : ℕ → ℕ → ℤ × ℤ
  | _, 0 => (1, 0)
  | a, b + 1 =>
    let p := xgcd (b + 1) (a % (b + 1))
    (p.2, p.1 - ((a / (b + 1) : ℕ) : ℤ) * p.2)
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)
-- @endregion

-- @region divisibility_gcd.bezout
-- @provenance independent
/-- **Bézout's identity**, with the coefficients produced by `xgcd`:
`a·x + b·y = gcd(a, b)`. Proof by induction following the recursion, using the back-substitution
described in `xgcd`. -/
theorem bezout (a b : ℕ) :
    (a : ℤ) * (xgcd a b).1 + (b : ℤ) * (xgcd a b).2 = (Nat.gcd a b : ℤ) := by
  rw [← euclid_eq_gcd]
  induction a, b using xgcd.induct with
  | case1 a =>
    rw [xgcd, euclid]
    simp
  | case2 a b ih =>
    rw [xgcd, euclid]
    have hcast : ((a % (b + 1) : ℕ) : ℤ) + ((b + 1 : ℕ) : ℤ) * ((a / (b + 1) : ℕ) : ℤ) = (a : ℤ) := by
      exact_mod_cast Nat.mod_add_div a (b + 1)
    simp only
    linear_combination ih - (xgcd (b + 1) (a % (b + 1))).2 * hcast
-- @endregion

-- @region divisibility_gcd.bezout_library
-- @provenance library
/-- Bézout's identity in Mathlib: `Nat.gcd_eq_gcd_ab`, with Mathlib's extended Euclidean algorithm
`Nat.gcdA`, `Nat.gcdB`. -/
theorem bezout_library (a b : ℕ) :
    (Nat.gcd a b : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b :=
  Nat.gcd_eq_gcd_ab a b
-- @endregion

/-! ### Euclid's lemma -/

-- @region divisibility_gcd.euclid_lemma
-- @provenance independent
/-- **Euclid's lemma**: if a prime `p` divides `a·b`, then `p ∣ a` or `p ∣ b`.
If `p ∤ a` then `gcd(p, a) = 1` (the only positive divisors of `p` are `1` and `p`), so by Bézout
`p·x + a·y = 1`. Multiplying by `b`: `b = p·(b·x) + (a·b)·y`, and `p` divides both terms. -/
theorem euclid_lemma {p a b : ℕ} (hp : p.Prime) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hcop : Nat.gcd p a = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
    have hbez := bezout p a
    rw [hcop, Nat.cast_one] at hbez
    have hZ : (p : ℤ) ∣ (a : ℤ) * (b : ℤ) := by exact_mod_cast h
    have key : (b : ℤ) = (p : ℤ) * ((b : ℤ) * (xgcd p a).1) + ((a : ℤ) * (b : ℤ)) * (xgcd p a).2 := by
      linear_combination (-(b : ℤ)) * hbez
    have : (p : ℤ) ∣ (b : ℤ) := by
      rw [key]
      exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right hZ _)
    exact_mod_cast this
-- @endregion

-- @region divisibility_gcd.euclid_lemma_library
-- @provenance library
/-- Euclid's lemma in Mathlib: `Nat.Prime.dvd_mul`. -/
theorem euclid_lemma_library {p a b : ℕ} (hp : p.Prime) : p ∣ a * b ↔ p ∣ a ∨ p ∣ b :=
  hp.dvd_mul
-- @endregion

-- @region divisibility_gcd.four_counterexample
-- @provenance independent
/-- **Primality matters in Euclid's lemma**: `4 ∣ 2·2`, but `4 ∤ 2`. -/
theorem four_counterexample : 4 ∣ 2 * 2 ∧ ¬ 4 ∣ 2 := by decide
-- @endregion

/-! ### The fundamental theorem of arithmetic -/

-- @region divisibility_gcd.exists_prime_factorization
-- @provenance independent
/-- **Existence of prime factorisations**, by strong induction: every `n ≥ 1` is the product of a
list of primes (`1` is the empty product). For `n > 1`, let `p` be its smallest factor bigger
than `1` — a prime — and factorise the smaller number `n / p`. -/
theorem exists_prime_factorization (n : ℕ) (hn : n ≠ 0) :
    ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨[], by simp, by simp [h1]⟩
    · have hp : (Nat.minFac n).Prime := Nat.minFac_prime h1
      have hdiv : Nat.minFac n * (n / Nat.minFac n) = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have hlt : n / Nat.minFac n < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
      have hne : n / Nat.minFac n ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hdiv
        exact hn hdiv.symm
      obtain ⟨l, hl, hprod⟩ := ih (n / Nat.minFac n) hlt hne
      refine ⟨Nat.minFac n :: l, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hl q hq
      · rw [List.prod_cons, hprod, hdiv]
-- @endregion

-- @region divisibility_gcd.prime_dvd_prod
-- @provenance independent
/-- Euclid's lemma for several factors: if a prime divides a product of a list of numbers, it
divides one of them. Induction on the list, using `euclid_lemma` at each step. -/
theorem prime_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ l : List ℕ, p ∣ l.prod → ∃ q ∈ l, p ∣ q
  | [], h => absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
  | q :: t, h => by
    rw [List.prod_cons] at h
    rcases euclid_lemma hp h with hq | ht
    · exact ⟨q, List.mem_cons_self, hq⟩
    · obtain ⟨r, hr, hpr⟩ := prime_dvd_prod hp t ht
      exact ⟨r, List.mem_cons_of_mem q hr, hpr⟩
-- @endregion

-- @region divisibility_gcd.factorization_unique
-- @provenance independent
/-- **Uniqueness of prime factorisations**: two lists of primes with the same product are
rearrangements of each other (`List.Perm`, written `~`). Induction on the first list: its head `p`
divides the product of the second, so (Euclid's lemma) it divides — hence equals — one of its
primes `q`; remove `p` from both sides and cancel. -/
theorem factorization_unique :
    ∀ l₁ l₂ : List ℕ, (∀ p ∈ l₁, p.Prime) → (∀ p ∈ l₂, p.Prime) → l₁.prod = l₂.prod → l₁.Perm l₂
  | [], l₂, _, h₂, h => by
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons q t =>
      exfalso
      have hq : q ∣ (q :: t).prod := by rw [List.prod_cons]; exact dvd_mul_right q _
      rw [← h, List.prod_nil] at hq
      exact (h₂ q List.mem_cons_self).one_lt.ne' (Nat.dvd_one.mp hq)
  | p :: t, l₂, h₁, h₂, h => by
    have hp : p.Prime := h₁ p List.mem_cons_self
    have hdvd : p ∣ l₂.prod := by rw [← h, List.prod_cons]; exact dvd_mul_right p _
    obtain ⟨q, hq, hpq⟩ := prime_dvd_prod hp l₂ hdvd
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp (h₂ q hq)).mp hpq
    subst hpq'
    have hperm : l₂.Perm (p :: l₂.erase p) := List.perm_cons_erase hq
    have hprod : t.prod = (l₂.erase p).prod := by
      have e : p * t.prod = p * (l₂.erase p).prod := by
        rw [← List.prod_cons, h, hperm.prod_eq, List.prod_cons]
      exact Nat.eq_of_mul_eq_mul_left hp.pos e
    have ht : t.Perm (l₂.erase p) :=
      factorization_unique t (l₂.erase p) (fun r hr => h₁ r (List.mem_cons_of_mem p hr))
        (fun r hr => h₂ r (List.mem_of_mem_erase hr)) hprod
    exact (ht.cons p).trans hperm.symm
-- @endregion

-- @region divisibility_gcd.factorization_unique_library
-- @provenance library
/-- Unique factorisation in Mathlib: `Nat.primeFactorsList_unique` — any list of primes with
product `n` is a rearrangement of Mathlib's list `n.primeFactorsList`. -/
theorem factorization_unique_library {n : ℕ} {l : List ℕ} (h₁ : l.prod = n)
    (h₂ : ∀ p ∈ l, p.Prime) : l.Perm n.primeFactorsList :=
  Nat.primeFactorsList_unique h₁ h₂
-- @endregion

/-! ### Terminating decimals -/

-- @region divisibility_gcd.prime_dvd_pow
-- @provenance independent
/-- If a prime divides a power `n ^ k`, it divides `n`: Euclid's lemma applied `k` times
(induction on `k`; for `k = 0`, no prime divides `1`). -/
theorem prime_dvd_pow {p n : ℕ} (hp : p.Prime) : ∀ k : ℕ, p ∣ n ^ k → p ∣ n
  | 0, h => absurd (Nat.dvd_one.mp (by simpa using h)) hp.one_lt.ne'
  | k + 1, h => by
    rw [pow_succ] at h
    rcases euclid_lemma hp h with h1 | h2
    · exact prime_dvd_pow hp k h1
    · exact h2
-- @endregion

-- @region divisibility_gcd.terminating_prime_factors
-- @provenance independent
/-- **Terminating decimals, one direction.** A fraction `a / b` has a terminating decimal exactly
when `a · 10ᵏ / b` is a whole number for some `k`, i.e. `b ∣ a · 10ᵏ`. If moreover `a / b` is in
lowest terms (`gcd(a, b) = 1`), then every prime factor `p` of `b` is `2` or `5`: `p` divides
`a · 10ᵏ` but not `a`, so (Euclid's lemma) it divides `10ᵏ`, hence `10 = 2 · 5`, hence `2` or `5`. -/
theorem terminating_prime_factors {a b k p : ℕ} (hcop : Nat.gcd a b = 1) (h : b ∣ a * 10 ^ k)
    (hp : p.Prime) (hpb : p ∣ b) : p = 2 ∨ p = 5 := by
  have hpa10 : p ∣ a * 10 ^ k := Nat.dvd_trans hpb h
  rcases euclid_lemma hp hpa10 with hpa | hp10
  · have : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    rw [hcop] at this
    exact absurd (Nat.dvd_one.mp this) hp.one_lt.ne'
  · have h10 : p ∣ 2 * 5 := prime_dvd_pow hp k hp10
    rcases euclid_lemma hp h10 with h2 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5)
-- @endregion

-- @region divisibility_gcd.two_five_dvd_ten_pow
-- @provenance independent
/-- **Terminating decimals, the other direction.** If `b = 2ˢ · 5ᵗ`, then `b ∣ 10^(s + t)`, so
`a / b = a · c / 10^(s + t)` for a whole number `c`: the decimal terminates after `s + t` digits
(in fact after `max(s, t)`). Proof: `10^(s+t) = 2^(s+t) · 5^(s+t)`. -/
theorem two_five_dvd_ten_pow (s t : ℕ) : 2 ^ s * 5 ^ t ∣ 10 ^ (s + t) := by
  have e : (10 : ℕ) ^ (s + t) = 2 ^ (s + t) * 5 ^ (s + t) := by
    rw [← mul_pow]
    rfl
  rw [e]
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (Nat.le_add_right s t))
    (Nat.pow_dvd_pow 5 (Nat.le_add_left t s))
-- @endregion

/-! ### Where unique factorisation fails -/

-- @region divisibility_gcd.hilbert_irreducible
-- @provenance definition
/-- In the **Hilbert numbers** `1, 5, 9, 13, …` (those leaving remainder `1` on division by `4`,
which are closed under multiplication), `n > 1` is *irreducible* if it is not a product of two
smaller Hilbert numbers bigger than `1`. -/
def HilbertIrreducible (n : ℕ) : Prop :=
  n % 4 = 1 ∧ 1 < n ∧ ∀ a b : ℕ, (a % 4 = 1 ∧ b % 4 = 1 ∧ a * b = n) → a = 1 ∨ b = 1
-- @endregion

-- @region divisibility_gcd.hilbert_irreducible_iff
-- @provenance independent
/-- Irreducibility is a **finite check**: if `a · b = n` with `n > 0`, both factors are at most `n`,
so only `a, b ≤ n` need to be tried. -/
theorem hilbertIrreducible_iff (n : ℕ) :
    HilbertIrreducible n ↔ n % 4 = 1 ∧ 1 < n ∧
      ∀ a < n + 1, ∀ b < n + 1, (a % 4 = 1 ∧ b % 4 = 1 ∧ a * b = n) → a = 1 ∨ b = 1 := by
  constructor
  · rintro ⟨h4, h1, h⟩
    exact ⟨h4, h1, fun a _ b _ hab => h a b hab⟩
  · rintro ⟨h4, h1, h⟩
    refine ⟨h4, h1, fun a b hab => ?_⟩
    have hn : 0 < n := by omega
    have ha : a ≤ n := Nat.le_of_dvd hn ⟨b, hab.2.2.symm⟩
    have hb : b ≤ n := Nat.le_of_dvd hn ⟨a, by rw [Nat.mul_comm]; exact hab.2.2.symm⟩
    exact h a (by omega) b (by omega) hab
-- @endregion

-- @region divisibility_gcd.hilbert_non_unique
-- @provenance independent
/-- **Unique factorisation needs proof**: among Hilbert numbers, `9`, `21` and `49` are irreducible,
yet `441 = 9 · 49 = 21 · 21` — two genuinely different factorisations into irreducibles. Checked
by the finite search of `hilbertIrreducible_iff` (`decide`). -/
theorem hilbert_non_unique :
    HilbertIrreducible 9 ∧ HilbertIrreducible 21 ∧ HilbertIrreducible 49 ∧
      9 * 49 = 441 ∧ 21 * 21 = 441 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩ <;> rw [hilbertIrreducible_iff] <;> decide
-- @endregion

end Lumenary.DivisibilityGcd
