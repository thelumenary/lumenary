/-
The Lumenary — formal mathematics
Congruences: congruence modulo n as an equivalence relation compatible with + and ×,
inverses modulo n, the Chinese remainder theorem, and the theorems of Fermat, Euler and Wilson.

Mathlib writes `a ≡ b [ZMOD n]` for `Int.ModEq n a b` (defined as `a % n = b % n`) and
`ZMod n` for the ring of residues. Below, the equivalence and compatibility properties, the
criterion for an inverse (`gcd(a, n) = 1`), both halves of the Chinese remainder theorem and
Fermat's little theorem are proved from basic facts, mirroring the lesson
(`@provenance independent`). Euler's and Wilson's theorems, and Mathlib's own Fermat, are cited
(`@provenance library`).
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.PowMod

namespace Lumenary.Congruences

/-! ### Congruence is an equivalence relation, compatible with `+` and `×` -/

-- @region congruences.mod_eq_iff_dvd_sub
-- @provenance library
/-- **The definition used in the lesson.** `a ≡ b (mod n)` means `n ∣ a - b`. Mathlib defines
`a ≡ b [ZMOD n]` as "same remainder", `a % n = b % n`; its theorem `Int.modEq_iff_dvd`
(`n ∣ b - a`) shows the two definitions agree. -/
theorem modEq_iff_dvd_sub {n a b : ℤ} : a ≡ b [ZMOD n] ↔ n ∣ a - b :=
  Int.modEq_iff_dvd.trans dvd_sub_comm
-- @endregion

-- @region congruences.mod_eq_equivalence
-- @provenance independent
/-- **Congruence modulo `n` is an equivalence relation.** Reflexive: `n ∣ 0 = a - a`.
Symmetric: `b - a = -(a - b)`. Transitive: `a - c = (a - b) + (b - c)`. -/
theorem modEq_equivalence (n : ℤ) : Equivalence (Int.ModEq n) where
  refl a := modEq_iff_dvd_sub.mpr (by simp)
  symm {a b} h := by
    rw [modEq_iff_dvd_sub] at h ⊢
    have h' : n ∣ -(a - b) := dvd_neg.mpr h
    rwa [neg_sub] at h'
  trans {a b c} h₁ h₂ := by
    rw [modEq_iff_dvd_sub] at h₁ h₂ ⊢
    have h : n ∣ (a - b) + (b - c) := dvd_add h₁ h₂
    rwa [sub_add_sub_cancel] at h
-- @endregion

-- @region congruences.mod_eq_add
-- @provenance independent
/-- **Congruences can be added.** If `a ≡ b` and `c ≡ d (mod n)` then `a + c ≡ b + d`, because
`(a + c) - (b + d) = (a - b) + (c - d)`. -/
theorem modEq_add {n a b c d : ℤ} (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  rw [modEq_iff_dvd_sub] at h₁ h₂ ⊢
  have h : (a + c) - (b + d) = (a - b) + (c - d) := by ring
  rw [h]
  exact dvd_add h₁ h₂
-- @endregion

-- @region congruences.mod_eq_mul
-- @provenance independent
/-- **Congruences can be multiplied.** If `a ≡ b` and `c ≡ d (mod n)` then `ac ≡ bd`, because
`ac - bd = a(c - d) + d(a - b)` and `n` divides both terms. -/
theorem modEq_mul {n a b c d : ℤ} (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  rw [modEq_iff_dvd_sub] at h₁ h₂ ⊢
  have h : a * c - b * d = a * (c - d) + d * (a - b) := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_right h₂ a) (dvd_mul_of_dvd_right h₁ d)
-- @endregion

-- @region congruences.cancel_fails
-- @provenance independent
/-- **You may not always cancel.** `2 · 3 ≡ 2 · 9 (mod 12)`, since both sides are `6 (mod 12)`,
but `3 ≢ 9 (mod 12)`. The factor `2` shares the divisor `2` with `12`. Checked by `decide`. -/
theorem cancel_fails : 2 * 3 ≡ 2 * 9 [ZMOD 12] ∧ ¬ 3 ≡ 9 [ZMOD 12] := by
  decide
-- @endregion

/-! ### Inverses modulo `n` -/

-- @region congruences.exists_inverse_iff_is_coprime
-- @provenance independent
/-- **`a` has an inverse modulo `n` exactly when `a` and `n` are coprime**, in Bézout's form:
`ab ≡ 1 (mod n)` for some `b` if and only if `ua + vn = 1` for some integers `u, v`
(Mathlib's `IsCoprime a n`).
* (→) If `n ∣ ab - 1`, say `ab - 1 = nk`, then `b · a + (-k) · n = 1`.
* (←) If `ua + vn = 1` then `au - 1 = -vn` is a multiple of `n`, so `u` is an inverse. -/
theorem exists_inverse_iff_isCoprime {a n : ℤ} : (∃ b, a * b ≡ 1 [ZMOD n]) ↔ IsCoprime a n := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨k, hk⟩ := modEq_iff_dvd_sub.mp hb
    exact ⟨b, -k, by linear_combination hk⟩
  · rintro ⟨u, v, huv⟩
    refine ⟨u, modEq_iff_dvd_sub.mpr ⟨-v, ?_⟩⟩
    linear_combination huv
-- @endregion

-- @region congruences.exists_inverse_iff_gcd
-- @provenance independent
/-- The same criterion with the gcd: `a` is invertible modulo `n` if and only if
`gcd(a, n) = 1`. This combines `exists_inverse_iff_isCoprime` with Mathlib's
`Int.isCoprime_iff_gcd_eq_one` (Bézout's identity and its converse). -/
theorem exists_inverse_iff_gcd {a n : ℤ} : (∃ b, a * b ≡ 1 [ZMOD n]) ↔ Int.gcd a n = 1 :=
  exists_inverse_iff_isCoprime.trans Int.isCoprime_iff_gcd_eq_one
-- @endregion

-- @region congruences.cancel_of_is_coprime
-- @provenance independent
/-- **Cancelling a coprime factor is allowed.** If `c` is invertible modulo `n` and
`ca ≡ cb`, multiply both sides by an inverse `u` of `c`: `a ≡ (uc)a = u(ca) ≡ u(cb) = (uc)b ≡ b`. -/
theorem cancel_of_isCoprime {n a b c : ℤ} (hc : IsCoprime c n) (h : c * a ≡ c * b [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  obtain ⟨u, hu⟩ := exists_inverse_iff_isCoprime.mpr hc
  have hu' : u * c ≡ 1 [ZMOD n] := by rwa [mul_comm] at hu
  have ha : u * c * a ≡ 1 * a [ZMOD n] := modEq_mul hu' (Int.ModEq.refl a)
  have hb : u * c * b ≡ 1 * b [ZMOD n] := modEq_mul hu' (Int.ModEq.refl b)
  have hab : u * (c * a) ≡ u * (c * b) [ZMOD n] := modEq_mul (Int.ModEq.refl u) h
  rw [one_mul] at ha hb
  rw [← mul_assoc, ← mul_assoc] at hab
  exact (ha.symm.trans hab).trans hb
-- @endregion

/-! ### The Chinese remainder theorem -/

-- @region congruences.crt_exists
-- @provenance independent
/-- **Chinese remainder theorem, existence.** If `um + vn = 1`, then `x = a·vn + b·um` solves
`x ≡ a (mod m)` and `x ≡ b (mod n)`: modulo `m` we have `vn = 1 - um ≡ 1`, and modulo `n` we have
`um ≡ 1`. Each congruence is checked by exhibiting the quotient. -/
theorem crt_exists {m n : ℤ} (h : IsCoprime m n) (a b : ℤ) :
    ∃ x, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨a * v * n + b * u * m, ?_, ?_⟩
  · exact modEq_iff_dvd_sub.mpr ⟨b * u - a * u, by linear_combination a * huv⟩
  · exact modEq_iff_dvd_sub.mpr ⟨a * v - b * v, by linear_combination b * huv⟩
-- @endregion

-- @region congruences.crt_unique
-- @provenance independent
/-- **Chinese remainder theorem, uniqueness.** If `m, n` are coprime and `x ≡ y` modulo both
`m` and `n`, then `x ≡ y (mod mn)`: `m` and `n` both divide `x - y`, and coprime divisors
multiply (Mathlib's `IsCoprime.mul_dvd`, itself proved from Bézout). -/
theorem crt_unique {m n x y : ℤ} (h : IsCoprime m n) (hm : x ≡ y [ZMOD m])
    (hn : x ≡ y [ZMOD n]) : x ≡ y [ZMOD m * n] :=
  modEq_iff_dvd_sub.mpr (h.mul_dvd (modEq_iff_dvd_sub.mp hm) (modEq_iff_dvd_sub.mp hn))
-- @endregion

/-! ### Fermat, Euler and Wilson -/

-- @region congruences.pow_prime_eq_self
-- @provenance independent
/-- **Fermat's little theorem, first form: `aᵖ ≡ a (mod p)` for every `a`.** In `ZMod p` this
reads `xᵖ = x`. Proof by induction on `a`, as in the lesson: `0ᵖ = 0`, and
`(a + 1)ᵖ = aᵖ + 1ᵖ` because `p` divides every binomial coefficient `C(p, k)` with `0 < k < p`
(Mathlib's `add_pow_char`, "the freshman's dream" in characteristic `p`). Every residue is the
image of a natural number, which finishes the proof. -/
theorem pow_prime_eq_self (p : ℕ) [Fact p.Prime] (x : ZMod p) : x ^ p = x := by
  have key : ∀ k : ℕ, (k : ZMod p) ^ p = k := by
    intro k
    induction k with
    | zero => simp [zero_pow (Fact.out : p.Prime).ne_zero]
    | succ k ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective x
  exact key k
-- @endregion

-- @region congruences.fermat_little
-- @provenance independent
/-- **Fermat's little theorem: if `p ∤ a` then `aᵖ⁻¹ ≡ 1 (mod p)`.** From `a · aᵖ⁻¹ = aᵖ = a`
we may cancel `a ≠ 0`, because `ZMod p` is a field. -/
theorem fermat_little (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h : a * a ^ (p - 1) = a * 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp, pow_prime_eq_self, mul_one]
  exact mul_left_cancel₀ ha h
-- @endregion

-- @region congruences.fermat_library
-- @provenance library
/-- Fermat's little theorem for integers, from Mathlib (`Int.ModEq.pow_card_sub_one_eq_one`):
if `p` is prime and `a` is coprime to `p`, then `aᵖ⁻¹ ≡ 1 (mod p)`. -/
theorem fermat_library {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsCoprime a p) :
    a ^ (p - 1) ≡ 1 [ZMOD p] :=
  Int.ModEq.pow_card_sub_one_eq_one hp ha
-- @endregion

-- @region congruences.euler_totient
-- @provenance library
/-- **Euler's theorem:** if `gcd(a, n) = 1` then `a^φ(n) ≡ 1 (mod n)`. Mathlib's
`Nat.ModEq.pow_totient`, proved there by Lagrange's theorem in the group of units of `ZMod n`. -/
theorem euler_totient {a n : ℕ} (h : Nat.Coprime a n) : a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h
-- @endregion

-- @region congruences.wilson
-- @provenance library
/-- **Wilson's theorem:** `(p - 1)! ≡ -1 (mod p)` for every prime `p`. Mathlib's
`ZMod.wilsons_lemma`, proved by pairing each residue with its inverse. -/
theorem wilson (p : ℕ) [Fact p.Prime] : ((p - 1).factorial : ZMod p) = -1 :=
  ZMod.wilsons_lemma p
-- @endregion

/-! ### Computations -/

-- @region congruences.big_power
-- @provenance independent
/-- A worked example: `3¹⁰⁰ ≡ 4 (mod 7)`. By Fermat `3⁶ ≡ 1`, and `100 = 6 · 16 + 4`, so
`3¹⁰⁰ ≡ 3⁴ = 81 ≡ 4`. Here Lean simply checks the arithmetic with `decide`. -/
theorem big_power : 3 ^ 100 ≡ 4 [MOD 7] := by
  decide
-- @endregion

-- @region congruences.carmichael_561
-- @provenance independent
/-- **The converse of Fermat fails.** `561 = 3 · 11 · 17` is not prime, yet `2⁵⁶⁰ ≡ 1 (mod 561)`:
561 passes Fermat's test to base 2 (in fact to every base coprime to it — it is the smallest
Carmichael number). `norm_num` certifies compositeness; `decide` checks the power. -/
theorem carmichael_561 : ¬ Nat.Prime 561 ∧ 2 ^ 560 ≡ 1 [MOD 561] := by
  refine ⟨by norm_num, ?_⟩
  decide +kernel
-- @endregion

end Lumenary.Congruences
