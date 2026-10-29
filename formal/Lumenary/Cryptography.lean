/-
The Lumenary — formal mathematics
Cryptography: fast modular exponentiation, the correctness of RSA, Diffie–Hellman key
agreement, the malleability of textbook RSA, and the one-time pad.

Correctness is a theorem; security is not. Everything below is about *correctness* — that
decryption undoes encryption, that two parties obtain the same key, that a fast algorithm
computes the right number. No Lean (or other) proof here or anywhere establishes that RSA or
Diffie–Hellman is *secure*: that rests on unproved assumptions about the difficulty of factoring
and of discrete logarithms. The RSA correctness theorem is proved from Fermat's little theorem
and the Chinese remainder theorem, as in the lesson (`@provenance independent`); Mathlib
supplies Fermat (`ZMod.pow_card_sub_one_eq_one`), the Chinese remainder step
(`Nat.modEq_and_modEq_iff_modEq_mul`) and the totient of a product.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

namespace Lumenary.Cryptography

/-! ### Fast modular exponentiation -/

-- @region cryptography.pow_mod
-- @provenance definition
/-- **Modular exponentiation by repeated squaring.** To compute `bᵉ mod n`, compute
`h = b^⌊e/2⌋ mod n` recursively, square it, and multiply by `b` once more if `e` is odd. Each
call halves `e`, so about `log₂ e` calls suffice, and every intermediate number is below `n²`
(or `n² · b`) — never the astronomically large `bᵉ`. -/
def powMod (b e n : ℕ) : ℕ :=
  if e = 0 then 1 % n
  else
    let h := powMod b (e / 2) n
    if e % 2 = 0 then h * h % n else h * h % n * b % n
termination_by e
decreasing_by omega
-- @endregion

-- @region cryptography.pow_mod_eq
-- @provenance independent
/-- **Repeated squaring computes the right number:** `powMod b e n = bᵉ mod n`. Strong induction
on `e`, using `e = 2⌊e/2⌋` or `e = 2⌊e/2⌋ + 1` and the fact that reducing mod `n` before
multiplying does not change the result mod `n` (`Nat.mul_mod`). -/
theorem powMod_eq (b e n : ℕ) : powMod b e n = b ^ e % n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [powMod]
    split_ifs with h0 h2
    · simp [h0]
    · have he : e = e / 2 + e / 2 := by omega
      have ih' := ih (e / 2) (by omega)
      simp only [ih']
      conv_rhs => rw [he, pow_add, Nat.mul_mod]
    · have he : e = (e / 2 + e / 2) + 1 := by omega
      have ih' := ih (e / 2) (by omega)
      simp only [ih']
      conv_rhs => rw [he, pow_succ, pow_add, Nat.mul_mod, Nat.mul_mod (b ^ (e / 2))]
      simp [Nat.mul_mod]
-- @endregion

/-! ### RSA -/

-- @region cryptography.pow_mul_sub_one_succ
-- @provenance independent
/-- **The key lemma for RSA:** for a prime `p` and *every* natural number `m` (whether or not
`p` divides it), `m^(k(p - 1) + 1) ≡ m (mod p)`. If `p ∣ m` both sides are `0 (mod p)`; otherwise
Fermat gives `m^(p-1) ≡ 1`, so `m^(k(p-1)+1) = (m^(p-1))^k · m ≡ m`. -/
theorem pow_mul_sub_one_succ (p : ℕ) [Fact p.Prime] (k m : ℕ) :
    m ^ (k * (p - 1) + 1) ≡ m [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  by_cases hm : (m : ZMod p) = 0
  · rw [hm, zero_pow (Nat.succ_ne_zero _)]
  · rw [pow_succ, mul_comm k, pow_mul, ZMod.pow_card_sub_one_eq_one hm, one_pow, one_mul]
-- @endregion

-- @region cryptography.rsa_correct
-- @provenance independent
/-- **RSA decryption works.** Let `p ≠ q` be primes, `n = pq`, and `ed ≡ 1 (mod (p-1)(q-1))`.
Then `(mᵉ)ᵈ ≡ m (mod n)` for **every** natural number `m`. Write `ed = t(p-1)(q-1) + 1`; the key
lemma gives `m^(ed) ≡ m` modulo `p` and modulo `q` separately, and because `p` and `q` are
coprime the two congruences combine to one modulo `pq` (the Chinese remainder theorem, Mathlib's
`Nat.modEq_and_modEq_iff_modEq_mul`). -/
theorem rsa_correct {p q e d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hed : e * d ≡ 1 [MOD (p - 1) * (q - 1)]) (m : ℕ) : (m ^ e) ^ d ≡ m [MOD p * q] := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  -- `(p - 1)(q - 1) > 1`, so `ed` leaves remainder `1`.
  have hφ : 1 < (p - 1) * (q - 1) := by
    rcases Nat.lt_or_ge 2 p with h | h
    · calc 1 < 2 * 1 := by norm_num
        _ ≤ (p - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
    · have hq3 : 3 ≤ q := by omega
      calc 1 < 1 * 2 := by norm_num
        _ ≤ (p - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hrem : e * d % ((p - 1) * (q - 1)) = 1 := by
    rw [hed, Nat.mod_eq_of_lt hφ]
  set t := e * d / ((p - 1) * (q - 1))
  have hsplit : e * d = t * (p - 1) * (q - 1) + 1 := by
    have := Nat.div_add_mod (e * d) ((p - 1) * (q - 1))
    rw [hrem] at this
    rw [← this]
    ring
  rw [← pow_mul, hsplit]
  have hmodp : m ^ (t * (p - 1) * (q - 1) + 1) ≡ m [MOD p] := by
    have h := pow_mul_sub_one_succ p (t * (q - 1)) m
    rwa [show t * (q - 1) * (p - 1) = t * (p - 1) * (q - 1) by ring] at h
  have hmodq : m ^ (t * (p - 1) * (q - 1) + 1) ≡ m [MOD q] :=
    pow_mul_sub_one_succ q (t * (p - 1)) m
  exact (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes hp hq).mpr hpq)).mp
    ⟨hmodp, hmodq⟩
-- @endregion

-- @region cryptography.totient_pq
-- @provenance library
/-- For distinct primes, `φ(pq) = (p - 1)(q - 1)`: Mathlib's `Nat.totient_mul` (φ is
multiplicative on coprime arguments) and `Nat.totient_prime`. So the condition in `rsa_correct`
is the textbook `ed ≡ 1 (mod φ(n))`. -/
theorem totient_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq), Nat.totient_prime hp,
    Nat.totient_prime hq]
-- @endregion

-- @region cryptography.rsa_toy
-- @provenance independent
/-- **A toy RSA key** (the small example in Rivest, Shamir and Adleman's 1978 paper):
`n = 47 · 59 = 2773`, `φ = 46 · 58 = 2668`, `e = 17`, `d = 157`, since `17 · 157 = 2669`. The
message `1234` encrypts to `1234¹⁷ mod 2773 = 1793`, which decrypts back to `1234`. The kernel
checks the arithmetic (`decide +kernel`). -/
theorem rsa_toy :
    17 * 157 % ((47 - 1) * (59 - 1)) = 1 ∧ 1234 ^ 17 % 2773 = 1793 ∧ 1793 ^ 157 % 2773 = 1234 := by
  decide +kernel
-- @endregion

-- @region cryptography.rsa_malleable
-- @provenance independent
/-- **Textbook RSA is malleable:** the encryptions of `m₁` and `m₂` multiply to the encryption of
`m₁ m₂`, because `m₁ᵉ m₂ᵉ = (m₁ m₂)ᵉ`. An attacker can transform a ciphertext into the
ciphertext of a related message without knowing either — one reason real systems pad messages
with randomness before encrypting. -/
theorem rsa_malleable (m₁ m₂ e n : ℕ) :
    (m₁ ^ e % n) * (m₂ ^ e % n) % n = (m₁ * m₂) ^ e % n := by
  rw [← Nat.mul_mod, mul_pow]
-- @endregion

/-! ### Diffie–Hellman -/

-- @region cryptography.dh_agree
-- @provenance independent
/-- **Diffie–Hellman key agreement.** With public `g` and `p`, one party publishes `A = gᵃ mod p`,
the other `B = gᵇ mod p`; then `Bᵃ ≡ Aᵇ (mod p)`, since both are `g^(ab) mod p`. Reducing mod `p`
in between does not matter (`Nat.pow_mod`), and `(gᵇ)ᵃ = g^(ba) = g^(ab) = (gᵃ)ᵇ`. -/
theorem dh_agree (g a b p : ℕ) : (g ^ b % p) ^ a % p = (g ^ a % p) ^ b % p := by
  rw [← Nat.pow_mod, ← Nat.pow_mod, ← pow_mul, ← pow_mul, mul_comm]
-- @endregion

-- @region cryptography.dh_toy
-- @provenance independent
/-- A toy exchange in the group of non-zero residues mod `101`, where `2` is a generator. Ama keeps
`a = 37` and publishes `2³⁷ mod 101 = 55`; Bolat keeps `b = 58` and publishes `2⁵⁸ mod 101 = 47`.
Both compute the shared secret `82`. -/
theorem dh_toy :
    2 ^ 37 % 101 = 55 ∧ 2 ^ 58 % 101 = 47 ∧ 47 ^ 37 % 101 = 82 ∧ 55 ^ 58 % 101 = 82 := by
  decide +kernel
-- @endregion

/-! ### The one-time pad -/

-- @region cryptography.otp_decrypt
-- @provenance library
/-- **The one-time pad decrypts correctly:** encrypting with a key by bitwise XOR (`^^^`) and
XOR-ing with the same key again returns the message. Core Lean's `Nat.xor_xor_cancel_right`. -/
theorem otp_decrypt (m k : ℕ) : (m ^^^ k) ^^^ k = m := Nat.xor_xor_cancel_right m k
-- @endregion

-- @region cryptography.otp_unique_key
-- @provenance independent
/-- **Why the one-time pad hides everything:** for any message `m` and any ciphertext `c` there
is exactly one key `k` with `m ^^^ k = c`, namely `k = m ^^^ c`. So if the key is chosen
uniformly at random, every message is equally consistent with the ciphertext — Shannon's perfect
secrecy. -/
theorem otp_unique_key (m k c : ℕ) : m ^^^ k = c ↔ k = m ^^^ c := by
  constructor
  · rintro rfl
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rintro rfl
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
-- @endregion

end Lumenary.Cryptography
