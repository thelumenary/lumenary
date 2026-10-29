/-
The Lumenary — Lean exercises: Cryptography.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Cryptography.lean`.
-/
import Lumenary.Cryptography

namespace LumenaryExercises.Cryptography

-- @region ex.cryptography.dh_agree
-- @solution Lumenary.Cryptography.dh_agree
/-- Both Diffie–Hellman parties compute the same key.
Hint: `Nat.pow_mod` says `a ^ b % n = (a % n) ^ b % n`; then use `pow_mul` and `mul_comm`. -/
theorem dh_agree (g a b p : ℕ) : (g ^ b % p) ^ a % p = (g ^ a % p) ^ b % p := by
  sorry
-- @endregion

-- @region ex.cryptography.rsa_malleable
-- @solution Lumenary.Cryptography.rsa_malleable
/-- Textbook RSA is multiplicative.
Hint: `Nat.mul_mod` (read right to left) and `mul_pow`. -/
theorem rsa_malleable (m₁ m₂ e n : ℕ) :
    (m₁ ^ e % n) * (m₂ ^ e % n) % n = (m₁ * m₂) ^ e % n := by
  sorry
-- @endregion

end LumenaryExercises.Cryptography
