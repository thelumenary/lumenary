/-
The Lumenary — Lean exercises: Factors, multiples and primes.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FactorsPrimes.lean`.
-/
import Lumenary.FactorsPrimes

namespace LumenaryExercises.FactorsPrimes

open Lumenary.FactorsPrimes

-- @region ex.factors_primes.one_not_prime
-- @solution Lumenary.FactorsPrimes.one_not_prime
/-- Show that `1` is not prime.
Hint: `intro ⟨h2, _⟩` gives `h2 : 2 ≤ 1`. Why is that impossible? -/
theorem one_not_prime : ¬ IsPrime 1 := by
  sorry
-- @endregion

-- @region ex.factors_primes.dvd_add_of_dvd
-- @solution Lumenary.FactorsPrimes.dvd_add_of_dvd
/-- Show that a common factor of `a` and `b` is a factor of `a + b`.
Hint: unpack `ha` and `hb` with `obtain ⟨j, hj⟩ := ha`, then use `Nat.mul_add`. -/
theorem dvd_add_of_dvd {d a b : Nat} (ha : d ∣ a) (hb : d ∣ b) : d ∣ a + b := by
  sorry
-- @endregion

end LumenaryExercises.FactorsPrimes
