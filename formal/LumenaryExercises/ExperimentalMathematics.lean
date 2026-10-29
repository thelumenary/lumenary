/-
The Lumenary — Lean exercises: Experimental mathematics.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/ExperimentalMathematics.lean`.
-/
import Lumenary.ExperimentalMathematics

namespace LumenaryExercises.ExperimentalMathematics

open Lumenary.ExperimentalMathematics

-- @region ex.experimental_mathematics.euler_conjecture_five_false
-- @solution Lumenary.ExperimentalMathematics.euler_conjecture_five_false
/-- Refute Euler's sum-of-powers conjecture for fifth powers.
Hint: `intro h` and apply `h` to Lander and Parkin's numbers `27 84 110 133 144`; the
positivity side conditions follow from `norm_num`, and the equation is `lander_parkin`. -/
theorem euler_conjecture_five_false : ¬ EulerConjectureFive := by
  sorry
-- @endregion

-- @region ex.experimental_mathematics.fermat_conjecture_false
-- @solution Lumenary.ExperimentalMathematics.fermat_conjecture_false
/-- Not every Fermat number is prime.
Hint: show `fermat 5 = 641 * 6700417` with `norm_num [fermat]`, then use `Nat.not_prime_mul`. -/
theorem fermat_conjecture_false : ¬ ∀ n, (fermat n).Prime := by
  sorry
-- @endregion

end LumenaryExercises.ExperimentalMathematics
