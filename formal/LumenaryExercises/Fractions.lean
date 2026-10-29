/-
The Lumenary — Lean exercises: Fractions and decimals.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Fractions.lean`.
-/
import Lumenary.Fractions

namespace LumenaryExercises.Fractions

open Lumenary.Fractions

-- @region ex.fractions.bigger_den_smaller_piece
-- @solution Lumenary.Fractions.bigger_den_smaller_piece
/-- Show that a bigger denominator gives a smaller unit fraction: if `b < d` then `1/d < 1/b`.
Hint: `change 1 * b < 1 * d` unfolds the comparison; then `Nat.one_mul` simplifies. -/
theorem bigger_den_smaller_piece (b d : Nat) (hb : 0 < b) (hd : 0 < d) (h : b < d) :
    frac 1 d hd < frac 1 b hb := by
  sorry
-- @endregion

-- @region ex.fractions.ten_pow_mod_three
-- @solution Lumenary.Fractions.ten_pow_mod_three
/-- Show that every power of ten leaves remainder `1` when divided by `3`.
Hint: induction on `k`; in the step use `Nat.pow_succ` and `Nat.mul_mod`. -/
theorem ten_pow_mod_three (k : Nat) : 10 ^ k % 3 = 1 := by
  sorry
-- @endregion

end LumenaryExercises.Fractions
