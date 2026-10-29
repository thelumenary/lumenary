/-
The Lumenary — Lean exercises: check digits and parity bits.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CheckDigits.lean`.
-/
import Lumenary.CheckDigits

namespace LumenaryExercises.CheckDigits

open Lumenary.CheckDigits

-- @region ex.check_digits.swap_caught_by_isbn10
-- @solution Lumenary.CheckDigits.swap_caught_by_isbn10
/-- Show that `3-61-148410-X` (the digits `1` and `6` of `3-16-148410-X` swapped) is not a
valid ISBN-10. Hint: for one particular list of digits Lean can compute the check sum
itself — try `decide`. -/
theorem swap_caught_by_isbn10 : ¬ ValidISBN10 [3, 6, 1, 1, 4, 8, 4, 1, 0, 10] := by
  sorry
-- @endregion

-- @region ex.check_digits.add_parity_bit
-- @solution Lumenary.CheckDigits.add_parity_bit
/-- Show that appending the parity bit of a message gives an even number of `1`s.
Hint: rewrite with `parity_append`, then `simp [parity]` finishes, because `xor p p = false`. -/
theorem add_parity_bit (bs : List Bool) : parity (bs ++ [parity bs]) = false := by
  sorry
-- @endregion

end LumenaryExercises.CheckDigits
