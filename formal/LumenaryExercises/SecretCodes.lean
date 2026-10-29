/-
The Lumenary — Lean exercises: Secret codes.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/SecretCodes.lean`.
-/
import Lumenary.SecretCodes

namespace LumenaryExercises.SecretCodes

open Lumenary.SecretCodes

-- @region ex.secret_codes.wrap_around
-- @solution Lumenary.SecretCodes.wrap_around
/-- Check that a shift of 3 wraps X, Y and Z round to A, B and C.
Hint: Lean can work out these remainders itself — try `decide`. -/
theorem wrap_around : shift 3 23 = 0 ∧ shift 3 24 = 1 ∧ shift 3 25 = 2 ∧ shift 3 12 = 15 := by
  sorry
-- @endregion

-- @region ex.secret_codes.zebra
-- @solution Lumenary.SecretCodes.zebra
/-- Encode ZEBRA with a shift of 3.
Hint: `decide` can run the cipher on the whole word. -/
theorem zebra : caesar 3 "ZEBRA" = "CHEUD" := by
  sorry
-- @endregion

-- @region ex.secret_codes.shift_shift
-- @solution Lumenary.SecretCodes.shift_shift
/-- Show that two shifts make one shift.
Hint: `unfold shift` turns the goal into a statement about remainders; then `omega` can
finish it. -/
theorem shift_shift (a b n : Nat) : shift b (shift a n) = shift (a + b) n := by
  sorry
-- @endregion

end LumenaryExercises.SecretCodes
