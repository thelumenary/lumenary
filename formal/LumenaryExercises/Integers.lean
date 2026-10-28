/-
The Lumenary — Lean exercises: Integers.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Integers.lean`.
-/
import Lumenary.Integers

namespace LumenaryExercises.Integers

-- @region ex.integers.no_int_third
-- @solution Lumenary.Integers.no_int_third
/-- Show that `3` has no multiplicative inverse in the integers.
Hint: look at remainders on division by `3`. `Int.mul_emod_right` says `(a * b) % a = 0`. -/
theorem no_int_third : ¬ ∃ x : Int, 3 * x = 1 := by
  sorry
-- @endregion

end LumenaryExercises.Integers
