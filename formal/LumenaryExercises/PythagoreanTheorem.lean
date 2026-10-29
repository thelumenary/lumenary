/-
The Lumenary — Lean exercises: the Pythagorean theorem.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/PythagoreanTheorem.lean`.
-/
import Lumenary.PythagoreanTheorem

namespace LumenaryExercises.PythagoreanTheorem

-- @region ex.pythagorean_theorem.not_right_example
-- @solution Lumenary.PythagoreanTheorem.not_right_example
/-- Show that `5² + 6² ≠ 8²`, so a triangle with sides `5, 6, 8` has no right angle.
Hint: these are particular numbers — `decide` can compute both sides. -/
theorem not_right_example : 5 ^ 2 + 6 ^ 2 ≠ 8 ^ 2 := by
  sorry
-- @endregion

-- @region ex.pythagorean_theorem.triple_scale
-- @solution Lumenary.PythagoreanTheorem.triple_scale
/-- Show that scaling a Pythagorean triple by `k` gives another triple.
Hint: a `calc` chain: `(k * a) ^ 2 + (k * b) ^ 2 = k ^ 2 * (a ^ 2 + b ^ 2)` (by `grind`), then
use `h`, then `k ^ 2 * c ^ 2 = (k * c) ^ 2` (by `grind`). -/
theorem triple_scale (a b c k : Nat) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    (k * a) ^ 2 + (k * b) ^ 2 = (k * c) ^ 2 := by
  sorry
-- @endregion

end LumenaryExercises.PythagoreanTheorem
