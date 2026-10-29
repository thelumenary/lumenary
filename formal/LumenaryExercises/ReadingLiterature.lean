/-
The Lumenary — Lean exercises: Reading the mathematical literature.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ReadingLiterature.lean`.
-/
import Lumenary.ReadingLiterature

namespace LumenaryExercises.ReadingLiterature

open Lumenary.ReadingLiterature

-- @region ex.reading_literature.zagier_of_lt
-- @solution Lumenary.ReadingLiterature.zagier_of_lt
/-- Compute Zagier's map in its first case.
Hint: `simp [zagier, h]` unfolds the definition and selects the first branch. -/
theorem zagier_of_lt {x y z : ℕ} (h : x + z < y) :
    zagier (x, y, z) = (x + 2 * z, z, y - x - z) := by
  sorry
-- @endregion

-- @region ex.reading_literature.nat_sub_add_needs_hypothesis
-- @solution Lumenary.ReadingLiterature.nat_sub_add_needs_hypothesis
/-- In `ℕ`, `(a - b) + b = a` is not an identity.
Hint: `intro h`, specialise `h` to `a = 3`, `b = 5`, and let `omega` finish. -/
theorem nat_sub_add_needs_hypothesis : ¬ ∀ a b : ℕ, a - b + b = a := by
  sorry
-- @endregion

end LumenaryExercises.ReadingLiterature
