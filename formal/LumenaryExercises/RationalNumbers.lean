/-
The Lumenary — Lean exercises: Rational numbers.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RationalNumbers.lean`.
-/
import Lumenary.RationalNumbers

namespace LumenaryExercises.RationalNumbers

-- @region ex.rational_numbers.zero_no_reciprocal
-- @solution Lumenary.RationalNumbers.zero_no_reciprocal
/-- Show that `0` has no reciprocal among the rational numbers.
Hint: after `intro ⟨r, h⟩`, rewrite `h` with `Rat.zero_mul`; then `h : 0 = 1`, and
`absurd h (by decide)` finishes. -/
theorem zero_no_reciprocal : ¬ ∃ r : Rat, 0 * r = 1 := by
  sorry
-- @endregion

-- @region ex.rational_numbers.exists_between
-- @solution Lumenary.RationalNumbers.exists_between
/-- Density: between two different rationals there is another one.
Hint: use the average `(a + b) / 2` and the theorem `Lumenary.RationalNumbers.average_between`. -/
theorem exists_between {a b : Rat} (h : a < b) : ∃ c : Rat, a < c ∧ c < b := by
  sorry
-- @endregion

end LumenaryExercises.RationalNumbers
