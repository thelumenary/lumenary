/-
The Lumenary — Lean exercises: Set-builder notation, quantifiers and infinite sets.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Quantifiers.lean`.
-/
import Lumenary.Quantifiers

namespace LumenaryExercises.Quantifiers

-- @region ex.quantifiers.int_forall_exists
-- @solution Lumenary.Quantifiers.int_forall_exists
/-- For every integer `x` there is an integer `y` with `x + y = 0`.
Hint: `intro x`, then provide the witness with `exact ⟨-x, by omega⟩`. The `y` you choose may
depend on `x`. -/
theorem int_forall_exists : ∀ x : Int, ∃ y, x + y = 0 := by
  sorry
-- @endregion

-- @region ex.quantifiers.int_not_exists_forall
-- @solution Lumenary.Quantifiers.int_not_exists_forall
/-- But no single integer `y` works for every `x`.
Hint: `intro ⟨y, hy⟩` gives you `hy : ∀ x, x + y = 0`. Use it twice, with `have h0 := hy 0` and
`have h1 := hy 1`; then `omega` sees the contradiction. -/
theorem int_not_exists_forall : ¬ ∃ y : Int, ∀ x : Int, x + y = 0 := by
  sorry
-- @endregion

end LumenaryExercises.Quantifiers
