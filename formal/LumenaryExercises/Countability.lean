/-
The Lumenary — Lean exercises: Countability and Cantor's diagonal argument.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Countability.lean`.
-/
import Lumenary.Countability

namespace LumenaryExercises.Countability

open Function

-- @region ex.countability.diagonal_ne
-- @solution Lumenary.Countability.diagonal_ne
/-- The diagonal sequence `fun n => !(s n n)` differs from the `n`-th sequence of the list.
Hint: `intro h`, evaluate both sides at `n` with `congrFun h n`, then split on the value of
`s n n` with `cases hs : s n n` and `simp`. -/
theorem diagonal_ne (s : ℕ → ℕ → Bool) (n : ℕ) : (fun k => !(s k k)) ≠ s n := by
  sorry
-- @endregion

-- @region ex.countability.cantor
-- @solution Lumenary.Countability.cantor
/-- Cantor's theorem: no function from `α` to its power set is surjective.
Hint: `intro hf`, then `obtain ⟨a, ha⟩ := hf {x | x ∉ f x}` and ask whether `a ∈ f a`. -/
theorem cantor {α : Type*} (f : α → Set α) : ¬ Surjective f := by
  sorry
-- @endregion

end LumenaryExercises.Countability
