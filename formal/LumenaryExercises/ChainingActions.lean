/-
The Lumenary — Lean exercises: One thing after another.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ChainingActions.lean`.
-/
import Lumenary.ChainingActions

namespace LumenaryExercises.ChainingActions

open Lumenary.ChainingActions

-- @region ex.chaining_actions.start_at_three
-- @solution Lumenary.ChainingActions.start_at_three
/-- Starting at 3, check where the two chains end.
Hint: Lean can follow the chains itself — try `decide`. -/
theorem start_at_three : andThen addFive double 3 = 16 ∧ andThen double addFive 3 = 11 := by
  sorry
-- @endregion

-- @region ex.chaining_actions.four_quarter_turns
-- @solution Lumenary.ChainingActions.four_quarter_turns
/-- Show that four quarter turns do nothing.
Hint: there are only four directions. `cases d <;> rfl` checks each one. -/
theorem four_quarter_turns (d : Dir) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn d))) = d := by
  sorry
-- @endregion

-- @region ex.chaining_actions.socks_and_shoes
-- @solution Lumenary.ChainingActions.socks_and_shoes
/-- Prove the socks-and-shoes rule.
Hint: after `intro x` and `unfold andThen`, the goal is `uf (ug (g (f x))) = x`. Rewrite with
`hg (f x)` (taking off the shoes) and then with `hf x` (taking off the socks). -/
theorem socks_and_shoes {α : Type} {f g uf ug : α → α}
    (hf : Undoes uf f) (hg : Undoes ug g) : Undoes (andThen ug uf) (andThen f g) := by
  sorry
-- @endregion

end LumenaryExercises.ChainingActions
