/-
The Lumenary — Lean exercises: Function machines in sequence.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ChainingFunctions.lean`.
-/
import Lumenary.ChainingFunctions

namespace LumenaryExercises.ChainingFunctions

open Lumenary.ChainingFunctions

-- @region ex.chaining_functions.add_undoes_sub
-- @solution Lumenary.ChainingFunctions.add_undoes_sub
/-- Show that "add 3" undoes "subtract 3".
Hint: `intro a`, then `show a - 3 + 3 = a` to unfold the definitions, and finish with `omega`. -/
theorem add_undoes_sub : Undoes (fun x : Int => x + 3) (fun x => x - 3) := by
  sorry
-- @endregion

-- @region ex.chaining_functions.undo_chain
-- @solution Lumenary.ChainingFunctions.undo_chain
/-- Socks and shoes: "`f`, then `g`" is undone by "`g'`, then `f'`".
Hint: `intro a`. The goal unfolds to `f' (g' (g (f a))) = a`. Rewrite with `hg (f a)`, which says
`g' (g (f a)) = f a`, and finish with `hf a`. You may need `show f' (g' (g (f a))) = a` first. -/
theorem undo_chain {α β γ : Type} {f : α → β} {g : β → γ} {f' : β → α} {g' : γ → β}
    (hf : Undoes f' f) (hg : Undoes g' g) : Undoes (andThen g' f') (andThen f g) := by
  sorry
-- @endregion

end LumenaryExercises.ChainingFunctions
