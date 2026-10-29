/-
The Lumenary — Lean exercises: Diagrams where paths agree.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CommutativeDiagramsIntro.lean`.
-/
import Lumenary.CommutativeDiagramsIntro

namespace LumenaryExercises.CommutativeDiagramsIntro

open Lumenary.CommutativeDiagramsIntro

-- @region ex.commutative_diagrams_intro.add_one_not_preserves
-- @solution Lumenary.CommutativeDiagramsIntro.add_one_not_preserves
/-- Show that `x ↦ x + 1` does not preserve addition.
Hint: `intro h`, then `have h00 := h 0 0` — this says `(0 + 0) + 1 = (0 + 1) + (0 + 1)`.
`revert h00` and `decide` finish the job (or use `omega` on `h00`). -/
theorem add_one_not_preserves : ¬ PreservesAdd (fun x => x + 1) := by
  sorry
-- @endregion

-- @region ex.commutative_diagrams_intro.paste
-- @solution Lumenary.CommutativeDiagramsIntro.paste
/-- Two commuting squares side by side make a commuting rectangle.
Hint: `intro x`. The goal is `c (g (f x)) = g' (f' (a x))`. First use `hright (f x)`, which says
`c (g (f x)) = g' (b (f x))`, then rewrite with `hleft x : b (f x) = f' (a x)`. A `calc` block
with two steps works well. -/
theorem paste {A B C D E F : Type} {f : A → B} {g : B → C} {f' : D → E} {g' : E → F}
    {a : A → D} {b : B → E} {c : C → F}
    (hleft : SquareCommutes f b a f') (hright : SquareCommutes g c b g') :
    SquareCommutes (fun x => g (f x)) c a (fun x => g' (f' x)) := by
  sorry
-- @endregion

end LumenaryExercises.CommutativeDiagramsIntro
