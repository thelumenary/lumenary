/-
The Lumenary — Lean exercises: Category (products of types).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Category.lean`.
-/
import Lumenary.Category

namespace LumenaryExercises.Category

open Lumenary.Category (pair)

universe u v w

variable {Z : Type u} {A : Type v} {B : Type w}

-- @region ex.category.snd_comp_pair
-- @solution Lumenary.Category.snd_comp_pair
/-- Following `pair f g` by the second projection gives back `g`.
Hint: unfold the definitions — both sides send `z` to `g z`. -/
theorem snd_comp_pair (f : Z → A) (g : Z → B) : Prod.snd ∘ pair f g = g := by
  sorry
-- @endregion

end LumenaryExercises.Category
