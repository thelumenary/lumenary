/-
The Lumenary — Lean exercises: Sheaves.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Sheaves.lean`.
-/
import Lumenary.Sheaves

namespace LumenaryExercises.Sheaves

open Lumenary.Sheaves TopologicalSpace

-- @region ex.sheaves.sec_empty
-- @solution Lumenary.Sheaves.sec_empty
/-- Prove that a sheaf has exactly one section over the empty open set.
Hint: apply `hF` to `V = ⊥` covered by the empty family indexed by `PEmpty`: every condition
indexed by `i : PEmpty` is proved by `i.elim`. -/
theorem sec_empty {X : Type} [TopologicalSpace X] (F : Presheaf.{0, 0} X) (hF : IsSheaf F) :
    Nonempty (F.sec ⊥) ∧ ∀ s t : F.sec ⊥, s = t := by
  sorry
-- @endregion

-- @region ex.sheaves.const_not_sheaf
-- @solution Lumenary.Sheaves.const_not_sheaf
/-- Prove that the constant presheaf with values in `Bool` is not a sheaf.
Hint: `Lumenary.Sheaves.sec_empty` says a sheaf has only one section over `∅`; what are the
sections of the constant presheaf over `∅`? -/
theorem const_bool_not_sheaf {X : Type} [TopologicalSpace X] :
    ¬ IsSheaf (constPresheaf (X := X) Bool) := by
  sorry
-- @endregion

end LumenaryExercises.Sheaves
