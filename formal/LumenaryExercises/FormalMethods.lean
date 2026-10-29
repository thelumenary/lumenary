/-
The Lumenary — Lean exercises: Formal methods.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FormalMethods.lean`.
-/
import Lumenary.FormalMethods

namespace LumenaryExercises.FormalMethods

open Lumenary.FormalMethods

-- @region ex.formal_methods.numval_has_type
-- @solution Lumenary.FormalMethods.numVal_hasType
/-- Every numeric value `succ (succ … zero)` has type `nat`.
Hint: `induction h` and use the typing rules `HasType.zero` and `HasType.succ`. -/
theorem numVal_hasType {t : Tm} (h : NumVal t) : HasType t .nat := by
  sorry
-- @endregion

-- @region ex.formal_methods.loop_forever_hoare
-- @solution Lumenary.FormalMethods.loopForever_hoare
/-- The triple `{True} while true do skip {False}` is valid as a partial-correctness triple.
Hint: unfold `Hoare` with `intro s t _ h` and use `loopForever_diverges`. -/
theorem loopForever_hoare : Hoare (fun _ => True) loopForever (fun _ => False) := by
  sorry
-- @endregion

end LumenaryExercises.FormalMethods
