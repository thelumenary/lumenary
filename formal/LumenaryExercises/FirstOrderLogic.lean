/-
The Lumenary — Lean exercises: First-order logic.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FirstOrderLogic.lean`.
-/
import Lumenary.FirstOrderLogic

namespace LumenaryExercises.FirstOrderLogic

open Lumenary.FirstOrderLogic

-- @region ex.first_order_logic.all_imp_ex
-- @solution Lumenary.FirstOrderLogic.all_imp_ex
/-- Derive `∀x φ → ∃x φ` in the natural deduction system. Hint: `Derivable.impI`, then
`Derivable.exI (.var 0)`, then `Derivable.allE (.var 0)`, then `Derivable.assume`. -/
theorem all_imp_ex {L : Signature} (φ : Formula L) :
    Derivable [] (.imp (.all φ) (.ex φ)) := by
  sorry
-- @endregion

-- @region ex.first_order_logic.int_not_has_least
-- @solution Lumenary.FirstOrderLogic.int_not_hasLeast
/-- `(ℤ, <)` has no least element, as a statement about satisfaction. Hint: apply the
hypothesis to any environment, get a candidate `a`, and refute it with `a - 1`
(`show a - 1 < a by omega`). -/
theorem int_not_hasLeast : ¬ hasLeast.Holds (orderStructure ℤ) := by
  sorry
-- @endregion

end LumenaryExercises.FirstOrderLogic
