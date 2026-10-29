/-
The Lumenary — Lean exercises: Monads (algebras for the list monad).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Monads.lean`.
-/
import Lumenary.Monads

namespace LumenaryExercises.Monads

open Lumenary.Monads (ListAlgebra)

universe u

variable {X : Type u}

-- @region ex.monads.act_cons
-- @solution Lumenary.Monads.ListAlgebra.act_cons
/-- In a list algebra, evaluating `x :: xs` is evaluating the two-element list `[x, act xs]`.
Hint: rewrite `[x, A.act xs]` as `[[x], xs].map A.act` (using the unit law `A.unit x`), then use
the associativity law `A.assoc [[x], xs]`; `simp` can finish the list bookkeeping. -/
theorem act_cons (A : ListAlgebra X) (x : X) (xs : List X) :
    A.act (x :: xs) = A.act [x, A.act xs] := by
  sorry
-- @endregion

-- @region ex.monads.option_unit
-- @solution Lumenary.Monads.optionAlgebraEquiv
/-- An algebra for the maybe monad is determined by its value on `none`: show that its evaluation
map is `fun o => o.getD (A.act none)`.
Hint: `funext o`, then `cases o`; one case is `rfl` and the other is the unit law. -/
theorem option_act_eq (A : Lumenary.Monads.OptionAlgebra X) :
    A.act = fun o => o.getD (A.act none) := by
  sorry
-- @endregion

end LumenaryExercises.Monads
