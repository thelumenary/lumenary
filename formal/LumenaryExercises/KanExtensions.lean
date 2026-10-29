/-
The Lumenary — Lean exercises: Kan extensions.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/KanExtensions.lean`.
-/
import Lumenary.KanExtensions

namespace LumenaryExercises.KanExtensions

open Lumenary.KanExtensions

-- @region ex.kan_extensions.ran_monotone
-- @solution Lumenary.KanExtensions.ran_monotone
/-- Show that the pointwise right Kan extension `ran k f d = ⨅ { f c | d ≤ k c }` is monotone
in `d`. Hint: `le_iInf₂` and `iInf₂_le_of_le`; if `d ≤ d'` and `d' ≤ k c` then `d ≤ k c`. -/
theorem ran_monotone {C D E : Type*} [Preorder D] [CompleteLattice E] (k : C → D) (f : C → E) :
    Monotone (ran k f) := by
  sorry
-- @endregion

-- @region ex.kan_extensions.right_adjoint_eq_lan
-- @solution Lumenary.KanExtensions.right_adjoint_eq_lan
/-- Show that a right adjoint between complete lattices is the left Kan extension of the
identity along its left adjoint: `G a = ⨆ { x | F x ≤ a }`.
Hint: `funext`, `le_antisymm`, and the Galois connection facts `gc.l_u_le` and `gc x a`. -/
theorem right_adjoint_eq_lan {A X : Type*} [CompleteLattice A] [CompleteLattice X]
    {F : X → A} {G : A → X} (gc : GaloisConnection F G) : G = lan F id := by
  sorry
-- @endregion

end LumenaryExercises.KanExtensions
