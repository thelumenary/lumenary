/-
The Lumenary — Lean exercises: Knot theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/KnotTheory.lean`.
-/
import Lumenary.KnotTheory

namespace LumenaryExercises.KnotTheory

open Lumenary.KnotTheory

-- @region ex.knot_theory.trefoil_tricolourable
-- @solution Lumenary.KnotTheory.trefoil_tricolourable
/-- Show that the trefoil diagram is tricolourable.
Hint: give the colouring `![0, 1, 2]`; each remaining goal can be closed by `decide`. -/
theorem trefoil_tricolourable :
    ∃ c : Fin 3 → ZMod 3, IsFoxColouring trefoilDiagram 3 c ∧ ∃ i j, c i ≠ c j := by
  sorry
-- @endregion

-- @region ex.knot_theory.reidemeister_two
-- @solution Lumenary.KnotTheory.reidemeister_two
/-- The algebra of the second Reidemeister move.
Hint: for `→`, use `linear_combination` with `h1` and `h2`; for `←`, substitute and use `ring`. -/
theorem reidemeister_two {R : Type*} [CommRing R] (x a m b : R) :
    (2 * x = a + m ∧ 2 * x = m + b) ↔ (m = 2 * x - a ∧ b = a) := by
  sorry
-- @endregion

end LumenaryExercises.KnotTheory
