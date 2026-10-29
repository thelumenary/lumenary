/-
The Lumenary — Lean exercises: The axiom of choice.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AxiomOfChoice.lean`
(the `@solution` line names the solved theorem). Try to solve them without using
`Classical.choice`: check with `#print axioms` afterwards.
-/
import Lumenary.AxiomOfChoice

namespace LumenaryExercises.AxiomOfChoice

open Lumenary.AxiomOfChoice

universe u

-- @region ex.axiom_of_choice.split_of_choice
-- @solution Lumenary.AxiomOfChoice.split_of_choice
/-- Choice implies that every surjection has a section.
Hint: apply the choice principle `hc` to the family of fibres `fun b => {a // p a = b}`. -/
theorem split_of_choice : ChoiceFunctions.{u} → SurjectionsSplit.{u} := by
  sorry
-- @endregion

-- @region ex.axiom_of_choice.choice_of_split
-- @solution Lumenary.AxiomOfChoice.choice_of_split
/-- If every surjection has a section, then choice holds.
Hint: the projection `Sigma.fst : (Σ i, X i) → ι` is surjective. If `s` is a section, then
`(s i).2 : X (s i).1`, and you can transport it along `(s i).1 = i` with `▸`. -/
theorem choice_of_split : SurjectionsSplit.{u} → ChoiceFunctions.{u} := by
  sorry
-- @endregion

end LumenaryExercises.AxiomOfChoice
