/-
The Lumenary — Lean exercises: Relations, equivalence relations and partitions.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/EquivalenceRelations.lean`.
-/
import Lumenary.EquivalenceRelations

namespace LumenaryExercises.EquivalenceRelations

open Lumenary.EquivalenceRelations

-- @region ex.equivalence_relations.same_remainder_equivalence
-- @solution Lumenary.EquivalenceRelations.same_remainder_equivalence
/-- Show that "same remainder on division by `n`" is an equivalence relation.
Hint: `SameRemainder n a b` unfolds to `a % n = b % n`, so this is "same output" for the function
`a ↦ a % n`. Either use `same_output_equivalence`, or give the three fields yourself:
`refl := fun _ => rfl`, and use `Eq.symm` and `Eq.trans` for the other two. -/
theorem same_remainder_equivalence (n : Int) : Equivalence (SameRemainder n) := by
  sorry
-- @endregion

-- @region ex.equivalence_relations.refl_of_symm_trans
-- @solution Lumenary.EquivalenceRelations.refl_of_symm_trans
/-- Symmetry and transitivity give reflexivity **when every element is related to something**.
Hint: `intro a`, then `obtain ⟨b, hab⟩ := hsome a`. Now `hs a b hab : R b a`, and `ht` chains
`a R b` with `b R a`. -/
theorem refl_of_symm_trans {α : Type} (R : α → α → Prop) (hs : Symmetric R) (ht : Transitive R)
    (hsome : ∀ a, ∃ b, R a b) : Reflexive R := by
  sorry
-- @endregion

end LumenaryExercises.EquivalenceRelations
