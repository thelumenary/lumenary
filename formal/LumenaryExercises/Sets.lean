/-
The Lumenary — Lean exercises: Sets.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Sets.lean`
(the `@solution` line names the solved theorem).
-/
import Lumenary.Sets

namespace LumenaryExercises.Sets

open Lumenary.Sets

universe u

variable {α : Type u}

-- @region ex.sets.inter_subset_right
-- @solution Lumenary.Sets.inter_subset_right
/-- Show that `A ∩ B ⊆ B`.
Hint: start with `intro x hx`. What does `hx : x ∈ A ∩ B` tell you? -/
theorem inter_subset_right (A B : Set α) : A ∩ B ⊆ B := by
  sorry
-- @endregion

-- @region ex.sets.union_comm
-- @solution Lumenary.Sets.union_comm
/-- Show that union is commutative.
Hint: `apply ext`, then `intro x` and `constructor`; `Or.symm` swaps the two sides of an "or". -/
theorem union_comm (A B : Set α) : A ∪ B = B ∪ A := by
  sorry
-- @endregion

-- @region ex.sets.compl_union
-- @solution Lumenary.Sets.compl_union
/-- De Morgan's law: not being in `A ∪ B` means being in neither `A` nor `B`.
Hint: `x ∈ Aᶜ` means `x ∈ A → False`. You do not need classical logic for this one. -/
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  sorry
-- @endregion

end LumenaryExercises.Sets
