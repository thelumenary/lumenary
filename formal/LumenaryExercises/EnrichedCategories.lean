/-
The Lumenary — Lean exercises: Enriched categories (Lawvere metric spaces).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/EnrichedCategories.lean`.
-/
import Lumenary.EnrichedCategories

namespace LumenaryExercises.EnrichedCategories

open Lumenary.EnrichedCategories (LawvereMetric)

universe u

-- @region ex.enriched_categories.underlying_trans
-- @solution Lumenary.EnrichedCategories.underlying_preorder
/-- In a Lawvere metric space, "distance zero" is transitive: this is composition in the
underlying ordinary category.
Hint: `apply le_antisymm _ zero_le`, then use `M.triangle x y z` and rewrite with the
hypotheses. -/
theorem underlying_trans {X : Type u} (M : LawvereMetric X) (x y z : X)
    (hxy : M.d x y = 0) (hyz : M.d y z = 0) : M.d x z = 0 := by
  sorry
-- @endregion

end LumenaryExercises.EnrichedCategories
