/-
The Lumenary — Lean exercises: Triangulated categories.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/TriangulatedCategories.lean`.
-/
import Lumenary.TriangulatedCategories

open CategoryTheory Limits Pretriangulated

namespace LumenaryExercises.TriangulatedCategories

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

-- @region ex.triangulated_categories.is_split_epi_of_epi
-- @solution Lumenary.TriangulatedCategories.isSplitEpi_of_epi
/-- Every epimorphism in a pretriangulated category is split.
Hint: complete `f` to a distinguished triangle with `distinguished_cocone_triangle f`; show the
second map is zero using `cancel_epi f` and `comp_distTriang_mor_zero₁₂`; then factor `𝟙 Y`
through `f` with `Lumenary.TriangulatedCategories.hom_exact_middle`. -/
theorem isSplitEpi_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  sorry
-- @endregion

end LumenaryExercises.TriangulatedCategories
