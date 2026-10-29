/-
The Lumenary — Lean exercises: ∞-categories.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/InfinityCategories.lean`.
-/
import Lumenary.InfinityCategories

namespace LumenaryExercises.InfinityCategories

open CategoryTheory SSet Lumenary.InfinityCategories

-- @region ex.infinity_categories.groupoid_outer_horn_right
-- @solution Lumenary.InfinityCategories.groupoid_outer_horn_right
/-- Fill the outer horn `Λ[2, 2]` in the nerve of a groupoid: given `g : x₁ ⟶ x₂` and
`h : x₀ ⟶ x₂`, there is exactly one `f` with a 2-simplex `(f, g, h)`. Hint: use
`nerve_triangle_iff` to turn "there is a 2-simplex" into `f ≫ g = h`, take
`f := h ≫ Groupoid.inv g`, and finish the computations with `simp`. -/
theorem groupoid_outer_horn_right {G : Type} [Groupoid G] {x₀ x₁ x₂ : G}
    (g : x₁ ⟶ x₂) (h : x₀ ⟶ x₂) :
    ∃! f : x₀ ⟶ x₁,
      Nonempty (Edge.CompStruct (nerve.edgeMk f) (nerve.edgeMk g) (nerve.edgeMk h)) := by
  sorry
-- @endregion

end LumenaryExercises.InfinityCategories
