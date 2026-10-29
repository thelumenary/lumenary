/-
The Lumenary — Lean exercises: Higher categories.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/HigherCategories.lean`.
-/
import Lumenary.HigherCategories

namespace LumenaryExercises.HigherCategories

open CategoryTheory

-- @region ex.higher_categories.units_coincide
-- @solution Lumenary.HigherCategories.units_coincide
/-- The first step of Eckmann–Hilton: two unital operations satisfying the interchange law have
the same unit. Hint: start a `calc` with `e₁ = m₁ e₁ e₁`, rewrite each `e₁` inside as a product
in `m₂` (`e₁ = m₂ e₂ e₁` and `e₁ = m₂ e₁ e₂`), and apply `interchange e₂ e₁ e₁ e₂`. -/
theorem units_coincide {X : Type*} (m₁ m₂ : X → X → X) (e₁ e₂ : X)
    (h₁l : ∀ a, m₁ e₁ a = a) (h₁r : ∀ a, m₁ a e₁ = a)
    (h₂l : ∀ a, m₂ e₂ a = a) (h₂r : ∀ a, m₂ a e₂ = a)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    e₁ = e₂ := by
  sorry
-- @endregion

-- @region ex.higher_categories.nat_trans_id_comm
-- @solution Lumenary.HigherCategories.nat_trans_id_comm
/-- Natural transformations from the identity functor to itself commute. Hint: after `ext X`,
the goal is `α.app X ≫ β.app X = β.app X ≫ α.app X` (up to unfolding); this is the naturality
square of `α` at the morphism `β.app X : X ⟶ X`, i.e. `α.naturality (β.app X)`. -/
theorem nat_trans_id_comm {C : Type*} [Category C] (α β : 𝟭 C ⟶ 𝟭 C) :
    α ≫ β = β ≫ α := by
  sorry
-- @endregion

end LumenaryExercises.HigherCategories
