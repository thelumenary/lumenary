/-
The Lumenary — Lean exercises: Monoidal categories (the Eckmann–Hilton argument).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/MonoidalCategories.lean`.
-/
import Lumenary.MonoidalCategories

namespace LumenaryExercises.MonoidalCategories

universe u

-- @region ex.monoidal_categories.units_agree
-- @solution Lumenary.MonoidalCategories.eckmann_hilton
/-- The first step of Eckmann–Hilton: two unital operations satisfying the interchange law have
the same unit.
Hint: specialise `interchange` to `e₂ e₁ e₁ e₂` and simplify both sides with the unit laws
(`rw [h₂l, h₂r, h₁l, h₁r, ...] at h`). -/
theorem units_agree {X : Type u} (m₁ m₂ : X → X → X) (e₁ e₂ : X)
    (h₁l : ∀ x, m₁ e₁ x = x) (h₁r : ∀ x, m₁ x e₁ = x)
    (h₂l : ∀ x, m₂ e₂ x = x) (h₂r : ∀ x, m₂ x e₂ = x)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    e₁ = e₂ := by
  sorry
-- @endregion

end LumenaryExercises.MonoidalCategories
