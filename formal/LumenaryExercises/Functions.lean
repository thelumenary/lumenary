/-
The Lumenary — Lean exercises: Functions and composition.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Composition.lean`.
-/
import Lumenary.Composition

namespace LumenaryExercises.Functions

open Function

universe u₁ u₂ u₃

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃}

-- @region ex.functions.injective_comp
-- @solution Lumenary.Composition.injective_comp
/-- A composite of injective functions is injective.
Hint: `intro a b h`; here `h : g (f a) = g (f b)`. Use `hg` first, then `hf`. -/
theorem injective_comp {f : α → β} {g : β → γ} (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by
  sorry
-- @endregion

-- @region ex.functions.surjective_comp
-- @solution Lumenary.Composition.surjective_comp
/-- A composite of surjective functions is surjective.
Hint: `intro c`, then `obtain ⟨b, hb⟩ := hg c` and `obtain ⟨a, ha⟩ := hf b`. -/
theorem surjective_comp {f : α → β} {g : β → γ} (hg : Surjective g) (hf : Surjective f) :
    Surjective (g ∘ f) := by
  sorry
-- @endregion

end LumenaryExercises.Functions
