/-
The Lumenary — Lean exercises: Categorical logic.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CategoricalLogic.lean`.
-/
import Lumenary.CategoricalLogic

namespace LumenaryExercises.CategoricalLogic

open Lumenary.CategoricalLogic

-- @region ex.categorical_logic.frobenius
-- @solution Lumenary.CategoricalLogic.frobenius
/-- **Frobenius reciprocity**: `∃_f (S ∧ f*T) = ∃_f S ∧ T`.
Hint: `ext y`, then `constructor`; `rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩` takes the left side apart. -/
theorem frobenius {X Y : Type} (f : X → Y) (S : Set X) (T : Set Y) :
    f '' (S ∩ f ⁻¹' T) = f '' S ∩ T := by
  sorry
-- @endregion

-- @region ex.categorical_logic.le_compl_compl_heyting
-- @solution Lumenary.CategoricalLogic.le_compl_compl_heyting
/-- `a ≤ ¬¬a` in every Heyting algebra.
Hint: rewrite `¬¬a` as `¬a ⇨ ⊥` (`himp_bot`), then use `le_himp_iff`. -/
theorem le_compl_compl_heyting {α : Type*} [HeytingAlgebra α] (a : α) : a ≤ aᶜᶜ := by
  sorry
-- @endregion

-- @region ex.categorical_logic.derives_imp_self
-- @solution Lumenary.CategoricalLogic.derives_imp_self
/-- Derive `φ → φ` in the natural-deduction system `Derives`.
Hint: one introduction rule and one hypothesis. -/
theorem derives_imp_self (φ : Form) : Derives [] (.imp φ φ) := by
  sorry
-- @endregion

end LumenaryExercises.CategoricalLogic
