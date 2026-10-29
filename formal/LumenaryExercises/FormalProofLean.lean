/-
The Lumenary — Lean exercises: Formalising mathematics in Lean and Mathlib.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FormalProofLean.lean`.
-/
import Lumenary.FormalProofLean

namespace LumenaryExercises.FormalProofLean

open Function

-- @region ex.formal_proof_lean.surjective_comp
-- @solution Lumenary.FormalProofLean.surjective_comp
/-- Prove that a composite of surjections is surjective.
Hint: `intro z`, then use `obtain ⟨y, hy⟩ := hg z` and `obtain ⟨x, hx⟩ := hf y`, and provide
`x` as the witness. -/
theorem surjective_comp {α β γ : Type*} {f : α → β} {g : β → γ} (hg : Surjective g)
    (hf : Surjective f) : Surjective (g ∘ f) := by
  sorry
-- @endregion

-- @region ex.formal_proof_lean.exists_forall_imp
-- @solution Lumenary.FormalProofLean.exists_forall_imp
/-- Prove that `∃ x, ∀ y, P x y` implies `∀ y, ∃ x, P x y`.
Hint: `rintro ⟨x, hx⟩ y`, then `exact ⟨x, hx y⟩`. -/
theorem exists_forall_imp {α β : Type*} (P : α → β → Prop) :
    (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  sorry
-- @endregion

-- @region ex.formal_proof_lean.inv_unique
-- @solution Lumenary.FormalProofLean.inv_unique
/-- Prove that in a monoid a left inverse and a right inverse of the same element agree.
Hint: a `calc` chain `b = b * (a * c) = b * a * c = c`, using `mul_one`, `mul_assoc` and
`one_mul`. -/
theorem inv_unique {M : Type*} [Monoid M] {a b c : M} (hb : b * a = 1) (hc : a * c = 1) :
    b = c := by
  sorry
-- @endregion

end LumenaryExercises.FormalProofLean
