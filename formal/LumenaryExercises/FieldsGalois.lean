/-
The Lumenary — Lean exercises: Fields and Galois theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FieldsGalois.lean`.
-/
import Lumenary.FieldsGalois

namespace LumenaryExercises.FieldsGalois

open IntermediateField

-- @region ex.fields_galois.field_hom_injective
-- @solution Lumenary.FieldsGalois.field_hom_injective
/-- A ring homomorphism from a field to a non-zero ring is injective.
Hint: first show the kernel is zero — if `f x = 0` and `x ≠ 0`, compute `1 = f (x * x⁻¹)`.
Then use `f (a - b) = f a - f b`. -/
theorem field_hom_injective {K R : Type*} [Field K] [Ring R] [Nontrivial R] (f : K →+* R) :
    Function.Injective f := by
  sorry
-- @endregion

-- @region ex.fields_galois.fixed_field_antitone
-- @solution Lumenary.FieldsGalois.fixed_field_antitone
/-- Bigger subgroups fix smaller fields.
Hint: `mem_fixedField_iff` turns membership into `∀ σ ∈ H, σ x = x`. -/
theorem fixed_field_antitone {F E : Type*} [Field F] [Field E] [Algebra F E]
    {H₁ H₂ : Subgroup Gal(E/F)} (h : H₁ ≤ H₂) : fixedField H₂ ≤ fixedField H₁ := by
  sorry
-- @endregion

end LumenaryExercises.FieldsGalois
