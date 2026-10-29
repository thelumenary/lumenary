/-
The Lumenary — Lean exercises: Universal properties.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/UniversalProperties.lean`.
-/
import Lumenary.UniversalProperties

namespace LumenaryExercises.UniversalProperties

universe u

-- @region ex.universal_properties.prod_universal
-- @solution Lumenary.UniversalProperties.prod_universal
/-- The universal property of the product of sets. Hint: the witness is
`fun x => (f x, g x)`; for uniqueness use `funext` and `Prod.ext`. -/
theorem prod_universal {X A B : Type u} (f : X → A) (g : X → B) :
    ∃! h : X → A × B, Prod.fst ∘ h = f ∧ Prod.snd ∘ h = g := by
  sorry
-- @endregion

-- @region ex.universal_properties.quotient_universal
-- @solution Lumenary.UniversalProperties.quotient_universal
/-- The universal property of a quotient set. Hint: existence is `Quotient.lift f hf`;
for uniqueness, `funext c` and then `induction c using Quotient.ind`. -/
theorem quotient_universal {X Y : Type u} (s : Setoid X) (f : X → Y)
    (hf : ∀ a b, s a b → f a = f b) :
    ∃! g : Quotient s → Y, g ∘ Quotient.mk s = f := by
  sorry
-- @endregion

end LumenaryExercises.UniversalProperties
