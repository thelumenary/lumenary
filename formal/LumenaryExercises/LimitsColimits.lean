/-
The Lumenary — Lean exercises: Limits and colimits.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LimitsColimits.lean`.
-/
import Lumenary.LimitsColimits

namespace LumenaryExercises.LimitsColimits

open Lumenary.LimitsColimits

universe u

variable {W X Y Z : Type u}

-- @region ex.limits_colimits.equalizer_universal
-- @solution Lumenary.LimitsColimits.equalizer_universal
/-- The universal property of the equaliser of types.
Hint: the map is `fun w => ⟨h w, congr_fun hh w⟩`. For uniqueness, take another `u` with
`Subtype.val ∘ u = h`, use `funext w`, and compare values with `Subtype.ext`. -/
theorem equalizer_universal (f g : X → Y) (h : W → X) (hh : f ∘ h = g ∘ h) :
    ∃! u : W → {x : X // f x = g x}, Subtype.val ∘ u = h := by
  sorry
-- @endregion

-- @region ex.limits_colimits.coequalizer_universal
-- @solution Lumenary.LimitsColimits.coequalizer_universal
/-- The universal property of the coequaliser of types.
Hint: existence is `Quot.lift h _`, where the missing proof says that related elements have the
same image (`rintro _ _ ⟨x, rfl, rfl⟩`). For uniqueness, use `funext q` and `Quot.ind`. -/
theorem coequalizer_universal (f g : X → Y) (h : Y → Z) (hh : h ∘ f = h ∘ g) :
    ∃! u : Quot (CoeqRel f g) → Z, u ∘ Quot.mk _ = h := by
  sorry
-- @endregion

end LumenaryExercises.LimitsColimits
