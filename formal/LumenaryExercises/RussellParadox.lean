/-
The Lumenary — Lean exercises: Russell's paradox.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RussellParadox.lean`.
-/
import Lumenary.RussellParadox

namespace LumenaryExercises.RussellParadox

-- @region ex.russell_paradox.iff_not_self
-- @solution Lumenary.RussellParadox.not_iff_not_self
/-- No statement is equivalent to its own negation.
Hint: `intro h`; first prove `¬ p` (assume `hp : p` and use `h.mp hp hp`), then use `h.mpr`. -/
theorem not_iff_not_self (p : Prop) : ¬ (p ↔ ¬ p) := by
  sorry
-- @endregion

-- @region ex.russell_paradox.no_barber
-- @solution Lumenary.RussellParadox.no_barber
/-- There is no barber who shaves exactly those who do not shave themselves.
Hint: `rintro ⟨b, hb⟩` and look at `hb b`. -/
theorem no_barber {Person : Type*} (shaves : Person → Person → Prop) :
    ¬ ∃ b, ∀ p, shaves b p ↔ ¬ shaves p p := by
  sorry
-- @endregion

end LumenaryExercises.RussellParadox
