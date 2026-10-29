/-
The Lumenary — Lean exercises: Ratios, rates and proportional reasoning.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RatiosProportions.lean`.
-/
import Lumenary.RatiosProportions

namespace LumenaryExercises.RatiosProportions

open Lumenary.RatiosProportions

-- @region ex.ratios_proportions.proportional_zero
-- @solution Lumenary.RatiosProportions.proportional_zero
/-- The graph of a proportional relationship passes through the origin.
Hint: `obtain ⟨k, hk⟩ := hf`, then rewrite with `hk` and `Rat.mul_zero`. -/
theorem proportional_zero {f : Rat → Rat} (hf : IsProportional f) : f 0 = 0 := by
  sorry
-- @endregion

-- @region ex.ratios_proportions.proportional_add
-- @solution Lumenary.RatiosProportions.proportional_add
/-- Adding two rows of a ratio table gives another row.
Hint: after `obtain ⟨k, hk⟩ := hf`, rewrite `f (x + y)`, `f x` and `f y` with `hk`, then use
the distributive law `Rat.mul_add`. -/
theorem proportional_add {f : Rat → Rat} (hf : IsProportional f) (x y : Rat) :
    f (x + y) = f x + f y := by
  sorry
-- @endregion

end LumenaryExercises.RatiosProportions
