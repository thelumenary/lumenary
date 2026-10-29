/-
The Lumenary — Lean exercises: Rings.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Rings.lean`.
-/
import Lumenary.Rings

namespace LumenaryExercises.Rings

-- @region ex.rings.unit_mul_eq_zero
-- @solution Lumenary.Rings.unit_mul_eq_zero
/-- A unit is not a zero divisor.
Hint: `obtain ⟨v, rfl⟩ := hu`, then write `a = (v⁻¹ * v) * a` and reassociate. -/
theorem unit_mul_eq_zero {R : Type*} [Ring R] {u a : R} (hu : IsUnit u) (h : u * a = 0) :
    a = 0 := by
  sorry
-- @endregion

-- @region ex.rings.eq_top_of_unit_mem
-- @solution Lumenary.Rings.eq_top_of_unit_mem
/-- An ideal containing a unit is the whole ring.
Hint: `Ideal.eq_top_iff_one` reduces the goal to `1 ∈ I`; use `I.mul_mem_left`. -/
theorem eq_top_of_unit_mem {R : Type*} [CommRing R] (I : Ideal R) {u : R} (hu : IsUnit u)
    (h : u ∈ I) : I = ⊤ := by
  sorry
-- @endregion

end LumenaryExercises.Rings
