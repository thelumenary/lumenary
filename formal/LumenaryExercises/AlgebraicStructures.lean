/-
The Lumenary — Lean exercises: Algebraic structures.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AlgebraicStructures.lean`.
-/
import Lumenary.AlgebraicStructures

namespace LumenaryExercises.AlgebraicStructures

-- @region ex.algebraic_structures.inverse_unique
-- @solution Lumenary.AlgebraicStructures.inverse_unique
/-- In a monoid, a left inverse and a right inverse of the same element are equal.
Hint: a `calc` block `b = b * 1 = b * (a * c) = (b * a) * c = 1 * c = c`, using `mul_one`,
`mul_assoc` and `one_mul`. -/
theorem inverse_unique {M : Type*} [Monoid M] {a b c : M} (hb : b * a = 1) (hc : a * c = 1) :
    b = c := by
  sorry
-- @endregion

-- @region ex.algebraic_structures.hom_map_one
-- @solution Lumenary.AlgebraicStructures.hom_map_one
/-- A map between groups that preserves products sends `1` to `1`.
Hint: show `f 1 * f 1 = f 1 * 1`, then use `mul_left_cancel`. -/
theorem hom_map_one {G H : Type*} [Group G] [Group H] (f : G → H)
    (hf : ∀ a b, f (a * b) = f a * f b) : f 1 = 1 := by
  sorry
-- @endregion

end LumenaryExercises.AlgebraicStructures
