/-
The Lumenary — Lean exercises: Quiver representations (Tits forms and reflections).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/QuiverRepresentations.lean`.
-/
import Lumenary.QuiverRepresentations

namespace LumenaryExercises.QuiverRepresentations

open Lumenary.QuiverRepresentations (titsA2 titsD4)

-- @region ex.quiver_representations.tits_a2_pos
-- @solution Lumenary.QuiverRepresentations.titsA2_pos
/-- The Tits form `x² + y² - xy` of `A₂` is positive on non-zero vectors.
Hint: `4q = (2x - y)² + 3y²`; split into the cases `x ≠ 0` and `y ≠ 0`, and give `nlinarith`
the squares `sq_nonneg (x - y)`, `sq_nonneg x`, `sq_nonneg y`. -/
theorem titsA2_pos (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : 0 < titsA2 x y := by
  sorry
-- @endregion

-- @region ex.quiver_representations.tits_d4_reflect_leaf
-- @solution Lumenary.QuiverRepresentations.titsD4_reflect_leaf
/-- The reflection at the leaf `a`, `a ↦ c - a`, preserves the Tits form of `D₄`.
Hint: unfold `titsD4` and use `ring`. -/
theorem titsD4_reflect_leaf (a b c d : ℤ) : titsD4 (c - a) b c d = titsD4 a b c d := by
  sorry
-- @endregion

end LumenaryExercises.QuiverRepresentations
