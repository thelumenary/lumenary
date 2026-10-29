/-
The Lumenary — Lean exercises: Vectors and coordinate geometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Vectors.lean`.
-/
import Lumenary.Vectors

namespace LumenaryExercises.Vectors

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- @region ex.vectors.pythagoras_iff_perp
-- @solution Lumenary.Vectors.pythagoras_iff_perp
/-- Pythagoras with vectors and its converse: `|u + v|² = |u|² + |v|²` iff `u · v = 0`.
Hint: `norm_add_sq_real` expands `‖u + v‖ ^ 2` as `‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2`. -/
theorem pythagoras_iff_perp (u v : V) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 ↔ ⟪u, v⟫ = 0 := by
  sorry
-- @endregion

-- @region ex.vectors.parallelogram_diagonals_bisect
-- @solution Lumenary.Vectors.parallelogram_diagonals_bisect
/-- The diagonals of a parallelogram `ABCD` (with `B − A = C − D`) bisect each other.
Hint: first show `a + c = b + d`; `sub_eq_sub_iff_add_eq_add` may help. -/
theorem parallelogram_diagonals_bisect (a b c d : V) (h : b - a = c - d) :
    (1 / 2 : ℝ) • (a + c) = (1 / 2 : ℝ) • (b + d) := by
  sorry
-- @endregion

end LumenaryExercises.Vectors
