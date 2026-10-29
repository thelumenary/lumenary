/-
The Lumenary — Lean exercises: Transformation geometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/TransformationGeometry.lean`.
-/
import Lumenary.TransformationGeometry

namespace LumenaryExercises.TransformationGeometry

open Complex ComplexConjugate

-- @region ex.transformation_geometry.glide_no_fixed_point
-- @solution Lumenary.TransformationGeometry.glide_no_fixed_point
/-- A glide reflection `z ↦ z̄ + t` with real `t ≠ 0` has no fixed point.
Hint: take real parts of both sides with `congrArg Complex.re`, then `simp`. -/
theorem glide_no_fixed_point {t : ℝ} (ht : t ≠ 0) (z : ℂ) : conj z + t ≠ z := by
  sorry
-- @endregion

-- @region ex.transformation_geometry.parallel_reflections
-- @solution Lumenary.TransformationGeometry.parallel_reflections
/-- Reflecting in the vertical line `Re z = b` and then in `Re z = a` is the translation by
`2(a - b)`. Hint: push `conj` through with `map_sub`, `map_mul`, `Complex.conj_ofReal`,
`Complex.conj_conj` and `map_ofNat`, then `ring`. -/
theorem parallel_reflections (a b : ℝ) (z : ℂ) :
    2 * (a : ℂ) - conj (2 * (b : ℂ) - conj z) = z + 2 * ((a : ℂ) - b) := by
  sorry
-- @endregion

end LumenaryExercises.TransformationGeometry
