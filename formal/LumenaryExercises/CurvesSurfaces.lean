/-
The Lumenary — Lean exercises: Differential geometry of curves and surfaces.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CurvesSurfaces.lean`.
-/
import Lumenary.CurvesSurfaces

namespace LumenaryExercises.CurvesSurfaces

open Real Lumenary.CurvesSurfaces

-- @region ex.curves_surfaces.circle_unit_speed
-- @solution Lumenary.CurvesSurfaces.circle_unit_speed
/-- Show that the velocity of the unit-speed circle has length `1`.
Hint: `neg_sq` and `sin_sq_add_cos_sq`. -/
theorem circle_unit_speed (r s : ℝ) : (-sin (s / r)) ^ 2 + (cos (s / r)) ^ 2 = 1 := by
  sorry
-- @endregion

-- @region ex.curves_surfaces.cylinder_gauss_curvature
-- @solution Lumenary.CurvesSurfaces.cylinder_gauss_curvature
/-- Show that the cylinder has Gaussian curvature `0`.
Hint: unfold `gaussCurvature`; the numerator `L N - M²` is `(-r) · 0 - 0²`. -/
theorem cylinder_gauss_curvature (r : ℝ) : gaussCurvature (r ^ 2) 0 1 (-r) 0 0 = 0 := by
  sorry
-- @endregion

end LumenaryExercises.CurvesSurfaces
