/-
The Lumenary — Lean exercises: the coordinate plane.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CoordinatePlane.lean`.
-/
import Lumenary.CoordinatePlane

namespace LumenaryExercises.CoordinatePlane

open Lumenary.CoordinatePlane

-- @region ex.coordinate_plane.reflect_y_twice
-- @solution Lumenary.CoordinatePlane.reflectY_twice
/-- Reflecting twice in the `y`-axis brings every point back.
Hint: `rw [point_eq_iff]` turns the goal into two equations, one per coordinate. The
`x`-coordinate is `-(-a) = a` (`Rat.neg_neg`); the `y`-coordinate does not change (`rfl`). -/
theorem reflectY_twice (P : Point) : reflectY (reflectY P) = P := by
  sorry
-- @endregion

-- @region ex.coordinate_plane.horizontal_distance_example
-- @solution Lumenary.CoordinatePlane.horizontal_distance_example
/-- The distance from `(-3, 2)` to `(4, 2)` is `|-3 - 4| = 7`.
Hint: for particular numbers Lean can compute both sides: try `decide +kernel`. -/
theorem horizontal_distance_example : absQ (-3 - 4) = 7 := by
  sorry
-- @endregion

end LumenaryExercises.CoordinatePlane
