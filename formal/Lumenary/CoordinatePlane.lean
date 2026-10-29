/-
The Lumenary — formal mathematics
The coordinate plane: points as ordered pairs, quadrants, reflections in the axes, and
distances along grid lines.

A point is a structure with two rational coordinates, so `⟨3, 2⟩` and `⟨2, 3⟩` are different
points. We prove that two points are equal exactly when both coordinates agree, that
reflecting twice in the same axis returns every point, how reflections move points between
quadrants, and that reflections keep distances along grid lines. Concrete facts about
particular points are checked by `decide +kernel` (Lean computes both sides); general facts
are proved here, with routine algebra closed by `grind`. Core Lean only, no Mathlib.
Mathlib analogue: the plane is `ℝ × ℝ` (or `EuclideanSpace ℝ (Fin 2)`), `|x|` is `abs`, and
the grid ("taxicab") distance is the distance given by the `ℓ¹` norm.
-/

namespace Lumenary.CoordinatePlane

/-! ### Points are ordered pairs -/

-- @region coordinate_plane.point
-- @provenance definition
/-- A point of the coordinate plane: its `x`-coordinate (horizontal position) and its
`y`-coordinate (vertical position), measured from the origin `⟨0, 0⟩`. -/
structure Point where
  x : Rat
  y : Rat
deriving DecidableEq
-- @endregion

-- @region coordinate_plane.point_eq_iff
-- @provenance independent
/-- **One point, one ordered pair.** Two points are the same exactly when their
`x`-coordinates agree **and** their `y`-coordinates agree. -/
theorem point_eq_iff (P Q : Point) : P = Q ↔ P.x = Q.x ∧ P.y = Q.y := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · intro ⟨hx, hy⟩
    cases P
    cases Q
    simp only at hx hy
    rw [hx, hy]
-- @endregion

-- @region coordinate_plane.order_matters
-- @provenance independent
/-- The order of the coordinates matters: `(3, 2)` and `(2, 3)` are different points. -/
theorem order_matters : (⟨3, 2⟩ : Point) ≠ ⟨2, 3⟩ := by decide +kernel
-- @endregion

/-! ### Quadrants -/

-- @region coordinate_plane.quadrant
-- @provenance definition
/-- The quadrant of a point: 1 (`x > 0, y > 0`), 2 (`x < 0, y > 0`), 3 (`x < 0, y < 0`),
4 (`x > 0, y < 0`), and `0` for points on an axis, which lie in no quadrant. -/
def quadrant (P : Point) : Nat :=
  if 0 < P.x ∧ 0 < P.y then 1
  else if P.x < 0 ∧ 0 < P.y then 2
  else if P.x < 0 ∧ P.y < 0 then 3
  else if 0 < P.x ∧ P.y < 0 then 4
  else 0
-- @endregion

-- @region coordinate_plane.example_quadrant
-- @provenance independent
/-- The point `(-1/2, 3)` lies in the second quadrant, and `(0, -2)` on an axis. -/
theorem example_quadrant : quadrant ⟨-1/2, 3⟩ = 2 ∧ quadrant ⟨0, -2⟩ = 0 := by decide +kernel
-- @endregion

/-! ### Reflections in the axes -/

-- @region coordinate_plane.reflect_x
-- @provenance definition
/-- Reflection in the `x`-axis: `(a, b) ↦ (a, -b)`. -/
def reflectX (P : Point) : Point := ⟨P.x, -P.y⟩
-- @endregion

-- @region coordinate_plane.reflect_y
-- @provenance definition
/-- Reflection in the `y`-axis: `(a, b) ↦ (-a, b)`. -/
def reflectY (P : Point) : Point := ⟨-P.x, P.y⟩
-- @endregion

-- @region coordinate_plane.example_reflections
-- @provenance independent
/-- Reflecting `(3, 2)` in the `x`-axis gives `(3, -2)`; in the `y`-axis, `(-3, 2)`. -/
theorem example_reflections : reflectX ⟨3, 2⟩ = ⟨3, -2⟩ ∧ reflectY ⟨3, 2⟩ = ⟨-3, 2⟩ := by
  decide +kernel
-- @endregion

-- @region coordinate_plane.reflect_x_twice
-- @provenance independent
/-- Reflecting twice in the same axis brings every point back: `-(-b) = b`. -/
theorem reflectX_twice (P : Point) : reflectX (reflectX P) = P := by
  rw [point_eq_iff]
  exact ⟨rfl, Rat.neg_neg P.y⟩
-- @endregion

-- @region coordinate_plane.reflect_y_twice
-- @provenance independent
/-- Reflecting twice in the `y`-axis brings every point back. -/
theorem reflectY_twice (P : Point) : reflectY (reflectY P) = P := by
  rw [point_eq_iff]
  exact ⟨Rat.neg_neg P.x, rfl⟩
-- @endregion

-- @region coordinate_plane.reflect_x_reflect_y
-- @provenance independent
/-- Reflecting in the `y`-axis and then in the `x`-axis sends `(a, b)` to `(-a, -b)`: a half
turn about the origin. -/
theorem reflectX_reflectY (P : Point) : reflectX (reflectY P) = ⟨-P.x, -P.y⟩ := rfl
-- @endregion

-- @region coordinate_plane.reflections_commute
-- @provenance independent
/-- The two reflections can be done in either order: both orders give `(-a, -b)`. -/
theorem reflections_commute (P : Point) : reflectX (reflectY P) = reflectY (reflectX P) := rfl
-- @endregion

-- @region coordinate_plane.reflect_x_fixed_iff
-- @provenance independent
/-- The points that reflection in the `x`-axis leaves where they are are exactly the points
**on** the `x`-axis: `(a, -b) = (a, b)` exactly when `b = 0`. -/
theorem reflectX_fixed_iff (P : Point) : reflectX P = P ↔ P.y = 0 := by
  rw [point_eq_iff]
  constructor
  · intro ⟨_, h⟩
    -- `h` says `-b = b`, which forces `b = 0`.
    simp only [reflectX] at h
    grind
  · intro h
    exact ⟨rfl, by simp only [reflectX]; rw [h]; rfl⟩
-- @endregion

-- @region coordinate_plane.mirror_quadrant
-- @provenance definition
/-- How reflection in the `x`-axis relabels quadrants: `1 ↔ 4` and `2 ↔ 3` (and the axes,
labelled `0`, stay on the axes). -/
def mirrorQuadrant : Nat → Nat
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0
-- @endregion

-- @region coordinate_plane.quadrant_reflect_x
-- @provenance independent
/-- **Reflection in the `x`-axis swaps quadrants 1 and 4, and 2 and 3.** The sign of `x` is
kept and the sign of `y` is reversed. Proof: try every combination of signs. -/
theorem quadrant_reflectX (P : Point) : quadrant (reflectX P) = mirrorQuadrant (quadrant P) := by
  unfold quadrant reflectX
  simp only
  by_cases h1 : 0 < P.x <;> by_cases h2 : 0 < P.y <;> by_cases h3 : P.x < 0 <;>
    by_cases h4 : P.y < 0 <;> simp_all [mirrorQuadrant] <;> grind
-- @endregion

/-! ### Distances along grid lines -/

-- @region coordinate_plane.abs_q
-- @provenance definition
/-- Absolute value: the distance of a number from `0` on the number line. -/
def absQ (q : Rat) : Rat := if 0 ≤ q then q else -q
-- @endregion

-- @region coordinate_plane.abs_sub_comm
-- @provenance independent
/-- The distance between `a` and `c` on a number line does not depend on the order:
`|a - c| = |c - a|`. -/
theorem abs_sub_comm (a c : Rat) : absQ (a - c) = absQ (c - a) := by
  unfold absQ
  split <;> split <;> grind
-- @endregion

-- @region coordinate_plane.horizontal_distance_example
-- @provenance independent
/-- From `(-3, 2)` to `(4, 2)` is `|-3 - 4| = 7` units — **not** `4 - 3 = 1`: the path
crosses the `y`-axis, 3 units on one side and 4 on the other. -/
theorem horizontal_distance_example : absQ (-3 - 4) = 7 := by decide +kernel
-- @endregion

-- @region coordinate_plane.grid_dist
-- @provenance definition
/-- The distance between two points when you may only travel along grid lines (horizontal
and vertical steps, like a taxi in a city of square blocks): `|a - c| + |b - d|`. -/
def gridDist (P Q : Point) : Rat := absQ (P.x - Q.x) + absQ (P.y - Q.y)
-- @endregion

-- @region coordinate_plane.grid_dist_horizontal
-- @provenance independent
/-- For two points on the same horizontal line, `(a, b)` and `(c, b)`, the distance is
`|a - c|`. -/
theorem gridDist_horizontal (P Q : Point) (h : P.y = Q.y) :
    gridDist P Q = absQ (P.x - Q.x) := by
  unfold gridDist
  rw [h, Rat.sub_self]
  unfold absQ
  grind
-- @endregion

-- @region coordinate_plane.grid_dist_reflect_x
-- @provenance independent
/-- **Reflections keep distances.** Reflecting two points in the `x`-axis does not change the
grid distance between them, because `|(-b) - (-d)| = |d - b| = |b - d|`. -/
theorem gridDist_reflectX (P Q : Point) : gridDist (reflectX P) (reflectX Q) = gridDist P Q := by
  unfold gridDist reflectX
  simp only
  rw [show -P.y - -Q.y = Q.y - P.y by grind, abs_sub_comm Q.y P.y]
-- @endregion

-- @region coordinate_plane.abs_add_le
-- @provenance independent
/-- The triangle inequality on the number line: `|a + b| ≤ |a| + |b|`. Proof: check every
combination of signs of `a`, `b` and `a + b`. -/
theorem abs_add_le (a b : Rat) : absQ (a + b) ≤ absQ a + absQ b := by
  unfold absQ
  split <;> split <;> split <;> grind
-- @endregion

-- @region coordinate_plane.grid_dist_triangle
-- @provenance independent
/-- **A detour never helps:** going from `P` to `R` along grid lines is never longer than going
from `P` to `Q` and then from `Q` to `R`. Apply `abs_add_le` to the horizontal and the vertical
parts separately. -/
theorem gridDist_triangle (P Q R : Point) : gridDist P R ≤ gridDist P Q + gridDist Q R := by
  unfold gridDist
  have h1 := abs_add_le (P.x - Q.x) (Q.x - R.x)
  have h2 := abs_add_le (P.y - Q.y) (Q.y - R.y)
  rw [show P.x - Q.x + (Q.x - R.x) = P.x - R.x by grind] at h1
  rw [show P.y - Q.y + (Q.y - R.y) = P.y - R.y by grind] at h2
  grind
-- @endregion

-- @region coordinate_plane.grid_lines_vs_steps
-- @provenance library
/-- **Count the gaps, not the lines.** Walking `n` unit steps from `a` passes the `n + 1` grid
lines `a, a + 1, …, a + n`: one more line than the distance. This applies core Lean's
`List.length_range'`. -/
theorem grid_lines_vs_steps (a n : Nat) : (List.range' a (n + 1)).length = n + 1 :=
  List.length_range'
-- @endregion

end Lumenary.CoordinatePlane
