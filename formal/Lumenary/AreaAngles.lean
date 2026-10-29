/-
The Lumenary — formal mathematics
Area, perimeter and angles ("for grown-ups" companion to the Grades 3–5 lesson).

A shape drawn on squared paper is a list of unit squares, each named by its column and row.
Its area is the number of squares; its perimeter is the number of square sides that face the
outside. We prove that a `w × h` rectangle has area `w × h` and a box has volume
`l × w × h`, for all sizes, by counting column by column and layer by layer; Lean then checks
by computation that equal areas can have different perimeters and the other way round.

Angles are measured in whole degrees. Geometry itself (lines, parallels, measuring) is not
built here: the geometric facts a proof uses — angles on a straight line make 180°, alternate
angles at parallel lines are equal — appear as hypotheses, and Lean checks the reasoning that
turns them into the angle sum of a triangle and its consequences. Core Lean 4 only. Mathlib
analogue: `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` (the triangle angle sum in
a Euclidean space, in radians) and `MeasureTheory.Measure.addHaar_parallelepiped`.
-/

namespace Lumenary.AreaAngles

/-! ### Area: counting unit squares -/

-- @region area_angles.shape
-- @provenance definition
/-- A shape on squared paper: a list of unit squares, each named by `(column, row)`.
We always list each square once. -/
abbrev Shape := List (Int × Int)
-- @endregion

-- @region area_angles.area
-- @provenance definition
/-- The **area** of a shape is the number of unit squares that cover it. -/
def area (s : Shape) : Nat := s.length
-- @endregion

-- @region area_angles.column
-- @provenance definition
/-- One column of squares: the `h` squares `(x, 0), (x, 1), …, (x, h - 1)`. -/
def column (x : Int) (h : Nat) : Shape :=
  (List.range h).map (fun y : Nat => (x, (y : Int)))
-- @endregion

-- @region area_angles.rect
-- @provenance definition
/-- A rectangle `w` squares wide and `h` squares high, built one column at a time. -/
def rect : Nat → Nat → Shape
  | 0, _ => []
  | w + 1, h => column w h ++ rect w h
-- @endregion

-- @region area_angles.area_rect
-- @provenance independent
/-- **The area of a rectangle is width × height.** Each column holds `h` squares, and there
are `w` columns, so there are `h + h + ⋯ + h = w × h` squares. The proof adds one column at a
time (induction on the width). -/
theorem area_rect (w h : Nat) : area (rect w h) = w * h := by
  induction w with
  | zero => simp [rect, area]
  | succ w ih =>
    simp only [area] at ih ⊢
    simp only [rect, List.length_append, column, List.length_map, List.length_range, ih]
    rw [Nat.succ_mul]
    omega
-- @endregion

/-! ### Perimeter: counting the sides that face outside -/

-- @region area_angles.outside
-- @provenance definition
/-- `1` if the square `q` is **not** part of the shape `s`, and `0` if it is. -/
def outside (s : Shape) (q : Int × Int) : Nat :=
  if q ∈ s then 0 else 1
-- @endregion

-- @region area_angles.perimeter
-- @provenance definition
/-- The **perimeter** of a shape, in units: for every square, count those of its four sides
(right, left, top, bottom) whose neighbouring square is outside the shape. -/
def perimeter (s : Shape) : Nat :=
  (s.map fun p =>
    outside s (p.1 + 1, p.2) + outside s (p.1 - 1, p.2) +
    outside s (p.1, p.2 + 1) + outside s (p.1, p.2 - 1)).sum
-- @endregion

-- @region area_angles.same_area_different_perimeter
-- @provenance independent
/-- **Same area, different perimeters.** Rectangles `3 × 4`, `2 × 6` and `1 × 12` all have
area 12, but their perimeters are 14, 16 and 26. Lean counts the squares and the sides. -/
theorem same_area_different_perimeter :
    area (rect 3 4) = 12 ∧ area (rect 2 6) = 12 ∧ area (rect 1 12) = 12 ∧
    perimeter (rect 3 4) = 14 ∧ perimeter (rect 2 6) = 16 ∧ perimeter (rect 1 12) = 26 := by
  decide
-- @endregion

-- @region area_angles.same_perimeter_different_area
-- @provenance independent
/-- **Same perimeter, different areas.** Rectangles `3 × 3`, `2 × 4` and `1 × 5` all have
perimeter 12, but their areas are 9, 8 and 5. -/
theorem same_perimeter_different_area :
    perimeter (rect 3 3) = 12 ∧ perimeter (rect 2 4) = 12 ∧ perimeter (rect 1 5) = 12 ∧
    area (rect 3 3) = 9 ∧ area (rect 2 4) = 8 ∧ area (rect 1 5) = 5 := by
  decide
-- @endregion

-- @region area_angles.perimeter_rect_small
-- @provenance independent
/-- Walking round a rectangle gives `w + h + w + h = 2 × (w + h)`. Here Lean checks that
counting the outside sides square by square agrees with this rule for **every** rectangle up to
`6 × 6` — 36 rectangles, checked one by one. -/
theorem perimeter_rect_small :
    ∀ w < 6, ∀ h < 6, perimeter (rect (w + 1) (h + 1)) = 2 * ((w + 1) + (h + 1)) := by
  decide
-- @endregion

-- @region area_angles.l_shape
-- @provenance definition
/-- An L-shape made of 5 squares: a column of 4 with one extra square at the bottom right. -/
def lShape : Shape := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0)]
-- @endregion

-- @region area_angles.l_shape_measures
-- @provenance independent
/-- The L-shape has area 5 and perimeter 12 — the same perimeter as the `3 × 3` square, whose
area is 9. -/
theorem l_shape_measures : area lShape = 5 ∧ perimeter lShape = 12 := by
  decide
-- @endregion

/-! ### Volume: counting unit cubes -/

-- @region area_angles.layer
-- @provenance definition
/-- One layer of a box: an `l × w` rectangle of unit cubes at height `z`. -/
def layer (l w : Nat) (z : Int) : List (Int × Int × Int) :=
  (rect l w).map (fun p => (p.1, p.2, z))
-- @endregion

-- @region area_angles.box
-- @provenance definition
/-- A box `l` cubes long, `w` cubes wide and `h` cubes high, built one layer at a time. -/
def box (l w : Nat) : Nat → List (Int × Int × Int)
  | 0 => []
  | h + 1 => layer l w h ++ box l w h
-- @endregion

-- @region area_angles.volume_box
-- @provenance independent
/-- **The volume of a box is length × width × height.** Each layer is a rectangle of `l × w`
cubes (by `area_rect`), and there are `h` layers. -/
theorem volume_box (l w h : Nat) : (box l w h).length = l * w * h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have hl : (layer l w h).length = l * w := by
      simp only [layer, List.length_map]
      exact area_rect l w
    simp only [box, List.length_append, hl, ih]
    rw [Nat.mul_succ]
    omega
-- @endregion

/-! ### Angles in degrees -/

-- @region area_angles.vertically_opposite
-- @provenance independent
/-- **Vertically opposite angles are equal.** Where two straight lines cross, angles `a` and `b`
sit side by side on one line, and `b` and `c` on the other; each pair makes a straight angle of
180°. So `a = 180° − b = c`. -/
theorem vertically_opposite (a b c : Nat) (h₁ : a + b = 180) (h₂ : b + c = 180) : a = c := by
  omega
-- @endregion

-- @region area_angles.triangle_angle_sum
-- @provenance independent
/-- **The angles of a triangle add up to 180°.** Draw the line through the top corner parallel to
the base. At the top corner, three angles `d`, `c`, `e` lie along this line, so
`d + c + e = 180`. The angles `d` and `e` are alternate angles to the base angles `a` and `b`,
so `d = a` and `e = b`. The geometry is in the hypotheses; Lean checks the conclusion. -/
theorem triangle_angle_sum (a b c d e : Nat)
    (straight : d + c + e = 180) (alt₁ : d = a) (alt₂ : e = b) : a + b + c = 180 :=
  calc a + b + c = d + e + c := by rw [alt₁, alt₂]
    _ = d + c + e := by omega
    _ = 180 := straight
-- @endregion

-- @region area_angles.no_two_right_angles
-- @provenance independent
/-- A triangle cannot have two right angles: the third angle would have to be 0°. -/
theorem no_two_right_angles (a b c : Nat) (sum : a + b + c = 180) (hc : 0 < c) :
    ¬ (a = 90 ∧ b = 90) := by
  omega
-- @endregion

-- @region area_angles.at_most_one_obtuse
-- @provenance independent
/-- A triangle has at most one obtuse angle (more than 90°): two of them would already add up
to more than 180°. -/
theorem at_most_one_obtuse (a b c : Nat) (sum : a + b + c = 180) : ¬ (90 < a ∧ 90 < b) := by
  omega
-- @endregion

-- @region area_angles.equilateral_angles
-- @provenance independent
/-- In a triangle whose three angles are equal, each angle is 60°. -/
theorem equilateral_angles (a b c : Nat) (sum : a + b + c = 180) (hab : a = b) (hbc : b = c) :
    a = 60 := by
  omega
-- @endregion

-- @region area_angles.quadrilateral_angle_sum
-- @provenance independent
/-- **The angles of a quadrilateral add up to 360°.** A diagonal cuts it into two triangles with
angles `a₁, b₁, c₁` and `a₂, b₂, c₂`. Two corners of the quadrilateral are split by the
diagonal (`q = b₁ + b₂`, `s = c₁ + c₂`); the other two are whole triangle angles. -/
theorem quadrilateral_angle_sum (a₁ b₁ c₁ a₂ b₂ c₂ p q r s : Nat)
    (t₁ : a₁ + b₁ + c₁ = 180) (t₂ : a₂ + b₂ + c₂ = 180)
    (hp : p = a₁) (hq : q = b₁ + b₂) (hr : r = a₂) (hs : s = c₁ + c₂) :
    p + q + r + s = 360 := by
  omega
-- @endregion

-- @region area_angles.triangle_kind
-- @provenance definition
/-- Triangles sorted by their largest angle. -/
inductive TriangleKind where
  | acute
  | right
  | obtuse
  deriving DecidableEq, Repr
-- @endregion

-- @region area_angles.classify
-- @provenance definition
/-- Sort a triangle with angles `a`, `b`, `c` (in degrees): obtuse if some angle is more than
90°, right if some angle is exactly 90°, acute otherwise. -/
def classify (a b c : Nat) : TriangleKind :=
  if 90 < a ∨ 90 < b ∨ 90 < c then .obtuse
  else if a = 90 ∨ b = 90 ∨ c = 90 then .right
  else .acute
-- @endregion

-- @region area_angles.classify_examples
-- @provenance independent
/-- The triangles in the lesson: 60°, 60°, 60° is acute; 90°, 30°, 60° is right;
25°, 35°, 120° is obtuse. -/
theorem classify_examples :
    classify 60 60 60 = .acute ∧ classify 90 30 60 = .right ∧ classify 25 35 120 = .obtuse := by
  decide
-- @endregion

end Lumenary.AreaAngles
