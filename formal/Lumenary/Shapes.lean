/-
The Lumenary — formal mathematics
Shapes: squares, rectangles and triangles drawn on a dot grid ("for grown-ups" companion to
the K–2 lesson on shapes).

A corner of a shape is a dot on a square grid, with whole-number coordinates. We decide
whether four dots make a square or a rectangle, and three dots a triangle, using only whole
numbers: squared lengths (Pythagoras without square roots) and dot products (zero means a
square corner). Then we prove the lesson's key result for the moves that keep grid dots on
the grid: a quarter turn or a slide never changes what shape a shape is.

What is proved here: the side and corner tests are preserved by every quarter turn and every
slide (`dist2_turn`, `dot_turn`, `isSquare_turn_iff`, …), every square is a rectangle, not
every rectangle is a square, and several concrete shapes are checked by `decide`. What is not:
turns through other angles (a 45° turn moves most grid dots off the grid), and the full
classification of shapes. Core Lean 4 only. Mathlib analogue: Euclidean isometries
(`Isometry`, `EuclideanGeometry`) preserve all distances and angles in any dimension.
-/

namespace Lumenary.Shapes

/-! ### Dots, lengths and corners -/

-- @region shapes.pt
-- @provenance definition
/-- A dot on a square grid: `x` steps to the right and `y` steps up from a chosen start dot. -/
structure Pt where
  x : Int
  y : Int
  deriving DecidableEq, Repr
-- @endregion

-- @region shapes.dist2
-- @provenance definition
/-- The *squared* length of the side from `p` to `q`. By Pythagoras the length itself is the
square root of this, but comparing squared lengths is enough to tell whether two sides are
equal, and it keeps everything in whole numbers. -/
def dist2 (p q : Pt) : Int :=
  (q.x - p.x) * (q.x - p.x) + (q.y - p.y) * (q.y - p.y)
-- @endregion

-- @region shapes.dot
-- @provenance definition
/-- The dot product of the arrows `p → q` and `p → r`. It is `0` exactly when the two arrows
meet at a square corner (a right angle) — provided neither arrow has length zero. -/
def dot (p q r : Pt) : Int :=
  (q.x - p.x) * (r.x - p.x) + (q.y - p.y) * (r.y - p.y)
-- @endregion

-- @region shapes.cross
-- @provenance definition
/-- The cross product of the arrows `p → q` and `p → r`: twice the (signed) area of the
triangle `p q r`. It is `0` exactly when the three dots lie on one straight line. -/
def cross (p q r : Pt) : Int :=
  (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)
-- @endregion

/-! ### Moves that keep grid dots on the grid -/

-- @region shapes.turn
-- @provenance definition
/-- A quarter turn (90°, anticlockwise) about the start dot: `(x, y) ↦ (−y, x)`. -/
def turn (p : Pt) : Pt := ⟨-p.y, p.x⟩
-- @endregion

-- @region shapes.slide
-- @provenance definition
/-- A slide: move every dot `a` steps right and `b` steps up. -/
def slide (a b : Int) (p : Pt) : Pt := ⟨p.x + a, p.y + b⟩
-- @endregion

/-! ### Shapes with three and four corners -/

-- @region shapes.quad
-- @provenance definition
/-- Four dots `A, B, C, D`, joined in that order and back to `A`. -/
structure Quad where
  A : Pt
  B : Pt
  C : Pt
  D : Pt
  deriving Repr
-- @endregion

-- @region shapes.quad_map
-- @provenance definition
/-- Move all four corners of a four-sided shape with the same move `f`. -/
def Quad.map (f : Pt → Pt) (q : Quad) : Quad := ⟨f q.A, f q.B, f q.C, f q.D⟩
-- @endregion

-- @region shapes.is_rectangle
-- @provenance definition
/-- A **rectangle**: four sides of positive length and four square corners. (At corner `A`
the sides go to `B` and to `D`, and so on round the shape.) -/
def IsRectangle (q : Quad) : Prop :=
  0 < dist2 q.A q.B ∧ 0 < dist2 q.B q.C ∧ 0 < dist2 q.C q.D ∧ 0 < dist2 q.D q.A ∧
  dot q.A q.B q.D = 0 ∧ dot q.B q.C q.A = 0 ∧ dot q.C q.D q.B = 0 ∧ dot q.D q.A q.C = 0
-- @endregion

-- @region shapes.is_square
-- @provenance definition
/-- A **square**: a rectangle whose four sides all have the same length — the definition
used in the lesson. -/
def IsSquare (q : Quad) : Prop :=
  IsRectangle q ∧ dist2 q.A q.B = dist2 q.B q.C ∧ dist2 q.B q.C = dist2 q.C q.D ∧
  dist2 q.C q.D = dist2 q.D q.A
-- @endregion

-- @region shapes.is_triangle
-- @provenance definition
/-- Three dots make a **triangle** when they do not all lie on one straight line. Nothing is
said about which side is at the bottom, or about equal sides. -/
def IsTriangle (p q r : Pt) : Prop := cross p q r ≠ 0
-- @endregion

-- @region shapes.decidable_rectangle
-- @provenance definition
/-- The rectangle test is a finite list of whole-number checks, so Lean can decide it. -/
instance instDecidableIsRectangle (q : Quad) : Decidable (IsRectangle q) := by
  unfold IsRectangle; exact inferInstance
-- @endregion

-- @region shapes.decidable_square
-- @provenance definition
/-- The square test can be decided too. -/
instance instDecidableIsSquare (q : Quad) : Decidable (IsSquare q) := by
  unfold IsSquare; exact inferInstance
-- @endregion

-- @region shapes.decidable_triangle
-- @provenance definition
/-- …and so can the triangle test. -/
instance instDecidableIsTriangle (p q r : Pt) : Decidable (IsTriangle p q r) := by
  unfold IsTriangle; exact inferInstance
-- @endregion

/-! ### Every square is a rectangle; not every rectangle is a square -/

-- @region shapes.square_is_rectangle
-- @provenance independent
/-- **Every square is a rectangle.** With the lesson's definition (a square is a rectangle
whose sides are all equal) this is immediate: forget the "all sides equal" part. -/
theorem square_is_rectangle (q : Quad) (h : IsSquare q) : IsRectangle q := h.1
-- @endregion

-- @region shapes.long_rectangle
-- @provenance definition
/-- A rectangle 3 steps long and 1 step tall. -/
def longRectangle : Quad := ⟨⟨0, 0⟩, ⟨3, 0⟩, ⟨3, 1⟩, ⟨0, 1⟩⟩
-- @endregion

-- @region shapes.not_every_rectangle_is_square
-- @provenance independent
/-- **Not every rectangle is a square:** the 3-by-1 rectangle is one example. Lean checks
all the corners and sides by calculation (`decide`). -/
theorem not_every_rectangle_is_square : ∃ q : Quad, IsRectangle q ∧ ¬ IsSquare q :=
  ⟨longRectangle, by decide, by decide⟩
-- @endregion

/-! ### Turned and tilted shapes -/

-- @region shapes.upright_square
-- @provenance definition
/-- A square sitting flat: corners `(0,0), (2,0), (2,2), (0,2)`. -/
def uprightSquare : Quad := ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨0, 2⟩⟩
-- @endregion

-- @region shapes.diamond
-- @provenance definition
/-- The same kind of shape standing on one corner (a "diamond"):
corners `(1,0), (2,1), (1,2), (0,1)`. -/
def diamond : Quad := ⟨⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩⟩
-- @endregion

-- @region shapes.upright_square_is_square
-- @provenance independent
/-- The flat square passes the square test (checked by calculation). -/
theorem upright_square_is_square : IsSquare uprightSquare := by decide
-- @endregion

-- @region shapes.diamond_is_square
-- @provenance independent
/-- **A square standing on its corner is still a square.** The "diamond" has four equal
sides (each of squared length 2) and four square corners. -/
theorem diamond_is_square : IsSquare diamond := by decide
-- @endregion

-- @region shapes.tilted_triangle
-- @provenance independent
/-- A triangle does not need a flat bottom: the dots `(0,0), (3,1), (1,3)` make a triangle
with no side lying flat. -/
theorem tilted_triangle : IsTriangle ⟨0, 0⟩ ⟨3, 1⟩ ⟨1, 3⟩ := by decide
-- @endregion

-- @region shapes.line_not_triangle
-- @provenance independent
/-- Three dots in a straight line do not make a triangle. -/
theorem line_not_triangle : ¬ IsTriangle ⟨0, 0⟩ ⟨1, 1⟩ ⟨2, 2⟩ := by decide
-- @endregion

/-! ### Turning or sliding never changes the shape -/

-- @region shapes.dist2_turn
-- @provenance independent
/-- A quarter turn keeps every length. The side from `p` to `q` goes `(Δx, Δy)`; after the
turn it goes `(−Δy, Δx)`, and `(−Δy)² + Δx² = Δx² + Δy²` because `(−a)·(−a) = a·a`. -/
theorem dist2_turn (p q : Pt) : dist2 (turn p) (turn q) = dist2 p q := by
  simp only [dist2, turn]
  have h : -q.y - -p.y = -(q.y - p.y) := by omega
  rw [h, Int.neg_mul_neg, Int.add_comm]
-- @endregion

-- @region shapes.dot_turn
-- @provenance independent
/-- A quarter turn keeps every corner: the dot product of two arrows is unchanged, for the
same reason as in `dist2_turn`. So square corners stay square. -/
theorem dot_turn (p q r : Pt) : dot (turn p) (turn q) (turn r) = dot p q r := by
  simp only [dot, turn]
  have hq : -q.y - -p.y = -(q.y - p.y) := by omega
  have hr : -r.y - -p.y = -(r.y - p.y) := by omega
  rw [hq, hr, Int.neg_mul_neg, Int.add_comm]
-- @endregion

-- @region shapes.cross_turn
-- @provenance independent
/-- A quarter turn keeps the cross product, so dots in a line stay in a line and a triangle
stays a triangle. -/
theorem cross_turn (p q r : Pt) : cross (turn p) (turn q) (turn r) = cross p q r := by
  simp only [cross, turn]
  have hq : -q.y - -p.y = -(q.y - p.y) := by omega
  have hr : -r.y - -p.y = -(r.y - p.y) := by omega
  rw [hq, hr, Int.neg_mul, Int.mul_neg, Int.sub_neg, Int.add_comm, ← Int.sub_eq_add_neg]
-- @endregion

-- @region shapes.dist2_slide
-- @provenance independent
/-- A slide keeps every length: both ends move by the same amount, so the side still goes
`(Δx, Δy)`. -/
theorem dist2_slide (a b : Int) (p q : Pt) : dist2 (slide a b p) (slide a b q) = dist2 p q := by
  simp only [dist2, slide]
  have hx : q.x + a - (p.x + a) = q.x - p.x := by omega
  have hy : q.y + b - (p.y + b) = q.y - p.y := by omega
  rw [hx, hy]
-- @endregion

-- @region shapes.dot_slide
-- @provenance independent
/-- A slide keeps every corner. -/
theorem dot_slide (a b : Int) (p q r : Pt) :
    dot (slide a b p) (slide a b q) (slide a b r) = dot p q r := by
  simp only [dot, slide]
  have hqx : q.x + a - (p.x + a) = q.x - p.x := by omega
  have hqy : q.y + b - (p.y + b) = q.y - p.y := by omega
  have hrx : r.x + a - (p.x + a) = r.x - p.x := by omega
  have hry : r.y + b - (p.y + b) = r.y - p.y := by omega
  rw [hqx, hqy, hrx, hry]
-- @endregion

-- @region shapes.is_square_turn_iff
-- @provenance independent
/-- **Turning a shape does not change what shape it is** (for quarter turns): a four-sided
shape is a square after a quarter turn exactly when it was a square before. The proof only
uses that lengths and corners are unchanged (`dist2_turn`, `dot_turn`). -/
theorem isSquare_turn_iff (q : Quad) : IsSquare (q.map turn) ↔ IsSquare q := by
  simp only [IsSquare, IsRectangle, Quad.map, dist2_turn, dot_turn]
-- @endregion

-- @region shapes.is_rectangle_turn_iff
-- @provenance independent
/-- The same for rectangles: a quarter turn makes a rectangle into a rectangle, and nothing
else into one. -/
theorem isRectangle_turn_iff (q : Quad) : IsRectangle (q.map turn) ↔ IsRectangle q := by
  simp only [IsRectangle, Quad.map, dist2_turn, dot_turn]
-- @endregion

-- @region shapes.is_square_slide_iff
-- @provenance independent
/-- **Moving a shape does not change what shape it is** (for slides). -/
theorem isSquare_slide_iff (a b : Int) (q : Quad) :
    IsSquare (q.map (slide a b)) ↔ IsSquare q := by
  simp only [IsSquare, IsRectangle, Quad.map, dist2_slide, dot_slide]
-- @endregion

-- @region shapes.is_triangle_turn_iff
-- @provenance independent
/-- A quarter turn makes a triangle into a triangle, and three dots in a line into three dots
in a line. -/
theorem isTriangle_turn_iff (p q r : Pt) :
    IsTriangle (turn p) (turn q) (turn r) ↔ IsTriangle p q r := by
  simp only [IsTriangle, cross_turn]
-- @endregion

end Lumenary.Shapes
