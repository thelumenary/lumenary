/-
The Lumenary — formal mathematics
Symmetry: slides, turns and flips ("for grown-ups" companion to the Grades 3–5 lesson).

Points of squared paper are pairs of whole numbers `(x, y)`, which may be negative. Slides,
turns and flips are functions that move every point. We prove, for every point:

* each move can be undone (a flip undoes itself; four quarter turns make a full turn);
* doing two moves one after the other gives another move — two flips in crossing mirror lines
  make a turn, and two flips in parallel mirror lines make a slide;
* the order of two moves can matter;
* moves do not change distances (we use the square of the distance, so no square roots appear).

Lean also counts which of the eight grid moves that keep the centre fixed are symmetries of a
square (all 8) and of a rectangle (only 4: its diagonals are not mirror lines).
Core Lean 4 only. Mathlib analogue: `AffineIsometryEquiv` for the moves of the plane, and
`DihedralGroup 4` for the 8 symmetries of a square.
-/

namespace Lumenary.SymmetryTransformations

/-! ### Points and moves -/

-- @region symmetry_transformations.point
-- @provenance definition
/-- A point of squared paper: a column `x` and a row `y`, which may be negative. -/
abbrev Point := Int × Int
-- @endregion

-- @region symmetry_transformations.slide
-- @provenance definition
/-- **Slide** every point `a` squares to the right and `b` squares up. -/
def slide (a b : Int) (p : Point) : Point := (p.1 + a, p.2 + b)
-- @endregion

-- @region symmetry_transformations.flip_v
-- @provenance definition
/-- **Flip** in the vertical mirror line through `(0, 0)`: left and right swap over. -/
def flipV (p : Point) : Point := (-p.1, p.2)
-- @endregion

-- @region symmetry_transformations.flip_h
-- @provenance definition
/-- **Flip** in the horizontal mirror line through `(0, 0)`: up and down swap over. -/
def flipH (p : Point) : Point := (p.1, -p.2)
-- @endregion

-- @region symmetry_transformations.flip_d
-- @provenance definition
/-- **Flip** in the diagonal mirror line `y = x`, which runs up and to the right at 45°. -/
def flipD (p : Point) : Point := (p.2, p.1)
-- @endregion

-- @region symmetry_transformations.flip_a
-- @provenance definition
/-- **Flip** in the other diagonal mirror line, `y = -x`. -/
def flipA (p : Point) : Point := (-p.2, -p.1)
-- @endregion

-- @region symmetry_transformations.flip_at
-- @provenance definition
/-- **Flip** in the vertical mirror line `x = c`: a point `d` squares to one side of the line
goes to `d` squares on the other side. -/
def flipAt (c : Int) (p : Point) : Point := (2 * c - p.1, p.2)
-- @endregion

-- @region symmetry_transformations.quarter_turn
-- @provenance definition
/-- **Turn** a quarter turn (90°) anticlockwise about `(0, 0)`. -/
def quarterTurn (p : Point) : Point := (-p.2, p.1)
-- @endregion

-- @region symmetry_transformations.half_turn
-- @provenance definition
/-- **Turn** a half turn (180°) about `(0, 0)`. -/
def halfTurn (p : Point) : Point := (-p.1, -p.2)
-- @endregion

/-! ### Undoing moves -/

-- @region symmetry_transformations.flip_twice
-- @provenance independent
/-- **Flipping twice in the same line puts every point back where it started.** -/
theorem flip_twice (p : Point) : flipV (flipV p) = p := by
  obtain ⟨x, y⟩ := p
  simp [flipV]
-- @endregion

-- @region symmetry_transformations.flip_at_twice
-- @provenance independent
/-- The same for any vertical mirror line `x = c`. -/
theorem flipAt_twice (c : Int) (p : Point) : flipAt c (flipAt c p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [flipAt, Prod.mk.injEq, and_true]
  omega
-- @endregion

-- @region symmetry_transformations.slide_undo
-- @provenance independent
/-- A slide is undone by the opposite slide. -/
theorem slide_undo (a b : Int) (p : Point) : slide (-a) (-b) (slide a b p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [slide, Prod.mk.injEq]
  omega
-- @endregion

-- @region symmetry_transformations.four_quarter_turns
-- @provenance independent
/-- Four quarter turns make a full turn: every point is back where it started. So a quarter
turn is undone by three more quarter turns. -/
theorem four_quarter_turns (p : Point) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn p))) = p := by
  obtain ⟨x, y⟩ := p
  simp [quarterTurn]
-- @endregion

/-! ### One move after another -/

-- @region symmetry_transformations.slide_slide
-- @provenance independent
/-- A slide followed by a slide is a single slide: the distances add up. -/
theorem slide_slide (a b c d : Int) (p : Point) :
    slide c d (slide a b p) = slide (a + c) (b + d) p := by
  obtain ⟨x, y⟩ := p
  simp only [slide, Prod.mk.injEq]
  omega
-- @endregion

-- @region symmetry_transformations.two_quarter_turns
-- @provenance independent
/-- Two quarter turns make a half turn. -/
theorem two_quarter_turns (p : Point) : quarterTurn (quarterTurn p) = halfTurn p := by
  obtain ⟨x, y⟩ := p
  rfl
-- @endregion

-- @region symmetry_transformations.flips_at_right_angles
-- @provenance independent
/-- **Two flips in mirror lines crossing at a right angle make a half turn** about the crossing
point. (The turn is twice the angle between the mirrors: 2 × 90° = 180°.) -/
theorem flips_at_right_angles (p : Point) : flipH (flipV p) = halfTurn p := by
  obtain ⟨x, y⟩ := p
  rfl
-- @endregion

-- @region symmetry_transformations.flips_at_45
-- @provenance independent
/-- **Two flips in mirror lines crossing at 45° make a quarter turn** (2 × 45° = 90°): first
flip in the diagonal `y = x`, then in the vertical line. -/
theorem flips_at_45 (p : Point) : flipV (flipD p) = quarterTurn p := by
  obtain ⟨x, y⟩ := p
  rfl
-- @endregion

-- @region symmetry_transformations.flips_in_parallel_lines
-- @provenance independent
/-- **Two flips in parallel mirror lines make a slide.** Flipping in the line `x = c` and then
in the line `x = d` slides every point by twice the gap from the first line to the second. -/
theorem flips_in_parallel_lines (c d : Int) (p : Point) :
    flipAt d (flipAt c p) = slide (2 * (d - c)) 0 p := by
  obtain ⟨x, y⟩ := p
  simp only [flipAt, slide, Prod.mk.injEq]
  omega
-- @endregion

-- @region symmetry_transformations.order_matters
-- @provenance independent
/-- **The order of moves can matter.** A quarter turn and then a flip in the vertical line is a
flip in the diagonal `y = x`; the flip first and then the quarter turn is a flip in the other
diagonal. They send the point `(1, 0)` to different places. -/
theorem order_matters :
    flipV (quarterTurn (1, 0)) ≠ quarterTurn (flipV (1, 0)) := by
  decide
-- @endregion

-- @region symmetry_transformations.flip_is_not_half_turn
-- @provenance independent
/-- **A flip is not a half turn.** The flip in the vertical line sends `(1, 2)` to `(-1, 2)`,
but the half turn sends it to `(-1, -2)`. -/
theorem flip_is_not_half_turn : flipV (1, 2) ≠ halfTurn (1, 2) := by
  decide
-- @endregion

/-! ### Moves keep distances -/

-- @region symmetry_transformations.dist2
-- @provenance definition
/-- The **square** of the distance between two points (by Pythagoras). Working with the square
avoids square roots: two distances are equal exactly when their squares are. -/
def dist2 (p q : Point) : Int :=
  (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)
-- @endregion

-- @region symmetry_transformations.slide_keeps_distance
-- @provenance independent
/-- A slide does not change the distance between any two points. -/
theorem slide_keeps_distance (a b : Int) (p q : Point) :
    dist2 (slide a b p) (slide a b q) = dist2 p q := by
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  simp only [slide, dist2]
  have hx : x₁ + a - (x₂ + a) = x₁ - x₂ := by omega
  have hy : y₁ + b - (y₂ + b) = y₁ - y₂ := by omega
  rw [hx, hy]
-- @endregion

-- @region symmetry_transformations.flip_keeps_distance
-- @provenance independent
/-- A flip does not change the distance between any two points. -/
theorem flip_keeps_distance (p q : Point) : dist2 (flipV p) (flipV q) = dist2 p q := by
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  simp only [flipV, dist2]
  have hx : -x₁ - -x₂ = -(x₁ - x₂) := by omega
  rw [hx, Int.neg_mul_neg]
-- @endregion

-- @region symmetry_transformations.turn_keeps_distance
-- @provenance independent
/-- A quarter turn does not change the distance between any two points: the two parts of the
distance swap places, and one of them changes sign. -/
theorem turn_keeps_distance (p q : Point) :
    dist2 (quarterTurn p) (quarterTurn q) = dist2 p q := by
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  simp only [quarterTurn, dist2]
  have hy : -y₁ - -y₂ = -(y₁ - y₂) := by omega
  rw [hy, Int.neg_mul_neg, Int.add_comm]
-- @endregion

/-! ### Symmetries of a square and of a rectangle -/

-- @region symmetry_transformations.is_symmetry
-- @provenance definition
/-- A move is a **symmetry** of a shape (given by its corners) if it sends the corners onto the
corners — the same corners, possibly in a different order (`List.isPerm`). -/
def isSymmetry (m : Point → Point) (corners : List Point) : Bool :=
  (corners.map m).isPerm corners
-- @endregion

-- @region symmetry_transformations.turns
-- @provenance definition
/-- The four turns about `(0, 0)` that move squared paper onto itself: by 0°, 90°, 180°, 270°. -/
def turns : List (Point → Point) :=
  [id, quarterTurn, halfTurn, fun p => quarterTurn (halfTurn p)]
-- @endregion

-- @region symmetry_transformations.flips
-- @provenance definition
/-- The four flips in mirror lines through `(0, 0)` that move squared paper onto itself:
vertical, horizontal and the two diagonals. -/
def flips : List (Point → Point) := [flipV, flipH, flipD, flipA]
-- @endregion

-- @region symmetry_transformations.square
-- @provenance definition
/-- A square with its centre at `(0, 0)`. -/
def square : List Point := [(1, 1), (-1, 1), (-1, -1), (1, -1)]
-- @endregion

-- @region symmetry_transformations.rectangle
-- @provenance definition
/-- A rectangle, 4 squares wide and 2 squares high, with its centre at `(0, 0)`. -/
def rectangle : List Point := [(2, 1), (-2, 1), (-2, -1), (2, -1)]
-- @endregion

-- @region symmetry_transformations.square_symmetries
-- @provenance independent
/-- All 4 turns and all 4 flips are symmetries of the square: it has rotational symmetry of
order 4 and 4 lines of symmetry. -/
theorem square_symmetries :
    (turns.filter (isSymmetry · square)).length = 4 ∧
    (flips.filter (isSymmetry · square)).length = 4 := by
  decide
-- @endregion

-- @region symmetry_transformations.rectangle_symmetries
-- @provenance independent
/-- Only 2 of the turns (0° and 180°) and only 2 of the flips (vertical and horizontal) are
symmetries of the rectangle: rotational symmetry of order 2, and 2 lines of symmetry. -/
theorem rectangle_symmetries :
    (turns.filter (isSymmetry · rectangle)).length = 2 ∧
    (flips.filter (isSymmetry · rectangle)).length = 2 := by
  decide
-- @endregion

-- @region symmetry_transformations.rectangle_diagonal_not_mirror
-- @provenance independent
/-- **The diagonal of a rectangle is not a line of symmetry** (unless the rectangle is a
square): flipping in the diagonal sends the corner `(2, 1)` to `(1, 2)`, which is not a corner. -/
theorem rectangle_diagonal_not_mirror :
    isSymmetry flipD rectangle = false ∧ isSymmetry flipD square = true := by
  decide
-- @endregion

end Lumenary.SymmetryTransformations
