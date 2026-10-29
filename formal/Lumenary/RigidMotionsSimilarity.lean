/-
The Lumenary — formal mathematics
Rigid motions, congruence and similarity in the coordinate plane.

Transformations are functions `Point → Point` on points with rational coordinates. We prove
that translations, quarter turns and reflections keep (squared) distances, that composites and
inverses of distance-keeping maps keep distances, that two reflections make a rotation, that
the order of transformations matters, that rigid motions keep angles (in the form of the dot
product, which records the angle between two sides), and that a dilation with factor `k`
multiplies squared lengths and (signed) areas by `k²` and keeps angles. Lengths are compared
through their squares, so no square roots are needed. Routine algebra is closed by `grind`;
statements about particular points are checked by `decide +kernel`. Core Lean only, no Mathlib.
Mathlib analogue: `Isometry`, `IsometryEquiv` and `AffineIsometryEquiv` for rigid motions,
`Dilation` and `homothety` for dilations.
-/

namespace Lumenary.RigidMotionsSimilarity

/-! ### Points, distance and transformations -/

-- @region rigid_motions_similarity.point
-- @provenance definition
/-- A point of the coordinate plane with rational coordinates. -/
structure Point where
  x : Rat
  y : Rat
deriving DecidableEq
-- @endregion

-- @region rigid_motions_similarity.d2
-- @provenance definition
/-- The **square** of the distance from `P` to `Q` (the distance formula without the square
root): `(x₂ - x₁)² + (y₂ - y₁)²`. -/
def d2 (P Q : Point) : Rat := (Q.x - P.x) * (Q.x - P.x) + (Q.y - P.y) * (Q.y - P.y)
-- @endregion

-- @region rigid_motions_similarity.translate
-- @provenance definition
/-- Translation by `(a, b)`: every point moves `a` to the right and `b` up. -/
def translate (a b : Rat) (P : Point) : Point := ⟨P.x + a, P.y + b⟩
-- @endregion

-- @region rigid_motions_similarity.rot90
-- @provenance definition
/-- Rotation by `90°` anticlockwise about the origin: `(x, y) ↦ (-y, x)`. -/
def rot90 (P : Point) : Point := ⟨-P.y, P.x⟩
-- @endregion

-- @region rigid_motions_similarity.rot180
-- @provenance definition
/-- Rotation by `180°` (a half turn) about the origin: `(x, y) ↦ (-x, -y)`. -/
def rot180 (P : Point) : Point := ⟨-P.x, -P.y⟩
-- @endregion

-- @region rigid_motions_similarity.reflect_x
-- @provenance definition
/-- Reflection in the `x`-axis: `(x, y) ↦ (x, -y)`. -/
def reflectX (P : Point) : Point := ⟨P.x, -P.y⟩
-- @endregion

-- @region rigid_motions_similarity.reflect_diag
-- @provenance definition
/-- Reflection in the line `y = x`: `(x, y) ↦ (y, x)`. -/
def reflectDiag (P : Point) : Point := ⟨P.y, P.x⟩
-- @endregion

-- @region rigid_motions_similarity.dilate
-- @provenance definition
/-- Dilation with centre the origin and scale factor `k`: `(x, y) ↦ (kx, ky)`. -/
def dilate (k : Rat) (P : Point) : Point := ⟨k * P.x, k * P.y⟩
-- @endregion

/-! ### Rigid motions keep distances -/

-- @region rigid_motions_similarity.is_isometry
-- @provenance definition
/-- A transformation is a **rigid motion** (an *isometry*) if it keeps the distance between every
two points. We compare squared distances, which is the same thing for lengths `≥ 0`. -/
def IsIsometry (f : Point → Point) : Prop := ∀ P Q : Point, d2 (f P) (f Q) = d2 P Q
-- @endregion

-- @region rigid_motions_similarity.translate_isometry
-- @provenance independent
/-- A translation is a rigid motion: both coordinates of `Q - P` are unchanged, because the
added `a` (and `b`) cancel. -/
theorem translate_isometry (a b : Rat) : IsIsometry (translate a b) := by
  intro P Q
  unfold d2 translate
  grind
-- @endregion

-- @region rigid_motions_similarity.rot90_isometry
-- @provenance independent
/-- A quarter turn is a rigid motion: the differences `(Δx, Δy)` become `(-Δy, Δx)`, and
`(-Δy)² + (Δx)² = (Δx)² + (Δy)²`. -/
theorem rot90_isometry : IsIsometry rot90 := by
  intro P Q
  unfold d2 rot90
  grind
-- @endregion

-- @region rigid_motions_similarity.reflect_x_isometry
-- @provenance independent
/-- Reflection in the `x`-axis is a rigid motion: `(-Δy)² = (Δy)²`. -/
theorem reflectX_isometry : IsIsometry reflectX := by
  intro P Q
  unfold d2 reflectX
  grind
-- @endregion

-- @region rigid_motions_similarity.reflect_diag_isometry
-- @provenance independent
/-- Reflection in the line `y = x` is a rigid motion: it swaps `Δx` and `Δy`. -/
theorem reflectDiag_isometry : IsIsometry reflectDiag := by
  intro P Q
  unfold d2 reflectDiag
  grind
-- @endregion

-- @region rigid_motions_similarity.isometry_comp
-- @provenance independent
/-- **The composite of two rigid motions is a rigid motion.** If `f` and `g` keep distances, so
does "first `f`, then `g`": `d(g(f P), g(f Q)) = d(f P, f Q) = d(P, Q)`. -/
theorem isometry_comp {f g : Point → Point} (hf : IsIsometry f) (hg : IsIsometry g) :
    IsIsometry (g ∘ f) := by
  intro P Q
  calc d2 ((g ∘ f) P) ((g ∘ f) Q) = d2 (g (f P)) (g (f Q)) := rfl
    _ = d2 (f P) (f Q) := hg (f P) (f Q)
    _ = d2 P Q := hf P Q
-- @endregion

-- @region rigid_motions_similarity.isometry_inverse
-- @provenance independent
/-- **The inverse of a rigid motion is a rigid motion.** If `g` undoes `f` (`f (g P) = P` for
every `P`) and `f` keeps distances, then `g` keeps distances:
`d(g P, g Q) = d(f (g P), f (g Q)) = d(P, Q)`. -/
theorem isometry_inverse {f g : Point → Point} (hf : IsIsometry f)
    (hfg : ∀ P, f (g P) = P) : IsIsometry g := by
  intro P Q
  calc d2 (g P) (g Q) = d2 (f (g P)) (f (g Q)) := (hf (g P) (g Q)).symm
    _ = d2 P Q := by rw [hfg P, hfg Q]
-- @endregion

-- @region rigid_motions_similarity.translate_undo
-- @provenance independent
/-- Translating by `(a, b)` is undone by translating by `(-a, -b)`. -/
theorem translate_undo (a b : Rat) (P : Point) :
    translate (-a) (-b) (translate a b P) = P := by
  cases P
  simp only [translate, Point.mk.injEq]
  constructor <;> grind
-- @endregion

-- @region rigid_motions_similarity.rot90_four
-- @provenance independent
/-- Four quarter turns make a full turn: every point comes back. So the inverse of `rot90` is
`rot90` applied three times (a quarter turn clockwise). -/
theorem rot90_four (P : Point) : rot90 (rot90 (rot90 (rot90 P))) = P := by
  cases P
  simp only [rot90, Point.mk.injEq]
  constructor <;> grind
-- @endregion

-- @region rigid_motions_similarity.rot90_twice
-- @provenance independent
/-- Two quarter turns make a half turn. -/
theorem rot90_twice (P : Point) : rot90 (rot90 P) = rot180 P := rfl
-- @endregion

/-! ### Composing transformations -/

-- @region rigid_motions_similarity.two_reflections_rotation
-- @provenance independent
/-- **Two reflections make a rotation.** Reflecting in the `x`-axis and then in the line `y = x`
(two mirrors meeting at `45°`) is the rotation by `90°`, twice the angle between the mirrors:
`(x, y) ↦ (x, -y) ↦ (-y, x)`. -/
theorem two_reflections_rotation (P : Point) : reflectDiag (reflectX P) = rot90 P := rfl
-- @endregion

-- @region rigid_motions_similarity.reflections_other_order
-- @provenance independent
/-- In the other order the two reflections give the rotation by `90°` **clockwise**, which is
`rot90` done three times: `(x, y) ↦ (y, x) ↦ (y, -x)`. -/
theorem reflections_other_order (P : Point) :
    reflectX (reflectDiag P) = rot90 (rot90 (rot90 P)) := by
  cases P
  simp only [reflectX, reflectDiag, rot90, Point.mk.injEq]
  constructor <;> grind
-- @endregion

-- @region rigid_motions_similarity.order_matters
-- @provenance independent
/-- **Order matters.** Translating `1` to the right and then turning a quarter turn sends the
origin to `(0, 1)`; turning first and then translating sends it to `(1, 0)`. -/
theorem order_matters :
    rot90 (translate 1 0 ⟨0, 0⟩) ≠ translate 1 0 (rot90 ⟨0, 0⟩) := by decide +kernel
-- @endregion

/-! ### Angles: rigid motions keep them -/

-- @region rigid_motions_similarity.dot_at
-- @provenance definition
/-- The dot product of the sides `AB` and `AC` of the angle at `A`:
`(B - A) · (C - A)`. It is `0` exactly for a right angle, positive for an acute angle and
negative for an obtuse one; together with the two side lengths it fixes the angle. -/
def dotAt (A B C : Point) : Rat :=
  (B.x - A.x) * (C.x - A.x) + (B.y - A.y) * (C.y - A.y)
-- @endregion

-- @region rigid_motions_similarity.dot_from_sides
-- @provenance independent
/-- The angle at `A` is determined by the three side lengths of triangle `ABC`:
`2 · (B - A)·(C - A) = AB² + AC² - BC²`. (This is the coordinate form of "a triangle is fixed by
its three sides".) -/
theorem dot_from_sides (A B C : Point) :
    2 * dotAt A B C = d2 A B + d2 A C - d2 B C := by
  unfold dotAt d2
  grind
-- @endregion

-- @region rigid_motions_similarity.isometry_preserves_angles
-- @provenance independent
/-- **Rigid motions keep angles.** A rigid motion keeps the three side lengths of every triangle,
so by `dot_from_sides` it keeps the dot product that records the angle at `A`. -/
theorem isometry_preserves_angles {f : Point → Point} (hf : IsIsometry f) (A B C : Point) :
    dotAt (f A) (f B) (f C) = dotAt A B C := by
  have h1 := dot_from_sides (f A) (f B) (f C)
  have h2 := dot_from_sides A B C
  rw [hf A B, hf A C, hf B C] at h1
  grind
-- @endregion

/-! ### Dilations -/

-- @region rigid_motions_similarity.dilate_d2
-- @provenance independent
/-- **A dilation multiplies lengths by `k`**: squared distances are multiplied by `k²`. -/
theorem dilate_d2 (k : Rat) (P Q : Point) : d2 (dilate k P) (dilate k Q) = k * k * d2 P Q := by
  unfold d2 dilate
  grind
-- @endregion

-- @region rigid_motions_similarity.dilate_not_isometry
-- @provenance independent
/-- A non-example: the dilation with factor `2` is **not** a rigid motion. It moves `(1, 0)` to
`(2, 0)`, doubling its distance from the origin. -/
theorem dilate_not_isometry : ¬ IsIsometry (dilate 2) := by
  intro h
  have := h ⟨0, 0⟩ ⟨1, 0⟩
  revert this
  decide +kernel
-- @endregion

-- @region rigid_motions_similarity.dilate_dot
-- @provenance independent
/-- A dilation multiplies the dot product at every angle by `k²`, the same factor as the
squared lengths of both sides. So the *shape* of every angle (the dot product compared with the
lengths) is unchanged: **dilations keep angles**. -/
theorem dilate_dot (k : Rat) (A B C : Point) :
    dotAt (dilate k A) (dilate k B) (dilate k C) = k * k * dotAt A B C := by
  unfold dotAt dilate
  grind
-- @endregion

-- @region rigid_motions_similarity.signed_area2
-- @provenance definition
/-- Twice the **signed area** of triangle `ABC`: positive when `A → B → C` goes anticlockwise,
negative when clockwise. (Its size is twice the ordinary area.) -/
def signedArea2 (A B C : Point) : Rat :=
  (B.x - A.x) * (C.y - A.y) - (C.x - A.x) * (B.y - A.y)
-- @endregion

-- @region rigid_motions_similarity.dilate_area
-- @provenance independent
/-- **A dilation multiplies areas by `k²`.** Doubling all lengths makes areas four times as
large. -/
theorem dilate_area (k : Rat) (A B C : Point) :
    signedArea2 (dilate k A) (dilate k B) (dilate k C) = k * k * signedArea2 A B C := by
  unfold signedArea2 dilate
  grind
-- @endregion

-- @region rigid_motions_similarity.rot90_area
-- @provenance independent
/-- A quarter turn keeps signed area: it keeps both size and orientation. -/
theorem rot90_area (A B C : Point) :
    signedArea2 (rot90 A) (rot90 B) (rot90 C) = signedArea2 A B C := by
  unfold signedArea2 rot90
  grind
-- @endregion

-- @region rigid_motions_similarity.reflect_x_area
-- @provenance independent
/-- A reflection keeps the size of the area but **reverses orientation**: the signed area
changes sign, so anticlockwise triangles become clockwise ones. This is why no sequence of
slides and turns can produce a mirror image. -/
theorem reflectX_area (A B C : Point) :
    signedArea2 (reflectX A) (reflectX B) (reflectX C) = -signedArea2 A B C := by
  unfold signedArea2 reflectX
  grind
-- @endregion

/-! ### Congruence and similarity -/

-- @region rigid_motions_similarity.congruent
-- @provenance definition
/-- Triangle `ABC` is **congruent** to triangle `A'B'C'` if some rigid motion sends `A, B, C` to
`A', B', C'`. -/
def Congruent (A B C A' B' C' : Point) : Prop :=
  ∃ f : Point → Point, IsIsometry f ∧ f A = A' ∧ f B = B' ∧ f C = C'
-- @endregion

-- @region rigid_motions_similarity.congruent_example
-- @provenance independent
/-- The triangle `(0, 0), (2, 0), (0, 1)` is congruent to `(3, 1), (3, 3), (2, 1)`: turn a quarter
turn about the origin, then translate by `(3, 1)`. -/
theorem congruent_example : Congruent ⟨0, 0⟩ ⟨2, 0⟩ ⟨0, 1⟩ ⟨3, 1⟩ ⟨3, 3⟩ ⟨2, 1⟩ :=
  ⟨translate 3 1 ∘ rot90, isometry_comp rot90_isometry (translate_isometry 3 1),
    by decide +kernel, by decide +kernel, by decide +kernel⟩
-- @endregion

-- @region rigid_motions_similarity.similar
-- @provenance definition
/-- Triangle `ABC` is **similar** to triangle `A'B'C'` if a dilation with some factor `k > 0`
followed by a rigid motion sends `A, B, C` to `A', B', C'`. -/
def Similar (A B C A' B' C' : Point) : Prop :=
  ∃ k : Rat, 0 < k ∧ ∃ f : Point → Point, IsIsometry f ∧
    f (dilate k A) = A' ∧ f (dilate k B) = B' ∧ f (dilate k C) = C'
-- @endregion

-- @region rigid_motions_similarity.similar_example
-- @provenance independent
/-- The triangle `(0, 0), (2, 0), (0, 1)` is similar to `(1, 1), (1, 5), (-1, 1)`: dilate by `2`,
turn a quarter turn, then translate by `(1, 1)`. -/
theorem similar_example : Similar ⟨0, 0⟩ ⟨2, 0⟩ ⟨0, 1⟩ ⟨1, 1⟩ ⟨1, 5⟩ ⟨-1, 1⟩ :=
  ⟨2, by decide +kernel, translate 1 1 ∘ rot90,
    isometry_comp rot90_isometry (translate_isometry 1 1),
    by decide +kernel, by decide +kernel, by decide +kernel⟩
-- @endregion

-- @region rigid_motions_similarity.congruent_preserves_d2
-- @provenance independent
/-- Congruent triangles have equal corresponding sides (here `AB = A'B'`; the other two sides are
the same argument). -/
theorem congruent_preserves_d2 {A B C A' B' C' : Point} (h : Congruent A B C A' B' C') :
    d2 A' B' = d2 A B := by
  obtain ⟨f, hf, hA, hB, _⟩ := h
  rw [← hA, ← hB]
  exact hf A B
-- @endregion

-- @region rigid_motions_similarity.rectangles_not_similar
-- @provenance independent
/-- **Not all rectangles are similar.** A `1 × 2` rectangle and a `1 × 3` rectangle cannot be
matched by one scale factor: `k · 1 = 1` forces `k = 1`, but then `k · 2 = 2 ≠ 3`; and matching
the sides the other way round, `k · 1 = 3` forces `k = 3`, but then `k · 2 = 6 ≠ 1`. -/
theorem rectangles_not_similar :
    ¬ ∃ k : Rat, (k * 1 = 1 ∧ k * 2 = 3) ∨ (k * 1 = 3 ∧ k * 2 = 1) := by
  intro ⟨k, h⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind
-- @endregion

end Lumenary.RigidMotionsSimilarity
