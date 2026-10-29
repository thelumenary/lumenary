/-
The Lumenary — formal mathematics
The Pythagorean theorem: the algebra of the rearrangement proofs, the theorem and its converse
in coordinates, Pythagorean triples, and two common mistakes.

What is formalised. (1) The algebraic step of the two dissection proofs: *if* the big square
is made of the tilted square and four copies of the triangle, *then* `a² + b² = c²`. The
geometric part (that the pieces fit) is argued in the lesson, not here. (2) The theorem and its
converse in the coordinate plane with rational coordinates, where "the angle at `C` is a right
angle" means that the direction from `C` to `B` is the direction from `C` to `A` turned through
a quarter turn, and lengths are compared through their squares (`sqDist`), so no square roots
are needed. (3) Facts about whole numbers: triples, Euclid's formula, and why `√2` is not a
whole number. Routine algebra is closed by `grind`. Core Lean only, no Mathlib. Mathlib analogue:
`EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two` is Pythagoras and its
converse in any real inner product space; `PythagoreanTriple` and
`PythagoreanTriple.classification` describe all integer triples.
-/

namespace Lumenary.PythagoreanTheorem

/-! ### The algebra of the rearrangement proofs -/

-- @region pythagorean_theorem.rearrangement_algebra
-- @provenance independent
/-- **The first rearrangement proof, algebraic step.** If a square of side `a + b` is made up
of a tilted square of side `c` and four right triangles with legs `a`, `b` (area `ab/2` each),
then `a² + b² = c²`.
`(a + b)² = a² + 2ab + b²`, and the four triangles account for `4 · ab/2 = 2ab`. -/
theorem rearrangement_algebra (a b c : Rat) (h : (a + b) ^ 2 = c ^ 2 + 4 * (a * b / 2)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  have expand : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by grind
  have four : 4 * (a * b / 2) = 2 * (a * b) := by grind
  calc a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by rw [expand]; grind
    _ = c ^ 2 + 4 * (a * b / 2) - 2 * (a * b) := by rw [h]
    _ = c ^ 2 := by rw [four]; grind
-- @endregion

-- @region pythagorean_theorem.rearrangement_square_in_middle
-- @provenance independent
/-- **The second dissection proof, algebraic step** (the “hypotenuse diagram”). If a square of
side `c` is made up of four right triangles with legs `a`, `b` and a small square of side
`b - a` in the middle, then `a² + b² = c²`, because `(b - a)² + 2ab = a² + b²`. -/
theorem rearrangement_square_in_middle (a b c : Rat)
    (h : c ^ 2 = (b - a) ^ 2 + 4 * (a * b / 2)) : a ^ 2 + b ^ 2 = c ^ 2 := by
  rw [h]
  grind
-- @endregion

/-! ### The theorem and its converse in coordinates -/

-- @region pythagorean_theorem.point
-- @provenance definition
/-- A point of the coordinate plane with rational coordinates. -/
structure Point where
  x : Rat
  y : Rat
deriving DecidableEq
-- @endregion

-- @region pythagorean_theorem.sq_dist
-- @provenance definition
/-- The **square** of the distance from `P` to `Q`: `(x₂ - x₁)² + (y₂ - y₁)²`. Comparing
squares of lengths lets us avoid square roots entirely. -/
def sqDist (P Q : Point) : Rat := (Q.x - P.x) ^ 2 + (Q.y - P.y) ^ 2
-- @endregion

-- @region pythagorean_theorem.distance_example
-- @provenance independent
/-- The distance from `(1, 2)` to `(4, 6)` is `5`: the legs are `3` and `4`, and
`3² + 4² = 25 = 5²`. -/
theorem distance_example : sqDist ⟨1, 2⟩ ⟨4, 6⟩ = 5 ^ 2 := by decide +kernel
-- @endregion

-- @region pythagorean_theorem.is_right_angle_at
-- @provenance definition
/-- The angle `ACB` is a right angle: the step from `C` to `B` is the step from `C` to `A`
turned through a quarter turn (`(p, q) ↦ (-q, p)`) and scaled by some factor `t`. -/
def IsRightAngleAt (A B C : Point) : Prop :=
  ∃ t : Rat, B.x - C.x = -t * (A.y - C.y) ∧ B.y - C.y = t * (A.x - C.x)
-- @endregion

-- @region pythagorean_theorem.pythagoras_coordinates
-- @provenance independent
/-- **The Pythagorean theorem in coordinates.** If the angle at `C` is a right angle, then
`AB² = CA² + CB²`.
Write `A - C = (p, q)`, so `B - C = (-tq, tp)`. Then `CA² = p² + q²`, `CB² = t²(p² + q²)` and
`AB² = (-tq - p)² + (tp - q)² = (1 + t²)(p² + q²)`: the cross terms `±2tpq` cancel. -/
theorem pythagoras_coordinates (A B C : Point) (h : IsRightAngleAt A B C) :
    sqDist A B = sqDist C A + sqDist C B := by
  obtain ⟨t, h1, h2⟩ := h
  unfold sqDist
  have e1 : B.x - A.x = (B.x - C.x) - (A.x - C.x) := by grind
  have e2 : B.y - A.y = (B.y - C.y) - (A.y - C.y) := by grind
  rw [e1, e2, h1, h2]
  grind
-- @endregion

-- @region pythagorean_theorem.right_triangle_example
-- @provenance independent
/-- A tilted right triangle: `C = (1, 1)`, `A = (4, 2)`, `B = (0, 4)`. The step `C → A` is
`(3, 1)` and the step `C → B` is `(-1, 3)`, its quarter turn. So `AB² = 10 + 10 = 20`. -/
theorem right_triangle_example :
    IsRightAngleAt ⟨4, 2⟩ ⟨0, 4⟩ ⟨1, 1⟩ ∧ sqDist ⟨4, 2⟩ ⟨0, 4⟩ = 20 := by
  refine ⟨⟨1, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩
-- @endregion

-- @region pythagorean_theorem.sq_nonneg
-- @provenance independent
/-- A square is never negative: `0 ≤ p · p` (a positive times a positive, or a negative times a
negative). -/
theorem sq_nonneg (p : Rat) : 0 ≤ p * p := by
  by_cases h : 0 ≤ p
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -p := by grind
    have := Rat.mul_nonneg h' h'
    grind
-- @endregion

-- @region pythagorean_theorem.sum_sq_pos
-- @provenance independent
/-- If `p` and `q` are not both `0`, then `p² + q² > 0`. -/
theorem sum_sq_pos (p q : Rat) (h : p ≠ 0 ∨ q ≠ 0) : 0 < p * p + q * q := by
  have hp := sq_nonneg p
  have hq := sq_nonneg q
  have pos : ∀ r : Rat, r ≠ 0 → 0 < r * r := by
    intro r hr
    by_cases h' : 0 < r
    · exact Rat.mul_pos h' h'
    · have h'' : 0 < -r := by grind
      have := Rat.mul_pos h'' h''
      grind
  rcases h with h | h
  · have := pos p h
    grind
  · have := pos q h
    grind
-- @endregion

-- @region pythagorean_theorem.quarter_turn_of_dot_zero
-- @provenance independent
/-- If `(r, s)` is perpendicular to a non-zero `(p, q)` in the sense `p·r + q·s = 0`, then
`(r, s)` is a multiple of the quarter turn `(-q, p)`. The factor is
`t = (p·s - q·r) / (p² + q²)`. -/
theorem quarter_turn_of_dot_zero (p q r s : Rat) (hpq : p ≠ 0 ∨ q ≠ 0)
    (h : p * r + q * s = 0) : ∃ t : Rat, r = -t * q ∧ s = t * p := by
  have hne : p * p + q * q ≠ 0 := Rat.ne_of_gt (sum_sq_pos p q hpq)
  have ht : (p * s - q * r) / (p * p + q * q) * (p * p + q * q) = p * s - q * r :=
    Rat.div_mul_cancel hne
  generalize (p * s - q * r) / (p * p + q * q) = t at ht
  refine ⟨t, ?_, ?_⟩
  · have hr : r * (p * p + q * q) = (-t * q) * (p * p + q * q) := by grind
    calc r = r * (p * p + q * q) / (p * p + q * q) := (Rat.mul_div_cancel hne).symm
      _ = (-t * q) * (p * p + q * q) / (p * p + q * q) := by rw [hr]
      _ = -t * q := Rat.mul_div_cancel hne
  · have hs : s * (p * p + q * q) = (t * p) * (p * p + q * q) := by grind
    calc s = s * (p * p + q * q) / (p * p + q * q) := (Rat.mul_div_cancel hne).symm
      _ = (t * p) * (p * p + q * q) / (p * p + q * q) := by rw [hs]
      _ = t * p := Rat.mul_div_cancel hne
-- @endregion

-- @region pythagorean_theorem.converse_coordinates
-- @provenance independent
/-- **The converse in coordinates.** If `A ≠ C` and `AB² = CA² + CB²`, then the angle at `C`
is a right angle.
Expanding, `AB² = CA² + CB² - 2(p·r + q·s)` where `(p, q) = A - C` and `(r, s) = B - C`; so the
hypothesis says exactly `p·r + q·s = 0`, and `quarter_turn_of_dot_zero` finishes. -/
theorem converse_coordinates (A B C : Point) (hAC : A ≠ C)
    (h : sqDist A B = sqDist C A + sqDist C B) : IsRightAngleAt A B C := by
  have hpq : A.x - C.x ≠ 0 ∨ A.y - C.y ≠ 0 := by
    by_cases hx : A.x - C.x = 0
    · right
      intro hy
      apply hAC
      cases A
      cases C
      simp only at hx hy
      grind
    · left
      exact hx
  have hdot : (A.x - C.x) * (B.x - C.x) + (A.y - C.y) * (B.y - C.y) = 0 := by
    unfold sqDist at h
    grind
  exact quarter_turn_of_dot_zero _ _ _ _ hpq hdot
-- @endregion

/-! ### Whole-number triples -/

-- @region pythagorean_theorem.triple_examples
-- @provenance independent
/-- Three Pythagorean triples: `3² + 4² = 5²`, `5² + 12² = 13²`, `8² + 15² = 17²`. -/
theorem triple_examples : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 ∧ 5 ^ 2 + 12 ^ 2 = 13 ^ 2 ∧
    8 ^ 2 + 15 ^ 2 = 17 ^ 2 := by decide
-- @endregion

-- @region pythagorean_theorem.not_right_example
-- @provenance independent
/-- A triangle with sides `5, 6, 8` has **no** right angle: `5² + 6² = 61`, but `8² = 64`.
(By the converse, a right angle would force `61 = 64`; and the right angle could only be
opposite the longest side.) -/
theorem not_right_example : 5 ^ 2 + 6 ^ 2 ≠ 8 ^ 2 := by decide
-- @endregion

-- @region pythagorean_theorem.triple_scale
-- @provenance independent
/-- Scaling a triple gives a triple: if `a² + b² = c²` then `(ka)² + (kb)² = (kc)²`. -/
theorem triple_scale (a b c k : Nat) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    (k * a) ^ 2 + (k * b) ^ 2 = (k * c) ^ 2 := by
  calc (k * a) ^ 2 + (k * b) ^ 2 = k ^ 2 * (a ^ 2 + b ^ 2) := by grind
    _ = k ^ 2 * c ^ 2 := by rw [h]
    _ = (k * c) ^ 2 := by grind
-- @endregion

-- @region pythagorean_theorem.euclid_formula
-- @provenance independent
/-- **Euclid's formula.** For all integers `m, n`, the numbers `m² - n²`, `2mn`, `m² + n²`
satisfy `(m² - n²)² + (2mn)² = (m² + n²)²`. With `m = 2, n = 1` this is `3, 4, 5`. -/
theorem euclid_formula (m n : Int) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  grind
-- @endregion

-- @region pythagorean_theorem.infinitely_many_triples
-- @provenance independent
/-- **There are infinitely many Pythagorean triples**: beyond any number `N` there is a triple
with all sides positive and the first side bigger than `N`. Take `3k, 4k, 5k` with
`k = N + 1`. -/
theorem infinitely_many_triples (N : Nat) :
    ∃ a b c : Nat, N < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 := by
  refine ⟨3 * (N + 1), 4 * (N + 1), 5 * (N + 1), by omega, by omega, ?_⟩
  have h := triple_scale 3 4 5 (N + 1) (by decide)
  rw [Nat.mul_comm 3, Nat.mul_comm 4, Nat.mul_comm 5]
  exact h
-- @endregion

/-! ### Two common mistakes -/

-- @region pythagorean_theorem.sum_sq_lt_sq_sum
-- @provenance independent
/-- **`√(a² + b²)` is not `a + b`.** For positive `a, b`, `a² + b² < (a + b)²`: the square of
the sum has the extra `2ab`. So the hypotenuse is always shorter than the two legs together. -/
theorem sum_sq_lt_sq_sum (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 + b ^ 2 < (a + b) ^ 2 := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have expand : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by grind
  omega
-- @endregion

-- @region pythagorean_theorem.no_whole_sqrt_two
-- @provenance independent
/-- The diagonal of a unit square has length `√2`, and `√2` is not a whole number: no whole
number `n` has `n² = 2` (`1² = 1` is too small and `2² = 4` already too big). In fact `√2` is not
even a fraction — see the lesson on real numbers. -/
theorem no_whole_sqrt_two : ¬ ∃ n : Nat, n ^ 2 = 2 := by
  intro ⟨n, h⟩
  match n, h with
  | 0, h => exact absurd h (by decide)
  | 1, h => exact absurd h (by decide)
  | k + 2, h =>
    have : 4 ≤ (k + 2) ^ 2 := by
      have := Nat.mul_le_mul (Nat.le_add_left 2 k) (Nat.le_add_left 2 k)
      rw [Nat.pow_two]
      exact this
    omega
-- @endregion

end Lumenary.PythagoreanTheorem
