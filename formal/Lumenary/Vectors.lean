/-
The Lumenary — formal mathematics
Vectors and coordinate geometry: the dot product, the Cauchy–Schwarz and triangle
inequalities, perpendicularity, projections, lines, and geometry proved with vectors.

We work at two levels. In coordinates, with pairs of real numbers and a home-made dot product
`dot2`, we prove Lagrange's identity and from it the Cauchy–Schwarz inequality, and we show that
the vector equation and the normal equation of a line describe the same set. In a general real
inner product space `V` (Mathlib's setting, covering ℝ², ℝ³ and much more) we prove the triangle
inequality, the vector form of Pythagoras, the orthogonality of projections, and that the
diagonals of a parallelogram bisect each other and the medians of a triangle meet at the
centroid (`@provenance independent`). Mathlib supplies Cauchy–Schwarz in general,
`norm_add_le`, and the formula `cos θ = u · v / (|u| |v|)` (`@provenance library`).
Mathlib writes `⟪u, v⟫` for the dot (inner) product and `‖u‖` for the length.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

namespace Lumenary.Vectors

open Real
open scoped RealInnerProductSpace

/-! ### Coordinates: the dot product in the plane -/

-- @region vectors.dot2
-- @provenance definition
/-- The dot product of two vectors in the plane, given by coordinates:
`(u₁, u₂) · (v₁, v₂) = u₁ v₁ + u₂ v₂`. -/
def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
-- @endregion

-- @region vectors.lagrange_identity
-- @provenance independent
/-- **Lagrange's identity** in the plane:
`(u · u)(v · v) − (u · v)² = (u₁ v₂ − u₂ v₁)²`. Both sides are polynomials in the four
coordinates, and `ring` checks that they are equal. -/
theorem lagrange_identity (u v : ℝ × ℝ) :
    dot2 u u * dot2 v v - dot2 u v ^ 2 = (u.1 * v.2 - u.2 * v.1) ^ 2 := by
  unfold dot2
  ring
-- @endregion

-- @region vectors.cauchy_schwarz_2d
-- @provenance independent
/-- **Cauchy–Schwarz in coordinates**: `(u · v)² ≤ (u · u)(v · v)`, that is,
`|u · v| ≤ |u| |v|`. By Lagrange's identity the difference is a square, and squares are never
negative. -/
theorem cauchy_schwarz_2d (u v : ℝ × ℝ) : dot2 u v ^ 2 ≤ dot2 u u * dot2 v v := by
  have h := lagrange_identity u v
  nlinarith [sq_nonneg (u.1 * v.2 - u.2 * v.1)]
-- @endregion

-- @region vectors.cauchy_schwarz_2d_eq
-- @provenance independent
/-- **Equality in Cauchy–Schwarz** happens exactly when `u₁ v₂ = u₂ v₁`, i.e. when `u` and `v`
are parallel (one is a multiple of the other, or one of them is zero). Again from Lagrange's
identity: the gap is `(u₁ v₂ − u₂ v₁)²`, which is zero exactly when `u₁ v₂ − u₂ v₁ = 0`. -/
theorem cauchy_schwarz_2d_eq (u v : ℝ × ℝ) :
    dot2 u v ^ 2 = dot2 u u * dot2 v v ↔ u.1 * v.2 = u.2 * v.1 := by
  have h := lagrange_identity u v
  constructor
  · intro heq
    have hsq : (u.1 * v.2 - u.2 * v.1) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  · intro hpar
    have hsq : (u.1 * v.2 - u.2 * v.1) ^ 2 = 0 := by rw [hpar, sub_self]; ring
    linarith
-- @endregion

-- @region vectors.line_vector_iff_normal
-- @provenance independent
/-- **Two equations for the same line.** The line through `p` with direction `d ≠ 0` is
`{p + t d : t ∈ ℝ}` (the vector, or parametric, equation). With the normal vector
`n = (−d₂, d₁)`, perpendicular to `d`, the same line is `{x : n · (x − p) = 0}` (the normal, or
Cartesian, equation). For the hard direction, if `n · (x − p) = 0` we take
`t = d · (x − p) / (d · d)` and check `x = p + t d` coordinate by coordinate. -/
theorem line_vector_iff_normal (p d x : ℝ × ℝ) (hd : d ≠ 0) :
    (∃ t : ℝ, x = p + t • d) ↔ dot2 (-d.2, d.1) (x - p) = 0 := by
  unfold dot2
  constructor
  · rintro ⟨t, rfl⟩
    simp only [add_sub_cancel_left, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · intro h
    have hdd : d.1 ^ 2 + d.2 ^ 2 ≠ 0 := by
      intro h0
      apply hd
      have h1 : d.1 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
      have h2 : d.2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
      exact Prod.ext h1 h2
    refine ⟨(d.1 * (x.1 - p.1) + d.2 * (x.2 - p.2)) / (d.1 ^ 2 + d.2 ^ 2), ?_⟩
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linear_combination (-d.2) * h
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linear_combination d.1 * h
-- @endregion

/-! ### Inner product spaces: lengths, angles and inequalities -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- @region vectors.cauchy_schwarz
-- @provenance library
/-- **The Cauchy–Schwarz inequality** in any real inner product space: `|u · v| ≤ |u| |v|`.
Applies Mathlib's `abs_real_inner_le_norm`. -/
theorem cauchy_schwarz (u v : V) : |⟪u, v⟫| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
-- @endregion

-- @region vectors.triangle_inequality
-- @provenance independent
/-- **The triangle inequality** `|u + v| ≤ |u| + |v|`, from Cauchy–Schwarz:
`|u + v|² = |u|² + 2 u · v + |v|² ≤ |u|² + 2 |u| |v| + |v|² = (|u| + |v|)²`, and both
`|u + v|` and `|u| + |v|` are non-negative. -/
theorem triangle_inequality (u v : V) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    rw [norm_add_sq_real]
    nlinarith [real_inner_le_norm u v]
  nlinarith [norm_nonneg (u + v), norm_nonneg u, norm_nonneg v]
-- @endregion

-- @region vectors.norm_add_le_library
-- @provenance library
/-- The triangle inequality as stated in Mathlib, `norm_add_le`, which holds in every normed
space (not only inner product spaces). -/
theorem norm_add_le_library {W : Type*} [NormedAddCommGroup W] (u v : W) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
  norm_add_le u v
-- @endregion

-- @region vectors.pythagoras_iff_perp
-- @provenance independent
/-- **Pythagoras with vectors, and its converse**: `|u + v|² = |u|² + |v|²` exactly when
`u · v = 0`. Expanding gives `|u + v|² = |u|² + 2 u · v + |v|²` (Mathlib's
`norm_add_sq_real`), so the two sides differ by `2 u · v`. -/
theorem pythagoras_iff_perp (u v : V) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 ↔ ⟪u, v⟫ = 0 := by
  rw [norm_add_sq_real]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring
-- @endregion

-- @region vectors.cos_angle
-- @provenance library
/-- **The angle between two vectors**: `cos θ = (u · v) / (|u| |v|)`. In Mathlib this is how
the angle `InnerProductGeometry.angle u v` is *defined* (as an `arccos`), and Cauchy–Schwarz is
what guarantees the quotient lies between `−1` and `1`. Applies
`InnerProductGeometry.cos_angle`. -/
theorem cos_angle (u v : V) :
    cos (InnerProductGeometry.angle u v) = ⟪u, v⟫ / (‖u‖ * ‖v‖) :=
  InnerProductGeometry.cos_angle u v
-- @endregion

-- @region vectors.perp_iff_right_angle
-- @provenance library
/-- **Perpendicular means dot product zero**: `u · v = 0` exactly when the angle between `u`
and `v` is `π/2` (90°). Applies `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`.
(Mathlib's convention makes the angle with the zero vector `π/2`, matching `0 · v = 0`.) -/
theorem perp_iff_right_angle (u v : V) :
    ⟪u, v⟫ = 0 ↔ InnerProductGeometry.angle u v = π / 2 :=
  InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two u v
-- @endregion

-- @region vectors.projection_perp
-- @provenance independent
/-- **Projection.** The projection of `u` onto a non-zero `v` is `((u · v)/(v · v)) v`, and what
is left over, `u − ((u · v)/(v · v)) v`, is perpendicular to `v`:
`(u − c v) · v = u · v − c (v · v) = 0` for `c = (u · v)/(v · v)`. -/
theorem projection_perp (u v : V) (hv : v ≠ 0) :
    ⟪u - (⟪u, v⟫ / ⟪v, v⟫) • v, v⟫ = 0 := by
  have hvv : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.2 hv
  rw [inner_sub_left, real_inner_smul_left, div_mul_cancel₀ _ hvv, sub_self]
-- @endregion

/-! ### Geometry with vectors -/

-- @region vectors.parallelogram_diagonals_bisect
-- @provenance independent
/-- **The diagonals of a parallelogram bisect each other.** If `ABCD` is a parallelogram, so
that `B − A = C − D` (the sides `AB` and `DC` are the same vector), then the midpoint of the
diagonal `AC` equals the midpoint of the diagonal `BD`: `(A + C)/2 = (B + D)/2`. -/
theorem parallelogram_diagonals_bisect (a b c d : V) (h : b - a = c - d) :
    (1 / 2 : ℝ) • (a + c) = (1 / 2 : ℝ) • (b + d) := by
  have hsum : a + c = b + d := by
    rw [sub_eq_sub_iff_add_eq_add] at h
    rw [add_comm a c, ← h, add_comm]
  rw [hsum]
-- @endregion

-- @region vectors.centroid
-- @provenance independent
/-- **The medians of a triangle meet at the centroid.** The point two thirds of the way from
the vertex `A` to the midpoint `(B + C)/2` of the opposite side is `(A + B + C)/3`. This
expression is symmetric in `A`, `B`, `C`, so the same point lies on all three medians. -/
theorem centroid (a b c : V) :
    a + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • (b + c) - a) = (1 / 3 : ℝ) • (a + b + c) := by
  module
-- @endregion

end Lumenary.Vectors
