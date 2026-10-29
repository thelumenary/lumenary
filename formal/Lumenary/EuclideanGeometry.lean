/-
The Lumenary — formal mathematics
Euclidean geometry and proof: the parallel postulate, congruence, triangle and circle theorems.

Mathlib does not start from Euclid's or Hilbert's axioms. It models the plane (or space of any
dimension) as a *Euclidean affine space*: points `P`, displacement vectors `V`, and an inner
product on `V` that gives lengths and angles. In this model Euclid's axioms become theorems. We
prove some of them here — Playfair's form of the parallel postulate, the failure of "SSA", the
inscribed angle theorem when one side is a diameter (mirroring the classical proof), Thales'
theorem, and the perpendicular bisector facts behind the circumcentre (`@provenance
independent`). Mathlib provides the angle sum of a triangle, the congruence criteria SAS and SSS,
the isosceles triangle theorem, the general inscribed angle theorem and the existence of the
circumcentre (`@provenance library`).

Notation: `∠ A B C` is the (unoriented) angle at `B`, a real number in `[0, π]` (radians), and
`dist A B` is the length of the segment `AB`.
-/
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Analysis.InnerProductSpace.PiL2

open EuclideanGeometry
open scoped EuclideanGeometry Real RealInnerProductSpace Affine Congruent

namespace Lumenary.EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### The parallel postulate -/

-- @region euclidean_geometry.playfair
-- @provenance independent
/-- **Playfair's axiom holds in the model.** Through a point `p` there is exactly one affine
subspace parallel to a given non-empty one `s` (for a line `s`: exactly one line through `p`
parallel to `s`). Mathlib's `s ∥ t` means that `t` is a translate of `s`, so a line counts as
parallel to itself. Existence: the translate of `s` through `p`, `mk' p s.direction`.
Uniqueness: a parallel `t` has the same direction as `s`, and an affine subspace is determined
by its direction and one of its points (`AffineSubspace.mk'_eq`). In Hilbert's axioms this is
an *axiom*; in the vector model it is a *theorem*. -/
theorem playfair (s : AffineSubspace ℝ P) (hs : s ≠ ⊥) (p : P) :
    ∃! t : AffineSubspace ℝ P, p ∈ t ∧ t ∥ s := by
  have hne : AffineSubspace.mk' p s.direction ≠ ⊥ :=
    (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨p, AffineSubspace.self_mem_mk' p s.direction⟩
  refine ⟨AffineSubspace.mk' p s.direction, ⟨AffineSubspace.self_mem_mk' p s.direction, ?_⟩, ?_⟩
  · rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
    exact ⟨AffineSubspace.direction_mk' p s.direction, ⟨fun h => absurd h hne, fun h => absurd h hs⟩⟩
  · rintro t ⟨hpt, hts⟩
    rw [← hts.direction_eq]
    exact (AffineSubspace.mk'_eq hpt).symm
-- @endregion

-- @region euclidean_geometry.angle_sum
-- @provenance library
/-- **The angles of a triangle add up to `π` (180°).** This applies Mathlib's
`EuclideanGeometry.angle_add_angle_add_angle_eq_pi`. Mathlib proves it with vectors rather than
with Euclid's parallel line, but the parallel postulate is built into the vector model: it is
exactly what makes `playfair` above true. -/
theorem angle_sum (A B C : P) (hAB : B ≠ A) : ∠ A B C + ∠ B C A + ∠ C A B = π :=
  angle_add_angle_add_angle_eq_pi C hAB
-- @endregion

/-! ### Congruence -/

-- @region euclidean_geometry.sas
-- @provenance library
/-- **SAS.** Two sides and the included angle determine a triangle up to congruence. Applies
Mathlib's `EuclideanGeometry.side_angle_side` (proved there with the law of cosines). The
conclusion `![A, B, C] ≅ ![A', B', C']` says that *all* corresponding distances agree. -/
theorem sas {A B C A' B' C' : P} (hB : ∠ A B C = ∠ A' B' C') (hAB : dist A B = dist A' B')
    (hBC : dist B C = dist B' C') : ![A, B, C] ≅ ![A', B', C'] :=
  side_angle_side hB hAB hBC
-- @endregion

-- @region euclidean_geometry.sss
-- @provenance library
/-- **SSS.** Three sides determine a triangle up to congruence. Applies Mathlib's
`EuclideanGeometry.side_side_side`. -/
theorem sss {A B C A' B' C' : P} (hAB : dist A B = dist A' B') (hBC : dist B C = dist B' C')
    (hCA : dist C A = dist C' A') : ![A, B, C] ≅ ![A', B', C'] :=
  side_side_side hAB hBC hCA
-- @endregion

-- @region euclidean_geometry.ssa_fails
-- @provenance independent
/-- **SSA is not a congruence criterion.** The would-be theorem "two sides and a *non-included*
angle determine the triangle" is false. Counterexample in the coordinate plane: `A = (0, 0)`,
`B = (4, 3)`, `C = (3, 0)`, `C' = (5, 0)`. Both triangles `ABC` and `ABC'` have `AB = 5`,
`BC = BC' = √10` and the same angle at `A` (since `C'` lies on the ray `AC`), but `AC = 3` and
`AC' = 5`. -/
theorem ssa_fails : ¬ ∀ A B C A' B' C' : EuclideanSpace ℝ (Fin 2),
    ∠ B A C = ∠ B' A' C' → dist A B = dist A' B' → dist B C = dist B' C' →
      ![A, B, C] ≅ ![A', B', C'] := by
  intro h
  set A : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
  set B : EuclideanSpace ℝ (Fin 2) := !₂[4, 3]
  set C : EuclideanSpace ℝ (Fin 2) := !₂[3, 0]
  set C' : EuclideanSpace ℝ (Fin 2) := !₂[5, 0]
  -- `C' - A` is a positive multiple of `C - A`, so the angles at `A` agree.
  have hray : C' -ᵥ A = (5 / 3 : ℝ) • (C -ᵥ A) := by
    ext i; fin_cases i <;> simp [A, C, C']
  have hangle : ∠ B A C = ∠ B A C' := by
    unfold EuclideanGeometry.angle
    rw [hray, InnerProductGeometry.angle_smul_right_of_pos _ _ (by norm_num)]
  have hBC : dist B C = dist B C' := by
    simp [B, C, C', EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq]
    norm_num
  have hcong := h A B C A B C' hangle rfl hBC
  -- Congruent triangles have equal third sides: `dist A C = dist A C'`.
  have h13 := hcong.dist_eq 0 2
  simp [A, C, C', EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq] at h13
-- @endregion

/-! ### Triangle and circle theorems -/

-- @region euclidean_geometry.isosceles
-- @provenance library
/-- **The isosceles triangle theorem** (*pons asinorum*): if `OA = OB` then the base angles at
`A` and `B` are equal. Applies Mathlib's `EuclideanGeometry.angle_eq_angle_of_dist_eq`. -/
theorem isosceles {O A B : P} (h : dist O A = dist O B) : ∠ O A B = ∠ O B A :=
  angle_eq_angle_of_dist_eq h
-- @endregion

-- @region euclidean_geometry.inscribed_angle_diameter
-- @provenance independent
/-- **The inscribed angle theorem, when one side of the inscribed angle is a diameter.**
`O` is the centre of a circle, `BC` is a diameter (so `O` is the midpoint of `BC`) and `A` is
another point of the circle (`OA = OB`). Then the central angle `∠ A O C` is twice the inscribed
angle `∠ A B C`. This is the classical proof, step by step:
1. `∠ A B C = ∠ A B O`, because `O` lies on the segment `BC`;
2. `∠ O A B = ∠ O B A`, because triangle `OAB` is isosceles (`OA = OB`);
3. `∠ A O B + ∠ O B A + ∠ B A O = π` (angle sum in triangle `AOB`);
4. `∠ A O B + ∠ A O C = π`, because `B, O, C` lie on a line (angles on a straight line);
5. so `∠ A O C = ∠ O B A + ∠ B A O = 2 ∠ A B C`. -/
theorem inscribed_angle_diameter {O A B C : P} (hBC : B ≠ C) (hO : O = midpoint ℝ B C)
    (hA : dist O A = dist O B) (hAO : A ≠ O) : ∠ A O C = 2 * ∠ A B C := by
  have hstraight : ∠ B O C = π := by
    rw [hO]; exact (sbtw_midpoint_of_ne ℝ hBC).angle₁₂₃_eq_pi
  -- Step 1: the inscribed angle at `B` can be measured along `BO` instead of `BC`.
  have h1 : ∠ A B C = ∠ A B O := (angle_eq_angle_of_angle_eq_pi A hstraight).symm
  -- Step 2: base angles of the isosceles triangle `OAB`.
  have h2 : ∠ O A B = ∠ O B A := angle_eq_angle_of_dist_eq hA
  -- Step 3: the angle sum in triangle `AOB`.
  have h3 : ∠ A O B + ∠ O B A + ∠ B A O = π := angle_add_angle_add_angle_eq_pi B hAO.symm
  -- Step 4: angles on the straight line `BOC`.
  have h4 : ∠ A O B + ∠ A O C = π := angle_add_angle_eq_pi_of_angle_eq_pi A hstraight
  -- Step 5: put the pieces together.
  rw [h1, angle_comm A B O]
  rw [angle_comm B A O] at h3
  linarith
-- @endregion

-- @region euclidean_geometry.inscribed_angle
-- @provenance library
/-- **The inscribed angle theorem** in general, in a plane (`finrank ℝ V = 2`). If `A`, `B`, `C`
lie on a circle `s` and the inscribed angle `∠ A B C` is at most a right angle, the central
angle `∠ A O C` (with `O = s.center`) is twice `∠ A B C`. Applies Mathlib's
`EuclideanGeometry.Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi`, which is proved
with *oriented* angles so that all positions of `B` are handled at once. (If `∠ A B C` is
obtuse, the central angle on the other side is `2π − 2∠ A B C`.) -/
theorem inscribed_angle [Fact (Module.finrank ℝ V = 2)] {s : Sphere P} {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    (hacute : 2 * ∠ A B C ≤ π) : ∠ A s.center C = 2 * ∠ A B C :=
  Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi hA hB hC hBA hBC hacute
-- @endregion

-- @region euclidean_geometry.thales
-- @provenance independent
/-- **Thales' theorem**, in vectors. Put the centre of the circle at the origin. A diameter runs
from `a` to `-a`, and `c` is on the circle when `‖c‖ = ‖a‖`. Then the sides `a - c` and `-a - c`
of the triangle are perpendicular: their inner (dot) product is `‖c‖² - ‖a‖² = 0`. So the angle
in a semicircle is a right angle. -/
theorem thales (a c : V) (h : ‖c‖ = ‖a‖) : ⟪a - c, -a - c⟫ = 0 := by
  have key : ⟪a - c, -a - c⟫ = ‖c‖ ^ 2 - ‖a‖ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_neg_right, inner_neg_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm a c]
    ring
  rw [key, h, sub_self]
-- @endregion

/-! ### The circumcentre -/

-- @region euclidean_geometry.equidistant_iff_perp
-- @provenance independent
/-- **The perpendicular bisector is the set of equidistant points.** With `m = (a + b)/2` the
midpoint of `ab`, a point `p` is as far from `a` as from `b` exactly when `p - m` is
perpendicular to `b - a`. The key identity is `‖p - a‖² - ‖p - b‖² = 2 ⟪p - m, b - a⟫`. -/
theorem equidistant_iff_perp (a b p : V) :
    ‖p - a‖ = ‖p - b‖ ↔ ⟪p - (1 / 2 : ℝ) • (a + b), b - a⟫ = 0 := by
  have key : ‖p - a‖ ^ 2 - ‖p - b‖ ^ 2 = 2 * ⟪p - (1 / 2 : ℝ) • (a + b), b - a⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_smul_left, real_inner_comm a b, real_inner_comm a p, real_inner_comm b p]
    simp only [RCLike.conj_to_real]
    ring
  constructor
  · intro h
    have : ‖p - a‖ ^ 2 - ‖p - b‖ ^ 2 = 0 := by rw [h, sub_self]
    linarith
  · intro h
    have h2 : ‖p - a‖ ^ 2 = ‖p - b‖ ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
-- @endregion

-- @region euclidean_geometry.perp_bisectors_concurrent
-- @provenance independent
/-- **The third perpendicular bisector passes through the meeting point of the other two.**
If `O` lies on the perpendicular bisectors of `AB` and of `BC`, then `OA = OB = OC`, so `O` also
lies on the perpendicular bisector of `CA`. Uses Mathlib's description of
`AffineSubspace.perpBisector` as the set of equidistant points. -/
theorem perp_bisectors_concurrent {A B C O : P} (hAB : O ∈ AffineSubspace.perpBisector A B)
    (hBC : O ∈ AffineSubspace.perpBisector B C) : O ∈ AffineSubspace.perpBisector C A := by
  rw [AffineSubspace.mem_perpBisector_iff_dist_eq] at *
  rw [← hBC, hAB]
-- @endregion

-- @region euclidean_geometry.circumcentre_exists
-- @provenance library
/-- **Every triangle has a circumcentre**: if `A`, `B`, `C` are not collinear (affinely
independent), some point `O` is equidistant from all three, so the circle with centre `O`
through `A` passes through `B` and `C`. Applies Mathlib's `Affine.Simplex.circumcenter` and
`Affine.Simplex.dist_circumcenter_eq_circumradius`. -/
theorem circumcentre_exists {A B C : P} (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ O : P, dist O A = dist O B ∧ dist O B = dist O C := by
  let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
  exact ⟨t.circumcenter,
    (t.dist_circumcenter_eq_circumradius' 0).trans (t.dist_circumcenter_eq_circumradius' 1).symm,
    (t.dist_circumcenter_eq_circumradius' 1).trans (t.dist_circumcenter_eq_circumradius' 2).symm⟩
-- @endregion

end Lumenary.EuclideanGeometry
