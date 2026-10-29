/-
The Lumenary — formal mathematics
Projective geometry: homogeneous coordinates, the line through two points and the point on two
lines (cross products), invariance of the cross-ratio, the theorems of Desargues and Pappus in
coordinates, and the projective equivalence of conics.

Mathlib's `Projectivization K V` (notation `ℙ K V`) is the set of lines through `0` in `V`, with
`Projectivization.mk K v hv` the point with homogeneous coordinates `v ≠ 0`; the cross product
`u ⨯₃ v` and the triple product `u ⬝ᵥ (v ⨯₃ w) = det [u, v, w]` live in
`Mathlib.LinearAlgebra.CrossProduct`. In `ℙ²` a line `ℓ` is also a vector of `K³` (up to scale),
and `p` lies on `ℓ` exactly when `ℓ ⬝ᵥ p = 0`. Proved here (`@provenance independent`): opposite
vectors give the same point, a line through two distinct points is a multiple of their cross
product (and, by the same theorem read dually, two distinct lines meet in the cross product),
the cross-ratio is invariant under Möbius transformations, Desargues' theorem and Pappus'
theorem as polynomial identities in homogeneous coordinates (so over every field; Pappus uses
commutativity), and an explicit projective transformation taking the circle to a parabola.
Applied from Mathlib (`@provenance library`): equality of points in `ℙ K V`, the cross-product
incidence lemmas, the triple product as a determinant, and Sylvester's classification of real
quadratic forms. Not formalised: the synthetic axioms of a projective plane, the fundamental
theorem of projective geometry (four points in general position), Desargues over division rings
and the converse of Pappus.
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace Lumenary.ProjectiveGeometry

open Matrix

/-! ### Homogeneous coordinates -/

-- @region projective_geometry.mk_eq_mk_iff
-- @provenance library
/-- **Homogeneous coordinates are defined up to scale**: `[v] = [w]` in `ℙ K V` exactly when
`v = a • w` for some scalar `a` (Mathlib's `Projectivization.mk_eq_mk_iff'`). -/
theorem mk_eq_mk_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (v w : V)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔ ∃ a : K, a • w = v :=
  Projectivization.mk_eq_mk_iff' K v w hv hw
-- @endregion

-- @region projective_geometry.mk_neg
-- @provenance independent
/-- **Opposite directions give the same point.** `[v] = [−v]`: in particular a direction in the
plane and its reverse determine the *same* point at infinity `[x : y : 0] = [−x : −y : 0]`. -/
theorem mk_neg {K : Type*} [Field K] (v : Fin 3 → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K (-v) (neg_ne_zero.mpr hv) := by
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨-1, by simp⟩
-- @endregion

/-! ### Lines through points, points on lines -/

-- @region projective_geometry.cross_on_both
-- @provenance library
/-- **The line through `p` and `q` is `p × q`**: the cross product is orthogonal to both factors,
so both points lie on it (Mathlib's `dot_self_cross` and `dot_cross_self`). Read dually, with
`p`, `q` lines: the point `p × q` lies on both lines. -/
theorem cross_on_both {K : Type*} [CommRing K] (p q : Fin 3 → K) :
    p ⬝ᵥ (p ⨯₃ q) = 0 ∧ q ⬝ᵥ (p ⨯₃ q) = 0 :=
  ⟨dot_self_cross p q, dot_cross_self p q⟩
-- @endregion

-- @region projective_geometry.cross_ne_zero_iff
-- @provenance library
/-- `p × q ≠ 0` exactly when `p` and `q` are linearly independent, i.e. represent **distinct**
points (Mathlib's `crossProduct_ne_zero_iff_linearIndependent`). -/
theorem cross_ne_zero_iff {K : Type*} [Field K] (p q : Fin 3 → K) :
    p ⨯₃ q ≠ 0 ↔ LinearIndependent K ![p, q] :=
  crossProduct_ne_zero_iff_linearIndependent
-- @endregion

-- @region projective_geometry.incident_cross_zero
-- @provenance independent
/-- If the line `ℓ` passes through `p` and `q`, then `ℓ × (p × q) = 0`, i.e. `ℓ` and `p × q` are
parallel vectors. Proof: the expansion `ℓ × (p × q) = (ℓ · q) p − (p · ℓ) q` (Mathlib's
`cross_cross_eq_smul_sub_smul'`) has both coefficients zero. -/
theorem incident_cross_zero {K : Type*} [CommRing K] (ℓ p q : Fin 3 → K) (hp : ℓ ⬝ᵥ p = 0)
    (hq : ℓ ⬝ᵥ q = 0) : ℓ ⨯₃ (p ⨯₃ q) = 0 := by
  rw [cross_cross_eq_smul_sub_smul', hq, dotProduct_comm, hp, zero_smul, zero_smul, sub_zero]
-- @endregion

-- @region projective_geometry.line_unique
-- @provenance independent
/-- **Two distinct points lie on exactly one line.** If `p × q ≠ 0` (distinct points) and `ℓ`
passes through both, then `ℓ` is a scalar multiple of `p × q` — the same projective line. By
duality (swap the roles of points and lines) the *same theorem* says that two distinct lines
meet in exactly one point, their cross product. -/
theorem line_unique {K : Type*} [Field K] (ℓ p q : Fin 3 → K) (hpq : p ⨯₃ q ≠ 0)
    (hp : ℓ ⬝ᵥ p = 0) (hq : ℓ ⬝ᵥ q = 0) : ∃ c : K, c • (p ⨯₃ q) = ℓ := by
  have h1 : (p ⨯₃ q) ⨯₃ ℓ = 0 := by
    rw [← cross_anticomm, incident_cross_zero ℓ p q hp hq, neg_zero]
  have h2 : ¬ LinearIndependent K ![p ⨯₃ q, ℓ] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not]
    exact h1
  rw [LinearIndependent.pair_iff' hpq] at h2
  push Not at h2
  exact h2
-- @endregion

-- @region projective_geometry.triple_product_det
-- @provenance library
/-- **Collinearity test**: three points `u, v, w` of `ℙ²` are collinear (lie on a common line)
exactly when `det [u, v, w] = 0`; the triple product `u · (v × w)` is that determinant
(Mathlib's `triple_product_eq_det`). -/
theorem triple_product_det {K : Type*} [CommRing K] (u v w : Fin 3 → K) :
    u ⬝ᵥ (v ⨯₃ w) = Matrix.det ![u, v, w] :=
  triple_product_eq_det u v w
-- @endregion

/-! ### The cross-ratio -/

-- @region projective_geometry.cross_ratio
-- @provenance definition
/-- The **cross-ratio** of four numbers (affine coordinates of four points on a line):
`(a, b; c, d) = ((a − c)(b − d)) / ((a − d)(b − c))`. (Lean's division by `0` gives `0`.) -/
def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=
  ((a - c) * (b - d)) / ((a - d) * (b - c))
-- @endregion

-- @region projective_geometry.mobius_sub
-- @provenance independent
/-- The key identity behind cross-ratio invariance: for `f(x) = (a x + b)/(c x + d)`,
`f(x) − f(y) = (ad − bc)(x − y) / ((c x + d)(c y + d))`. -/
theorem mobius_sub {K : Type*} [Field K] (a b c d x y : K) (hx : c * x + d ≠ 0)
    (hy : c * y + d ≠ 0) :
    (a * x + b) / (c * x + d) - (a * y + b) / (c * y + d)
      = (a * d - b * c) * (x - y) / ((c * x + d) * (c * y + d)) := by
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring
-- @endregion

-- @region projective_geometry.cross_ratio_mobius
-- @provenance independent
/-- **The cross-ratio is a projective invariant.** A projective transformation of the line,
`f(x) = (a x + b)/(c x + d)` with `ad − bc ≠ 0`, preserves the cross-ratio of any four points
where it is defined. In each of the four differences the factor `ad − bc` and the denominators
`c x + d` cancel between numerator and denominator — exactly the lesson's proof. -/
theorem cross_ratio_mobius {K : Type*} [Field K] (a b c d p q r s : K) (hdet : a * d - b * c ≠ 0)
    (hp : c * p + d ≠ 0) (hq : c * q + d ≠ 0) (hr : c * r + d ≠ 0) (hs : c * s + d ≠ 0) :
    let f := fun x => (a * x + b) / (c * x + d)
    crossRatio (f p) (f q) (f r) (f s) = crossRatio p q r s := by
  intro f
  simp only [crossRatio, f]
  rw [mobius_sub a b c d p r hp hr, mobius_sub a b c d q s hq hs, mobius_sub a b c d p s hp hs,
    mobius_sub a b c d q r hq hr]
  set D := a * d - b * c
  have hP : (c * p + d) * (c * r + d) * ((c * q + d) * (c * s + d)) ≠ 0 := by
    apply mul_ne_zero <;> apply mul_ne_zero <;> assumption
  rw [div_mul_div_comm, div_mul_div_comm]
  rw [show (c * p + d) * (c * s + d) * ((c * q + d) * (c * r + d))
      = (c * p + d) * (c * r + d) * ((c * q + d) * (c * s + d)) by ring]
  rw [div_div_div_cancel_right₀ hP]
  rw [show D * (p - r) * (D * (q - s)) = (D * D) * ((p - r) * (q - s)) by ring,
    show D * (p - s) * (D * (q - r)) = (D * D) * ((p - s) * (q - r)) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero hdet hdet)
-- @endregion

/-! ### Desargues and Pappus -/

-- @region projective_geometry.desargues
-- @provenance independent
/-- **Desargues' theorem** in homogeneous coordinates. Triangles `ABC` and `A'B'C'` are in
perspective from `O`: `A' = O + a A`, `B' = O + b B`, `C' = O + c C` (every point of the line `OA`
other than `A` has a representative of this form). Then `P = aA − bB` lies on the lines `AB` and
`A'B'` (because `P = A' − B'`), similarly `Q` on `BC` and `B'C'` and `R` on `CA` and `C'A'`, and
`P + Q + R = 0` makes `P, Q, R` collinear: the triple product `P · (Q × R)` vanishes. -/
theorem desargues {K : Type*} [CommRing K] (O A B C : Fin 3 → K) (a b c : K) :
    let A' := O + a • A
    let B' := O + b • B
    let C' := O + c • C
    let P := a • A - b • B
    let Q := b • B - c • C
    let R := c • C - a • A
    (A ⬝ᵥ (B ⨯₃ P) = 0 ∧ A' ⬝ᵥ (B' ⨯₃ P) = 0) ∧
    (B ⬝ᵥ (C ⨯₃ Q) = 0 ∧ B' ⬝ᵥ (C' ⨯₃ Q) = 0) ∧
    (C ⬝ᵥ (A ⨯₃ R) = 0 ∧ C' ⬝ᵥ (A' ⨯₃ R) = 0) ∧
    P ⬝ᵥ (Q ⨯₃ R) = 0 := by
  intro A' B' C' P Q R
  simp only [A', B', C', P, Q, R, cross_apply, dotProduct, Fin.sum_univ_three]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp <;> ring
-- @endregion

-- @region projective_geometry.pappus
-- @provenance independent
/-- **Pappus' theorem** in homogeneous coordinates. After a projective change of coordinates the
two lines are `y = 0` and `x = 0`, so `A, B, C = [a₁ : 0 : a₂], …` and `A', B', C' = [0 : d₁ : d₂], …`.
The three cross-joins `AB' ∩ A'B`, `AC' ∩ A'C`, `BC' ∩ B'C` — each a cross product of two
cross products — are collinear: their triple product is identically zero. The proof is a
polynomial identity checked by `ring`, valid in every *commutative* ring: commutativity of
multiplication is exactly what Pappus needs. -/
theorem pappus {K : Type*} [CommRing K] (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : K) :
    let A : Fin 3 → K := ![a₁, 0, a₂]
    let B : Fin 3 → K := ![b₁, 0, b₂]
    let C : Fin 3 → K := ![c₁, 0, c₂]
    let A' : Fin 3 → K := ![0, d₁, d₂]
    let B' : Fin 3 → K := ![0, e₁, e₂]
    let C' : Fin 3 → K := ![0, f₁, f₂]
    let P := (A ⨯₃ B') ⨯₃ (A' ⨯₃ B)
    let Q := (A ⨯₃ C') ⨯₃ (A' ⨯₃ C)
    let R := (B ⨯₃ C') ⨯₃ (B' ⨯₃ C)
    P ⬝ᵥ (Q ⨯₃ R) = 0 := by
  intro A B C A' B' C' P Q R
  simp only [A, B, C, A', B', C', P, Q, R, cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring
-- @endregion

/-! ### Conics -/

-- @region projective_geometry.circle_to_parabola
-- @provenance independent
/-- **The circle and the parabola are projectively the same conic.** With
`P = [[1/2, 0, −1/2], [0, 1, 0], [1/2, 0, 1/2]]` (invertible: `det P = 1/2`), the form
`x² + y² − z²` (the circle `x² + y² = 1` when `z = 1`) becomes `y² − u w`, i.e. `Pᵀ C P = D` —
the parabola `y² = u` in the chart `w = 1`. Concretely, `x = (u − w)/2`, `z = (u + w)/2`. -/
theorem circle_to_parabola :
    let P : Matrix (Fin 3) (Fin 3) ℚ := !![1/2, 0, -1/2; 0, 1, 0; 1/2, 0, 1/2]
    let C : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]
    let D : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, -1/2; 0, 1, 0; -1/2, 0, 0]
    Pᵀ * C * P = D ∧ P.det ≠ 0 := by
  intro P C D
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, C, D, Matrix.mul_apply, Fin.sum_univ_three]
  · norm_num [P, Matrix.det_fin_three]
-- @endregion

-- @region projective_geometry.real_quadratic_forms
-- @provenance library
/-- **Sylvester's classification of real quadratic forms**: a non-degenerate quadratic form on a
real `n`-dimensional space is equivalent to `Σ wᵢ xᵢ²` with every `wᵢ = ±1` (Mathlib's
`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`). For `n = 3`, up to an overall sign
only `x² + y² + z²` (an empty conic) and `x² + y² − z²` (the circle) remain: so all non-empty
non-degenerate real conics are projectively equivalent. -/
theorem real_quadratic_forms {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧ QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) :=
  Q.equivalent_one_neg_one_weighted_sum_squared hQ
-- @endregion

end Lumenary.ProjectiveGeometry
