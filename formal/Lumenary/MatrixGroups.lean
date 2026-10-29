/-
The Lumenary — formal mathematics
Matrix groups and continuous symmetry: orthogonal matrices, SO(2) and SO(3), Euler's rotation
theorem, the matrix exponential and one-parameter subgroups, the tangent space of O(n) at the
identity, and unit quaternions acting on ℝ³.

Mathlib defines `Matrix.orthogonalGroup n R` (matrices with `A * Aᵀ = 1`),
`Matrix.specialOrthogonalGroup`, `Matrix.unitaryGroup` and `Matrix.specialUnitaryGroup` as
submonoids of `Matrix n n R` with a group structure, the exponential `NormedSpace.exp` with
`Matrix.exp_add_of_commute`, `Matrix.exp_neg` and `Matrix.exp_transpose`, and the quaternions
`ℍ[ℝ]` with the multiplicative norm `Quaternion.normSq`. Proved here from more basic facts
(`@provenance independent`), mirroring the lesson: orthogonal matrices preserve dot products and
have determinant ±1, SO(2) is commutative but SO(3) is not, Euler's rotation theorem
(`det (A − I) = 0`, so every rotation of ℝ³ fixes an axis), `exp` of a skew-symmetric matrix is
orthogonal, `t ↦ exp (t X)` is a homomorphism, tangent vectors to O(n) at `I` are skew-symmetric,
points of the 3-sphere give matrices in SU(2), and conjugation by a unit quaternion preserves the
pure quaternions and their length, with `q` and `−q` acting identically. Not formalised: `det (exp X) = e^{tr X}` (listed as a to-do in
Mathlib), compactness and connectedness of the classical groups, surjectivity of `SU(2) → SO(3)`,
and the homeomorphism `SU(2) ≅ S³`.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Basic

namespace Lumenary.MatrixGroups

open Matrix

/-! ### Orthogonal matrices -/

-- @region matrix_groups.orthogonal_preserves_dot
-- @provenance independent
/-- **Orthogonal matrices preserve the dot product**, hence lengths and angles: if `AᵀA = I`
then `(A v) · (A w) = v · (Aᵀ A w) = v · w`. -/
theorem orthogonal_preserves_dot {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : Aᵀ * A = 1) (v w : n → ℝ) : (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA, one_mulVec]
-- @endregion

-- @region matrix_groups.mem_orthogonal_group_iff
-- @provenance library
/-- Mathlib's `Matrix.orthogonalGroup n ℝ` is exactly the set of real matrices with `AᵀA = I`
(`Matrix.mem_orthogonalGroup_iff'`). It is a group under multiplication, with inverse `Aᵀ`. -/
theorem mem_orthogonal_group_iff {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    A ∈ Matrix.orthogonalGroup n ℝ ↔ Aᵀ * A = 1 :=
  Matrix.mem_orthogonalGroup_iff' n ℝ
-- @endregion

-- @region matrix_groups.det_orthogonal
-- @provenance independent
/-- **An orthogonal matrix has determinant `1` or `−1`**: `det A ² = det Aᵀ · det A =
det (AᵀA) = det I = 1`. The two values label the two connected components of `O(n)`. -/
theorem det_orthogonal {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : Aᵀ * A = 1) : A.det = 1 ∨ A.det = -1 := by
  have h : (Aᵀ * A).det = 1 := by rw [hA, det_one]
  rw [det_mul, det_transpose] at h
  exact mul_self_eq_one_iff.mp h
-- @endregion

-- @region matrix_groups.rotation_mem_so2
-- @provenance independent
/-- The rotation matrix `R(θ)` lies in `SO(2)`, using Mathlib's description of `SO(2)` as the
matrices `!![a, b; c, d]` with `a = d`, `b = −c`, `a² + b² = 1` and the identity
`cos² θ + sin² θ = 1`. -/
theorem rotation_mem_so2 (θ : ℝ) :
    !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨rfl, rfl, ?_⟩
  rw [neg_sq]
  exact Real.cos_sq_add_sin_sq θ
-- @endregion

-- @region matrix_groups.so2_comm
-- @provenance independent
/-- **`SO(2)` is commutative.** Every element has the form `!![a, −c; c, a]`, and two such
matrices commute — rotations of the plane can be done in either order. -/
theorem so2_comm (A B : Matrix (Fin 2) (Fin 2) ℝ) (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (hB : B ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) : A * B = B * A := by
  rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff] at hA hB
  obtain ⟨ha1, ha2, -⟩ := hA
  obtain ⟨hb1, hb2, -⟩ := hB
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Fin.zero_eta, Fin.mk_one, ha1, ha2, hb1, hb2] <;> ring
-- @endregion

-- @region matrix_groups.so3_not_comm
-- @provenance independent
/-- **`SO(3)` is not commutative.** The quarter turns about the `x`-axis and the `z`-axis
(both orthogonal with determinant `1`) give different results in the two orders: turn a book
a quarter turn forwards and then a quarter turn clockwise, then try the other order. -/
theorem so3_not_comm :
    let Rx : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, -1; 0, 1, 0]
    let Rz : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]
    (Rxᵀ * Rx = 1 ∧ Rx.det = 1) ∧ (Rzᵀ * Rz = 1 ∧ Rz.det = 1) ∧ Rx * Rz ≠ Rz * Rx := by
  intro Rx Rz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Rx, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Rx, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Rz, Matrix.det_fin_three]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [Rx, Rz, Matrix.mul_apply, Fin.sum_univ_three] at h01
-- @endregion

-- @region matrix_groups.euler_rotation_det
-- @provenance independent
/-- **Euler's rotation theorem, algebraic core**: for `A ∈ SO(3)`, `det (A − I) = 0`. The proof
is the lesson's: `det (A − I) = det (A (I − Aᵀ)) = det (I − A)ᵀ = det (I − A) = (−1)³ det (A − I)`,
so `det (A − I)` equals its own negative. The odd dimension `3` is essential. -/
theorem euler_rotation_det {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (hdet : A.det = 1) :
    (A - 1).det = 0 := by
  have hA' : A * Aᵀ = 1 := mul_eq_one_comm.mp hA
  have key : (A - 1).det = -(A - 1).det :=
    calc (A - 1).det = (A * (1 - Aᵀ)).det := by rw [mul_sub, mul_one, hA']
      _ = (1 - Aᵀ).det := by rw [det_mul, hdet, one_mul]
      _ = ((1 - A)ᵀ).det := by rw [transpose_sub, transpose_one]
      _ = (1 - A).det := det_transpose _
      _ = (-(A - 1)).det := by rw [neg_sub]
      _ = -(A - 1).det := by rw [det_neg]; norm_num
  linarith
-- @endregion

-- @region matrix_groups.euler_rotation_axis
-- @provenance independent
/-- **Every rotation of ℝ³ has an axis**: a non-zero vector `v` with `A v = v`. From
`det (A − I) = 0` and Mathlib's `Matrix.exists_mulVec_eq_zero_iff` (a square matrix has a
non-zero kernel vector exactly when its determinant vanishes). -/
theorem euler_rotation_axis {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (hdet : A.det = 1) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = v := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (euler_rotation_det hA hdet)
  refine ⟨v, hv0, ?_⟩
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv
  exact hv
-- @endregion

/-! ### The matrix exponential -/

-- @region matrix_groups.exp_skew_orthogonal
-- @provenance independent
/-- **`exp` maps skew-symmetric matrices into `O(n)`.** If `Xᵀ = −X` then
`(exp X)ᵀ (exp X) = exp (Xᵀ) exp X = exp (−X) exp X = (exp X)⁻¹ exp X = I`. Uses Mathlib's
`Matrix.exp_transpose`, `Matrix.exp_neg` and the invertibility of `exp X`. -/
theorem exp_skew_orthogonal {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℝ}
    (hX : Xᵀ = -X) : (NormedSpace.exp X)ᵀ * NormedSpace.exp X = 1 := by
  rw [← Matrix.exp_transpose, hX, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))
-- @endregion

-- @region matrix_groups.one_parameter_subgroup
-- @provenance independent
/-- **`t ↦ exp (t X)` is a one-parameter subgroup**: `exp ((s + t) X) = exp (s X) exp (t X)`.
The matrices `s X` and `t X` commute, so Mathlib's `Matrix.exp_add_of_commute` applies. (For
non-commuting `X`, `Y` the identity `exp (X + Y) = exp X exp Y` fails.) -/
theorem one_parameter_subgroup {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ)
    (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left s |>.smul_right t)
-- @endregion

-- @region matrix_groups.exp_tangent
-- @provenance library
open scoped Matrix.Norms.Operator in
/-- **The tangent vector of `t ↦ exp (t X)` at `t = 0` is `X`.** This is Mathlib's
`hasDerivAt_exp_smul_const`. Derivatives need a norm on matrices; we use Mathlib's operator norm
(`Matrix.Norms.Operator`), but all norms on a finite-dimensional space give the same derivative. -/
theorem exp_tangent {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
-- @endregion

-- @region matrix_groups.tangent_skew
-- @provenance independent
open scoped Matrix.Norms.Operator in
/-- **Tangent vectors to `O(n)` at the identity are skew-symmetric.** If `γ` is a curve of
orthogonal matrices with `γ 0 = I` and velocity `X` at `0`, differentiate `γ(t)ᵀ γ(t) = I` with
the product rule: `Xᵀ · I + I · X = 0`. Together with `exp_skew_orthogonal` this identifies the
Lie algebra of `O(n)` (and of `SO(n)`) with the skew-symmetric matrices. -/
theorem tangent_skew {n : Type*} [Fintype n] [DecidableEq n] (γ : ℝ → Matrix n n ℝ)
    (X : Matrix n n ℝ) (hγ : HasDerivAt γ X 0) (h0 : γ 0 = 1) (horth : ∀ t, (γ t)ᵀ * γ t = 1) :
    Xᵀ + X = 0 := by
  have hT : HasDerivAt (fun t => (γ t)ᵀ) Xᵀ 0 := by
    have hL := (Matrix.transposeLinearEquiv n n ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt (x := γ 0)
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hL hγ
  have hprod := hT.mul hγ
  have hconst : HasDerivAt (fun t => (γ t)ᵀ * γ t) 0 0 := by
    have : (fun t => (γ t)ᵀ * γ t) = fun _ => (1 : Matrix n n ℝ) := funext horth
    rw [this]
    exact hasDerivAt_const _ _
  have := hprod.unique hconst
  simpa [h0] using this
-- @endregion

/-! ### Quaternions and rotations of ℝ³ -/

-- @region matrix_groups.su2_mem
-- @provenance independent
/-- **Points of the 3-sphere give elements of `SU(2)`.** If `|a|² + |b|² = 1` then
`!![a, −b̄; b, ā]` is unitary with determinant `1`. (Conversely every element of `SU(2)` has this
form, which identifies `SU(2)` with the unit sphere `S³ ⊂ ℂ² = ℝ⁴` and with the unit
quaternions `a + b j`; that converse is not formalised here.) -/
theorem su2_mem (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) :
    !![a, -(starRingEnd ℂ) b; b, (starRingEnd ℂ) a] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have h' : a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, h, Complex.ofReal_one]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      first | ring1 | linear_combination h'
  · simp [Matrix.det_fin_two]
    linear_combination h'
-- @endregion

-- @region matrix_groups.quat_norm_mul
-- @provenance library
/-- **The quaternion norm is multiplicative**: `|p q|² = |p|² |q|²` (Euler's four-square
identity in disguise). So the unit quaternions form a group — the 3-sphere `S³` with a
group law. Mathlib: `Quaternion.normSq` is a monoid-with-zero homomorphism, so `map_mul`. -/
theorem quat_norm_mul (p q : Quaternion ℝ) :
    Quaternion.normSq (p * q) = Quaternion.normSq p * Quaternion.normSq q :=
  map_mul Quaternion.normSq p q
-- @endregion

-- @region matrix_groups.quat_conj_pure
-- @provenance independent
/-- **Conjugation preserves pure quaternions.** Identify `ℝ³` with the quaternions of real part
`0`. If `v` is pure, so is `q v q̄` (where `q̄ = star q`); in fact its real part is
`|q|² · Re v`, a polynomial identity checked by `simp` and `ring`. -/
theorem quat_conj_pure (q v : Quaternion ℝ) (hv : v.re = 0) : (q * v * star q).re = 0 := by
  simp [hv]
  ring
-- @endregion

-- @region matrix_groups.quat_conj_norm
-- @provenance independent
/-- **Conjugation by a unit quaternion preserves length**: `|q v q̄|² = |q|² |v|² |q̄|² = |v|²`.
So `v ↦ q v q̄` is an orthogonal map of `ℝ³` — the rotation `ρ(q)` of the lesson. -/
theorem quat_conj_norm (q v : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    Quaternion.normSq (q * v * star q) = Quaternion.normSq v := by
  rw [map_mul, map_mul, Quaternion.normSq_star, hq]
  ring
-- @endregion

-- @region matrix_groups.quat_neg_same
-- @provenance independent
/-- **`q` and `−q` give the same rotation**: `(−q) v (−q)̄ = q v q̄`, since the two signs cancel.
This is the "two-to-one" in the double cover `SU(2) → SO(3)`: its kernel contains `±1`. -/
theorem quat_neg_same (q v : Quaternion ℝ) : (-q) * v * star (-q) = q * v * star q := by
  rw [star_neg, neg_mul, mul_neg, neg_mul, neg_neg]
-- @endregion

end Lumenary.MatrixGroups
