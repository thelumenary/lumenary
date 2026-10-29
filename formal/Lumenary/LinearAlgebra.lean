/-
The Lumenary — formal mathematics
Linear algebra: solution sets of linear systems, linear maps and matrices, rank–nullity,
determinants, eigenvectors and a matrix that cannot be diagonalised.

Mathlib has a very general linear algebra library: `Module K V` is a vector space over a
field `K`, `V →ₗ[K] W` is a linear map, `Matrix m n K` a matrix, `Module.finrank` the
dimension and `Module.End.HasEigenvector` the eigenvector predicate. Several results below
re-prove a fact from more basic ones, mirroring the proofs in the lesson
(`@provenance independent`): solution sets are translates of the kernel, a worked Gaussian
elimination, non-commutativity of matrix multiplication, "more unknowns than equations" from
rank–nullity, the independence of eigenvectors for two distinct eigenvalues, and the fact that
the nilpotent matrix with rows (0, 1) and (0, 0) is not diagonalisable. Others apply Mathlib
directly (`@provenance library`): rank–nullity itself, invariance of dimension, matrices of
composites, and the determinant criterion for invertibility.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Lumenary.LinearAlgebra

open Matrix

/-! ### Linear systems -/

-- @region linear_algebra.solutions_translate_ker
-- @provenance independent
/-- **Solution sets are translates of the kernel.** If `x₀` is one solution of `f x = b`,
then `x` is a solution exactly when `x - x₀` lies in the kernel of `f`: the general solution is
"one particular solution plus the general solution of the homogeneous system". The proof is
the human one: `f x - f x₀ = f (x - x₀)` by linearity. -/
theorem solutions_translate_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) {x₀ : V} {b : W} (h₀ : f x₀ = b) (x : V) :
    f x = b ↔ x - x₀ ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker, map_sub, h₀, sub_eq_zero]
-- @endregion

-- @region linear_algebra.system_matrix
-- @provenance definition
/-- The coefficient matrix of the worked example in the lesson:
`x + 2y + z = 4`, `2x + 4y + 3z = 9` (two equations, three unknowns). -/
def systemMatrix : Matrix (Fin 2) (Fin 3) ℚ := !![1, 2, 1; 2, 4, 3]
-- @endregion

-- @region linear_algebra.worked_system
-- @provenance independent
/-- **The worked Gaussian elimination, checked.** Elimination reduces the system to
`x + 2y = 3`, `z = 1` with `y` free, so the solutions are exactly
`(3, 0, 1) + t·(-2, 1, 0)`: a line, the translate of the one-dimensional null space by a
particular solution. Here `t` is the free variable `y`. -/
theorem worked_system (x : Fin 3 → ℚ) :
    systemMatrix *ᵥ x = ![4, 9] ↔ ∃ t : ℚ, x = ![3, 0, 1] + t • ![-2, 1, 0] := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [systemMatrix, mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    refine ⟨x 1, ?_⟩
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro ⟨t, rfl⟩
    funext i
    fin_cases i <;> simp [systemMatrix, mulVec, dotProduct, Fin.sum_univ_three] <;> ring
-- @endregion

/-! ### Linear maps, matrices and composition -/

-- @region linear_algebra.to_lin_mul
-- @provenance library
/-- **Composition is matrix multiplication.** The linear map of `M * N` is the composite
"first `N`, then `M`". This is Mathlib's `Matrix.toLin'_mul`; it is the reason matrix
multiplication is defined the way it is. -/
theorem toLin_mul {K : Type*} [Field K] {l m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix l m K) (N : Matrix m n K) :
    Matrix.toLin' (M * N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  Matrix.toLin'_mul M N
-- @endregion

-- @region linear_algebra.mul_not_comm
-- @provenance independent
/-- **Matrix multiplication is not commutative.** With `A = !![0, 1; 0, 0]` and
`B = !![0, 0; 1, 0]`, the top-left entries of `A * B` and `B * A` are `1` and `0`. -/
theorem mul_not_comm : ∃ A B : Matrix (Fin 2) (Fin 2) ℚ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], fun h => ?_⟩
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
-- @endregion

-- @region linear_algebra.rot
-- @provenance definition
/-- The matrix of the rotation of the plane by the angle `θ`: its columns are the images
`(cos θ, sin θ)` and `(-sin θ, cos θ)` of the standard basis vectors. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
-- @endregion

-- @region linear_algebra.rot_mul_rot
-- @provenance independent
/-- **Rotations compose by adding angles.** Rotating by `β` and then by `α` is rotating by
`α + β`. Multiplying the matrices entry by entry turns this into the addition formulas for
cosine and sine (`Real.cos_add`, `Real.sin_add`). -/
theorem rot_mul_rot (α β : ℝ) : rot α * rot β = rot (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring
-- @endregion

/-! ### Dimension and rank–nullity -/

-- @region linear_algebra.bases_same_card
-- @provenance library
/-- **Invariance of dimension.** Any two finite bases of a vector space have the same number
of elements. Both are equal to `Module.finrank K V` by Mathlib's `Module.finrank_eq_card_basis`,
whose proof rests on the exchange argument given in the lesson. -/
theorem bases_same_card {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V) :
    Fintype.card ι = Fintype.card ι' :=
  (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis b')
-- @endregion

-- @region linear_algebra.rank_nullity
-- @provenance library
/-- **Rank–nullity.** For a linear map `f : V → W` with `V` finite-dimensional,
`dim (im f) + dim (ker f) = dim V`. This is Mathlib's `LinearMap.finrank_range_add_finrank_ker`. -/
theorem rank_nullity {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f
-- @endregion

-- @region linear_algebra.exists_nonzero_solution
-- @provenance independent
/-- **More unknowns than equations.** A homogeneous system of `m` equations in `n > m`
unknowns has a non-zero solution. Proof from rank–nullity, as in the lesson:
`dim ker = n - dim im ≥ n - m > 0`, and a subspace of positive dimension contains a non-zero
vector. -/
theorem exists_nonzero_solution {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (h : m < n) : ∃ x : Fin n → K, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have him : Module.finrank K (LinearMap.range A.mulVecLin) ≤ m := by
    simpa using (LinearMap.range A.mulVecLin).finrank_le
  have hdim : Module.finrank K (Fin n → K) = n := by simp
  have hpos : 0 < Module.finrank K (LinearMap.ker A.mulVecLin) := by omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hpos)
  exact ⟨x, hx0, by simpa using hx⟩
-- @endregion

/-! ### Determinants and invertibility -/

-- @region linear_algebra.is_unit_iff_det_ne_zero
-- @provenance library
/-- **The determinant test.** A square matrix over a field is invertible if and only if its
determinant is non-zero. This combines Mathlib's `Matrix.isUnit_iff_isUnit_det` with the fact
that the units of a field are its non-zero elements. -/
theorem isUnit_iff_det_ne_zero {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
-- @endregion

-- @region linear_algebra.cols_independent_iff
-- @provenance library
/-- **The column test.** A square matrix over a field is invertible if and only if its
columns are linearly independent: Mathlib's `Matrix.linearIndependent_col_iff_isUnit`. -/
theorem cols_independent_iff {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : LinearIndependent K A.col ↔ IsUnit A :=
  Matrix.linearIndependent_col_iff_isUnit
-- @endregion

/-! ### Eigenvalues, eigenvectors and diagonalisation -/

-- @region linear_algebra.eigen_pair_independent
-- @provenance independent
/-- **Eigenvectors for distinct eigenvalues are independent** (two at a time). Suppose
`s • v + t • w = 0`. Applying `T` gives `s λ v + t μ w = 0`; subtracting `λ` times the first
equation leaves `t (μ - λ) w = 0`, so `t = 0` because `μ ≠ λ` and `w ≠ 0`; then `s v = 0`
forces `s = 0`. -/
theorem eigen_pair_independent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : V →ₗ[K] V) {v w : V} {lam mu : K} (hv : T v = lam • v) (hw : T w = mu • w)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hne : lam ≠ mu) : LinearIndependent K ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- Apply `T` to the relation.
  have hT : (s * lam) • v + (t * mu) • w = 0 := by
    have := congrArg T hst
    rw [map_add, map_smul, map_smul, hv, hw, map_zero, smul_smul, smul_smul] at this
    exact this
  -- Subtract `lam` times the relation.
  have hdiff : (t * (mu - lam)) • w = 0 := by
    have h2 : lam • (s • v + t • w) = 0 := by rw [hst, smul_zero]
    calc (t * (mu - lam)) • w
        = ((s * lam) • v + (t * mu) • w) - lam • (s • v + t • w) := by
          rw [smul_add, smul_smul, smul_smul, mul_sub, sub_smul]; abel_nf; module
      _ = 0 := by rw [hT, h2, sub_zero]
  have ht : t = 0 := by
    rcases smul_eq_zero.mp hdiff with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd (sub_eq_zero.mp h').symm hne
    · exact absurd h hw0
  refine ⟨?_, ht⟩
  rw [ht, zero_smul, add_zero] at hst
  rcases smul_eq_zero.mp hst with h | h
  · exact h
  · exact absurd h hv0
-- @endregion

-- @region linear_algebra.eigenvectors_independent
-- @provenance library
/-- **Eigenvectors for distinct eigenvalues are independent** (any number at a time). This is
Mathlib's `Module.End.eigenvectors_linearIndependent'`, proved there by showing that the
eigenspaces form an independent family of subspaces. -/
theorem eigenvectors_independent {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : ι → K) (hμ : Function.Injective μ) (v : ι → V)
    (hv : ∀ i, T.HasEigenvector (μ i) (v i)) : LinearIndependent K v :=
  T.eigenvectors_linearIndependent' μ hμ v hv
-- @endregion

-- @region linear_algebra.nilpotent_not_diagonalisable
-- @provenance independent
/-- **Not every matrix is diagonalisable.** The matrix `N = !![0, 1; 0, 0]` is not similar to
any diagonal matrix `D`: there is no invertible `P` with `N P = P D`. Proof from the lesson:
`N² = 0`, so `P D² = N² P = 0`, so `D² = 0` (cancel the invertible `P`), so every diagonal
entry of `D` is `0`; then `N P = P D = 0` and cancelling `P` again gives `N = 0`, which is
false. -/
theorem nilpotent_not_diagonalisable {K : Type*} [Field K] :
    ¬ ∃ (P : Matrix (Fin 2) (Fin 2) K) (d : Fin 2 → K),
      IsUnit P ∧ !![0, 1; 0, 0] * P = P * Matrix.diagonal d := by
  rintro ⟨P, d, hP, hNP⟩
  set N : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0] with hN
  have hNN : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hN, Matrix.mul_apply, Fin.sum_univ_two]
  -- `P D² = 0`.
  have hPDD : P * (Matrix.diagonal d * Matrix.diagonal d) = 0 := by
    calc P * (Matrix.diagonal d * Matrix.diagonal d)
        = (P * Matrix.diagonal d) * Matrix.diagonal d := (Matrix.mul_assoc _ _ _).symm
      _ = (N * P) * Matrix.diagonal d := by rw [hNP]
      _ = N * (P * Matrix.diagonal d) := Matrix.mul_assoc _ _ _
      _ = N * (N * P) := by rw [hNP]
      _ = (N * N) * P := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hNN, Matrix.zero_mul]
  -- So `D² = 0`, hence `D = 0`.
  have hDD : Matrix.diagonal d * Matrix.diagonal d = 0 := (hP.mul_right_eq_zero).mp hPDD
  have hd : ∀ i, d i = 0 := by
    intro i
    have := congrFun (congrFun hDD i) i
    simpa [Matrix.diagonal_mul_diagonal] using this
  have hD : Matrix.diagonal d = 0 := by
    ext i j
    simp [Matrix.diagonal_apply, hd]
  -- Then `N P = 0`, hence `N = 0`: a contradiction.
  have hN0 : N = 0 := by
    have : N * P = 0 := by rw [hNP, hD, Matrix.mul_zero]
    exact (hP.mul_left_eq_zero).mp this
  have h01 := congrFun (congrFun hN0 0) 1
  simp [hN] at h01
-- @endregion

end Lumenary.LinearAlgebra
