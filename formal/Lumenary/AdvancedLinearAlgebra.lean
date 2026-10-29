/-
The Lumenary — formal mathematics
Advanced linear algebra: the spectral theorem, Cayley–Hamilton, Jordan blocks and generalised
eigenspaces, dual spaces and the natural map to the double dual, and tensor products.

Mathlib's `InnerProductSpace 𝕜 E` (with `𝕜 = ℝ` or `ℂ`, packaged as `RCLike 𝕜`) is an inner
product space, `T.IsSymmetric` says `⟪T x, y⟫ = ⟪x, T y⟫` (self-adjoint), `Module.Dual K V` is the
dual space `V →ₗ[K] K`, `f.dualMap` is the transpose `W* → V*` and `V ⊗[K] W` is the tensor
product, built by its universal property `TensorProduct.lift`. Proved here from more basic facts
(`@provenance independent`), mirroring the lesson: eigenvalues of self-adjoint operators are real,
eigenvectors for distinct eigenvalues are orthogonal, Cayley–Hamilton for 2 × 2 matrices, the
minimal polynomial of a 3 × 3 Jordan block, a non-zero complex symmetric matrix with square zero,
the naturality of `V → V**`, and the fact that `e₁ ⊗ e₁ + e₂ ⊗ e₂` is not a pure tensor. Applied
from Mathlib (`@provenance library`): the spectral theorem itself, Cayley–Hamilton in general, the
generalised eigenspace decomposition, `V ≅ V**`, `dim V* = dim V`, the universal property and the
dimension of `V ⊗ W`. Not formalised: the Jordan normal form theorem as a statement about matrices
(Mathlib has the generalised eigenspace decomposition and the Jordan–Chevalley decomposition, not
yet the block form), and the theorem that no natural isomorphism `V ≅ V*` exists.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Complex.Basic

namespace Lumenary.AdvancedLinearAlgebra

open Module
open scoped Matrix

/-! ### Inner product spaces and the spectral theorem -/

-- @region advanced_linear_algebra.eigenvalue_real
-- @provenance independent
/-- **Eigenvalues of a self-adjoint operator are real.** If `T v = μ v` with `v ≠ 0`, then
`conj μ ⟪v, v⟫ = ⟪T v, v⟫ = ⟪v, T v⟫ = μ ⟪v, v⟫`, and `⟪v, v⟫ ≠ 0` can be cancelled. (Mathlib's
inner product is conjugate-linear in the *first* slot, hence the `conj` on the left.) This is
Lemma 1 of the lesson; Mathlib's version is `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/
theorem eigenvalue_real {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {μ : 𝕜} {v : E} (hv0 : v ≠ 0) (hv : T v = μ • v) :
    starRingEnd 𝕜 μ = μ := by
  have h : starRingEnd 𝕜 μ * inner 𝕜 v v = μ * inner 𝕜 v v :=
    calc starRingEnd 𝕜 μ * inner 𝕜 v v = inner 𝕜 (T v) v := by rw [hv, inner_smul_left]
      _ = inner 𝕜 v (T v) := hT v v
      _ = μ * inner 𝕜 v v := by rw [hv, inner_smul_right]
  exact mul_right_cancel₀ (inner_self_ne_zero.mpr hv0) h
-- @endregion

-- @region advanced_linear_algebra.eigenvectors_orthogonal
-- @provenance independent
/-- **Eigenvectors of a symmetric operator for distinct eigenvalues are orthogonal.** The proof
is Lemma 2 of the lesson: `a ⟪v, w⟫ = ⟪T v, w⟫ = ⟪v, T w⟫ = b ⟪v, w⟫`, so `(a - b) ⟪v, w⟫ = 0`
and `a ≠ b` forces `⟪v, w⟫ = 0`. -/
theorem eigenvectors_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {a b : ℝ} {v w : E}
    (hv : T v = a • v) (hw : T w = b • w) (hab : a ≠ b) : inner ℝ v w = 0 := by
  have h : a * inner ℝ v w = b * inner ℝ v w :=
    calc a * inner ℝ v w = inner ℝ (T v) w := by rw [hv, real_inner_smul_left]
      _ = inner ℝ v (T w) := hT v w
      _ = b * inner ℝ v w := by rw [hw, real_inner_smul_right]
  have h2 : (a - b) * inner ℝ v w = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hab)
-- @endregion

-- @region advanced_linear_algebra.spectral_theorem
-- @provenance library
/-- **The spectral theorem.** A self-adjoint operator `T` on a finite-dimensional real or complex
inner product space of dimension `n` has an orthonormal basis `b` of eigenvectors, with *real*
eigenvalues `μ i`. This packages Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis`,
`eigenvalues` and `apply_eigenvectorBasis`; Mathlib's proof is the lesson's (eigenspaces are
orthogonal and together span `E`). -/
theorem spectral_theorem {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) :
    ∃ (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ), ∀ i, T (b i) = (μ i : 𝕜) • b i :=
  ⟨hT.eigenvectorBasis hn, hT.eigenvalues hn, hT.apply_eigenvectorBasis hn⟩
-- @endregion

-- @region advanced_linear_algebra.symmetric_matrix_eigenbasis
-- @provenance library
/-- **Real symmetric matrices are orthogonally diagonalisable.** For a real matrix with `Aᵀ = A`
there is an orthonormal basis of `ℝⁿ` (the columns of an orthogonal matrix `Q`) consisting of
eigenvectors of `A`; equivalently `A = Q Λ Qᵀ`. Over `ℝ` the conjugate transpose is the
transpose, so `A` is Hermitian, and Mathlib's `Matrix.IsHermitian.mulVec_eigenvectorBasis`
applies. -/
theorem symmetric_matrix_eigenbasis {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Aᵀ = A) :
    ∃ (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (μ : n → ℝ),
      ∀ j, A.mulVec (b j) = μ j • (b j : n → ℝ) := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hA
  exact ⟨hH.eigenvectorBasis, hH.eigenvalues, hH.mulVec_eigenvectorBasis⟩
-- @endregion

-- @region advanced_linear_algebra.complex_symmetric_nilpotent
-- @provenance independent
/-- **"Symmetric" is not enough over `ℂ`.** The complex symmetric matrix with rows `(1, i)` and
`(i, -1)` is non-zero but squares to zero, so it is nilpotent and not diagonalisable. Over `ℂ` the
spectral theorem needs *Hermitian* (`A* = A`), not symmetric (`Aᵀ = A`). -/
theorem complex_symmetric_nilpotent :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; Complex.I, -1]
    Aᵀ = A ∧ A ≠ 0 ∧ A * A = 0 := by
  intro A
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [A] at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two]
-- @endregion

/-! ### Cayley–Hamilton, minimal polynomials and Jordan blocks -/

-- @region advanced_linear_algebra.cayley_hamilton_two
-- @provenance independent
/-- **Cayley–Hamilton for 2 × 2 matrices**, by direct computation over any commutative ring:
`A² − (tr A) A + (det A) I = 0`. The characteristic polynomial of `A` is
`x² − (tr A) x + det A`, so this says `χ_A(A) = 0`. -/
theorem cayley_hamilton_two {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
-- @endregion

-- @region advanced_linear_algebra.cayley_hamilton
-- @provenance library
/-- **The Cayley–Hamilton theorem**: every square matrix over a commutative ring is a root of its
characteristic polynomial, `χ_A(A) = 0`. This is Mathlib's `Matrix.aeval_self_charpoly`, proved
(like the lesson) with the adjugate identity `(x I − A) · adj(x I − A) = χ_A(x) I`. -/
theorem cayley_hamilton {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) : Polynomial.aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A
-- @endregion

-- @region advanced_linear_algebra.jordan_block3
-- @provenance definition
/-- The 3 × 3 **Jordan block** `J₃(μ)`: `μ` on the diagonal, `1` just above it. -/
def jordanBlock3 {K : Type*} [Field K] (μ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![μ, 1, 0; 0, μ, 1; 0, 0, μ]
-- @endregion

-- @region advanced_linear_algebra.jordan_block3_nilpotent
-- @provenance independent
/-- `N = J₃(μ) − μ I` is nilpotent: `N³ = 0`. So `(x − μ)³` annihilates `J₃(μ)`. -/
theorem jordan_block3_nilpotent {K : Type*} [Field K] (μ : K) :
    (jordanBlock3 μ - μ • (1 : Matrix (Fin 3) (Fin 3) K)) ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jordanBlock3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
-- @endregion

-- @region advanced_linear_algebra.jordan_block3_sq_ne_zero
-- @provenance independent
/-- …but `N² ≠ 0` (its top-right entry is `1`). Together with `N³ = 0` this shows that the
minimal polynomial of `J₃(μ)` is `(x − μ)³`, equal to the characteristic polynomial: no
polynomial of smaller degree kills it, so it is not diagonalisable. -/
theorem jordan_block3_sq_ne_zero {K : Type*} [Field K] (μ : K) :
    (jordanBlock3 μ - μ • (1 : Matrix (Fin 3) (Fin 3) K)) ^ 2 ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp [jordanBlock3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] at h02
-- @endregion

-- @region advanced_linear_algebra.generalized_eigenspace_decomposition
-- @provenance library
/-- **The generalised eigenspace (primary) decomposition**, the first half of the Jordan normal
form theorem: over an algebraically closed field, the generalised eigenspaces
`ker (f − μ)^∞` of an operator on a finite-dimensional space are independent and together span
the space, so `V` is their direct sum. Mathlib: `Module.End.independent_maxGenEigenspace` and
`Module.End.iSup_maxGenEigenspace_eq_top` (the latter following Axler's proof). -/
theorem generalized_eigenspace_decomposition {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : End K V) :
    iSupIndep f.maxGenEigenspace ∧ ⨆ μ : K, f.maxGenEigenspace μ = ⊤ :=
  ⟨f.independent_maxGenEigenspace, f.iSup_maxGenEigenspace_eq_top⟩
-- @endregion

/-! ### Dual spaces -/

-- @region advanced_linear_algebra.eval_natural
-- @provenance independent
/-- **`V → V**` is natural.** For every linear map `f : V → W`, the square
`V → V** → W**` equals `V → W → W**`: evaluating at `v` and then transporting along `f**` is the
same as evaluating at `f v`. No basis appears anywhere — the proof is a definitional unfolding
(`rfl`), which is exactly what "natural" means in practice. -/
theorem eval_natural {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    f.dualMap.dualMap ∘ₗ Dual.eval K V = Dual.eval K W ∘ₗ f := by
  ext v φ
  rfl
-- @endregion

-- @region advanced_linear_algebra.eval_bijective
-- @provenance library
/-- **`V ≅ V**` in finite dimensions**: the evaluation map is bijective (Mathlib's
`Module.bijective_dual_eval`, using that finite-dimensional spaces are reflexive). -/
theorem eval_bijective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Function.Bijective (Dual.eval K V) :=
  bijective_dual_eval K V
-- @endregion

-- @region advanced_linear_algebra.dual_finrank
-- @provenance library
/-- `dim V* = dim V` for finite-dimensional `V` (Mathlib's `Subspace.dual_finrank_eq`, proved
with the dual basis). So `V ≅ V*` — but only through a choice, as the lesson explains. -/
theorem dual_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : finrank K (Dual K V) = finrank K V :=
  Subspace.dual_finrank_eq
-- @endregion

/-! ### Tensor products -/

-- @region advanced_linear_algebra.tensor_universal
-- @provenance library
/-- **The universal property of `V ⊗ W`.** Every bilinear map `B : V × W → U` factors through
`(v, w) ↦ v ⊗ w` by exactly one linear map `φ : V ⊗ W → U`. Existence is
`TensorProduct.lift`; uniqueness is `TensorProduct.ext'` (linear maps that agree on pure tensors
agree everywhere, because pure tensors span). -/
theorem tensor_universal {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U] (B : V →ₗ[K] W →ₗ[K] U) :
    ∃! φ : TensorProduct K V W →ₗ[K] U, ∀ v w, φ (v ⊗ₜ w) = B v w := by
  refine ⟨TensorProduct.lift B, fun v w => TensorProduct.lift.tmul v w, ?_⟩
  intro ψ hψ
  exact TensorProduct.ext' fun v w => by rw [hψ, TensorProduct.lift.tmul]
-- @endregion

-- @region advanced_linear_algebra.finrank_tensor
-- @provenance library
/-- `dim (V ⊗ W) = dim V · dim W` (Mathlib's `Module.finrank_tensorProduct`, from the basis
`eᵢ ⊗ fⱼ`). Compare `dim (V × W) = dim V + dim W`. -/
theorem finrank_tensor {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] :
    finrank K (TensorProduct K V W) = finrank K V * finrank K W :=
  Module.finrank_tensorProduct
-- @endregion

-- @region advanced_linear_algebra.coord
-- @provenance definition
/-- The `(i, j)` **coordinate** of a tensor in `K² ⊗ K²`: the linear map induced, through the
universal property, by the bilinear map `(v, w) ↦ vᵢ wⱼ`. On a pure tensor it gives the entries
of the "outer product" matrix `v wᵀ`. -/
noncomputable def coord {K : Type*} [Field K] (i j : Fin 2) :
    TensorProduct K (Fin 2 → K) (Fin 2 → K) →ₗ[K] K :=
  TensorProduct.lift (LinearMap.mk₂ K (fun v w => v i * w j)
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp [mul_assoc])
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]))
-- @endregion

-- @region advanced_linear_algebra.not_pure_tensor
-- @provenance independent
/-- **Not every tensor is pure.** `e₁ ⊗ e₁ + e₂ ⊗ e₂` is not of the form `v ⊗ w`. Taking
coordinates: a pure tensor has coordinates `vᵢ wⱼ`, so we would need `v₁ w₁ = 1`, `v₂ w₂ = 1`
and `v₁ w₂ = 0` — impossible, since the last forces `v₁ = 0` or `w₂ = 0`. In matrix language:
the identity matrix has rank 2, while `v wᵀ` has rank at most 1. -/
theorem not_pure_tensor {K : Type*} [Field K] :
    ¬ ∃ v w : Fin 2 → K, v ⊗ₜ[K] w =
      (Pi.single 0 1 : Fin 2 → K) ⊗ₜ Pi.single 0 1 + Pi.single 1 1 ⊗ₜ Pi.single 1 1 := by
  rintro ⟨v, w, h⟩
  have c00 := congrArg (coord (K := K) 0 0) h
  have c11 := congrArg (coord (K := K) 1 1) h
  have c01 := congrArg (coord (K := K) 0 1) h
  simp [coord] at c00 c11 c01
  rcases c01 with h0 | h1
  · simp [h0] at c00
  · simp [h1] at c11
-- @endregion

end Lumenary.AdvancedLinearAlgebra
