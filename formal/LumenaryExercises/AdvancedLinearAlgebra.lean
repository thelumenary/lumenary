/-
The Lumenary — Lean exercises: Advanced linear algebra.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AdvancedLinearAlgebra.lean`.
-/
import Lumenary.AdvancedLinearAlgebra

namespace LumenaryExercises.AdvancedLinearAlgebra

-- @region ex.advanced_linear_algebra.eigenvectors_orthogonal
-- @solution Lumenary.AdvancedLinearAlgebra.eigenvectors_orthogonal
/-- Eigenvectors of a symmetric operator for distinct eigenvalues are orthogonal.
Hint: compute `inner ℝ (T v) w` in two ways, using `real_inner_smul_left`,
`real_inner_smul_right` and the hypothesis `hT v w : inner ℝ (T v) w = inner ℝ v (T w)`. -/
theorem eigenvectors_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {a b : ℝ} {v w : E}
    (hv : T v = a • v) (hw : T w = b • w) (hab : a ≠ b) : inner ℝ v w = 0 := by
  sorry
-- @endregion

-- @region ex.advanced_linear_algebra.cayley_hamilton_two
-- @solution Lumenary.AdvancedLinearAlgebra.cayley_hamilton_two
/-- Cayley–Hamilton for 2 × 2 matrices. Hint: `ext i j`, then `fin_cases i <;> fin_cases j`,
and expand with `Matrix.mul_apply`, `Fin.sum_univ_two`, `Matrix.trace_fin_two` and
`Matrix.det_fin_two` before finishing with `ring`. -/
theorem cayley_hamilton_two {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  sorry
-- @endregion

end LumenaryExercises.AdvancedLinearAlgebra
