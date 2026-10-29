/-
The Lumenary — Lean exercises: Matrix groups and continuous symmetry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/MatrixGroups.lean`.
-/
import Lumenary.MatrixGroups

namespace LumenaryExercises.MatrixGroups

open Matrix

-- @region ex.matrix_groups.det_orthogonal
-- @solution Lumenary.MatrixGroups.det_orthogonal
/-- An orthogonal matrix has determinant `1` or `-1`.
Hint: take determinants of `Aᵀ * A = 1` using `det_mul`, `det_transpose` and `det_one`, then use
`mul_self_eq_one_iff`. -/
theorem det_orthogonal {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : Aᵀ * A = 1) : A.det = 1 ∨ A.det = -1 := by
  sorry
-- @endregion

-- @region ex.matrix_groups.quat_neg_same
-- @solution Lumenary.MatrixGroups.quat_neg_same
/-- The unit quaternions `q` and `-q` induce the same rotation `v ↦ q v q̄`.
Hint: `star_neg`, `neg_mul`, `mul_neg` and `neg_neg`. -/
theorem quat_neg_same (q v : Quaternion ℝ) : (-q) * v * star (-q) = q * v * star q := by
  sorry
-- @endregion

end LumenaryExercises.MatrixGroups
