/-
The Lumenary — Lean exercises: Linear algebra.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LinearAlgebra.lean`.
-/
import Lumenary.LinearAlgebra

namespace LumenaryExercises.LinearAlgebra

-- @region ex.linear_algebra.solutions_translate_ker
-- @solution Lumenary.LinearAlgebra.solutions_translate_ker
/-- If `x₀` solves `f x = b`, then `x` solves it exactly when `x - x₀` is in the kernel.
Hint: `LinearMap.mem_ker`, `map_sub` and `sub_eq_zero` are the three rewrites you need. -/
theorem solutions_translate_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) {x₀ : V} {b : W} (h₀ : f x₀ = b) (x : V) :
    f x = b ↔ x - x₀ ∈ LinearMap.ker f := by
  sorry
-- @endregion

-- @region ex.linear_algebra.mul_not_comm
-- @solution Lumenary.LinearAlgebra.mul_not_comm
/-- Find two `2 × 2` rational matrices that do not commute.
Hint: try `!![0, 1; 0, 0]` and `!![0, 0; 1, 0]`, and compare the top-left entries of the two
products with `congrFun` and `simp [Matrix.mul_apply, Fin.sum_univ_two]`. -/
theorem mul_not_comm : ∃ A B : Matrix (Fin 2) (Fin 2) ℚ, A * B ≠ B * A := by
  sorry
-- @endregion

end LumenaryExercises.LinearAlgebra
