/-
The Lumenary — Lean exercises: Optimisation.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Optimisation.lean`.
-/
import Lumenary.Optimisation

namespace LumenaryExercises.Optimisation

open Matrix

-- @region ex.optimisation.weak_duality
-- @solution Lumenary.Optimisation.weak_duality
/-- Weak duality for linear programs.
Hint: a `calc` chain with `dotProduct_le_dotProduct_of_nonneg_right`, `dotProduct_mulVec`,
`dotProduct_le_dotProduct_of_nonneg_left` and `dotProduct_comm`. -/
theorem weak_duality {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ)
    (c : n → ℝ) (x : n → ℝ) (y : m → ℝ) (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ b) (hy : 0 ≤ y)
    (hAy : c ≤ y ᵥ* A) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  sorry
-- @endregion

-- @region ex.optimisation.optimality_certificate
-- @solution Lumenary.Optimisation.optimality_certificate
/-- Equal primal and dual values certify optimality. Hint: rewrite with `heq` and apply weak
duality (`Lumenary.Optimisation.weak_duality`) to `x'` and `y`. -/
theorem optimality_certificate {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ) (hy : 0 ≤ y) (hAy : c ≤ y ᵥ* A)
    (heq : c ⬝ᵥ x = b ⬝ᵥ y) (x' : n → ℝ) (hx' : 0 ≤ x') (hAx' : A *ᵥ x' ≤ b) :
    c ⬝ᵥ x' ≤ c ⬝ᵥ x := by
  sorry
-- @endregion

end LumenaryExercises.Optimisation
