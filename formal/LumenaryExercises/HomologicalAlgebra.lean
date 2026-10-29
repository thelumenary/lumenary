/-
The Lumenary — Lean exercises: Homological algebra (d ∘ d = 0, a non-split extension).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/HomologicalAlgebra.lean`.
-/
import Lumenary.HomologicalAlgebra

namespace LumenaryExercises.HomologicalAlgebra

open Lumenary.HomologicalAlgebra

-- @region ex.homological_algebra.rp2_dd
-- @solution Lumenary.HomologicalAlgebra.rp2_dd
/-- In the cellular chain complex of `ℝP²`, the boundary of the boundary is zero.
Hint: `ext i j`, then `fin_cases i <;> fin_cases j` and `simp` with the definitions
`rp2_d1`, `rp2_d2`, `Matrix.mul_apply` and `Fin.sum_univ_two`. -/
theorem rp2_dd : rp2_d1 * rp2_d2 = 0 := by
  sorry
-- @endregion

-- @region ex.homological_algebra.hom_zmod_two_int
-- @solution Lumenary.HomologicalAlgebra.hom_zmod_two_int
/-- Every additive map `ℤ/2 → ℤ` is zero.
Hint: first show `f 1 + f 1 = 0` using `map_add` and `(1 : ZMod 2) + 1 = 0` (true by `rfl`),
then `omega` gives `f 1 = 0`. Finally `ext x`, and split `x = 0 ∨ x = 1` (prove it by
`revert x; decide`). -/
theorem hom_zmod_two_int (f : ZMod 2 →+ ℤ) : f = 0 := by
  sorry
-- @endregion

end LumenaryExercises.HomologicalAlgebra
