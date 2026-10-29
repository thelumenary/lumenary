/-
The Lumenary — Lean exercises: Complex numbers.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ComplexNumbers.lean`.
-/
import Lumenary.ComplexNumbers

namespace LumenaryExercises.ComplexNumbers

open Complex

-- @region ex.complex_numbers.quadratic_example
-- @solution Lumenary.ComplexNumbers.quadratic_example
/-- Check that `z = −1 + 2i` solves `z² + 2z + 5 = 0`.
Hint: expand by hand first: the two sides differ by a multiple of `i² + 1`. The tactic
`linear_combination c * I_sq` closes the goal for the right constant `c`. -/
theorem quadratic_example : (-1 + 2 * I) ^ 2 + 2 * (-1 + 2 * I) + 5 = 0 := by
  sorry
-- @endregion

-- @region ex.complex_numbers.norm_sq_mul
-- @solution Lumenary.ComplexNumbers.normSq_mul
/-- Prove that `|zw|² = |z|² |w|²`. Hint: `simp only [normSq_apply, mul_re, mul_im]` writes both
sides in terms of real and imaginary parts; then it is the two-squares identity, and `ring`
finishes. -/
theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w := by
  sorry
-- @endregion

end LumenaryExercises.ComplexNumbers
