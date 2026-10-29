/-
The Lumenary — Lean exercises: Real numbers and irrationality.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RealNumbers.lean`.
-/
import Lumenary.RealNumbers

namespace LumenaryExercises.RealNumbers

-- @region ex.real_numbers.rat_add_irrational
-- @solution Lumenary.RealNumbers.rat_add_irrational
/-- Show that a rational number plus an irrational number is irrational.
Hint: `rintro ⟨r, hr⟩` gives a rational `r` with `(r : ℝ) = q + x`. Show that `x` would be the
rational number `r - q`; `push_cast` and `ring` help with the arithmetic. -/
theorem rat_add_irrational (q : ℚ) {x : ℝ} (hx : Irrational x) : Irrational (q + x) := by
  sorry
-- @endregion

-- @region ex.real_numbers.triangle_inequality
-- @solution Lumenary.RealNumbers.triangle_inequality
/-- Prove the triangle inequality. Hint: `abs_le` turns `|t| ≤ c` into `-c ≤ t ∧ t ≤ c`; the
facts `neg_abs_le x : -|x| ≤ x` and `le_abs_self x : x ≤ |x|` and `linarith` do the rest. -/
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
-- @endregion

end LumenaryExercises.RealNumbers
