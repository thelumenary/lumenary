/-
The Lumenary — Lean exercises: the geometry of spacetime.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Relativity.lean`.
-/
import Lumenary.Relativity

namespace LumenaryExercises.Relativity

-- @region ex.relativity.velocity_addition
-- @solution Lumenary.Relativity.velocity_addition
/-- **You cannot add your way past the speed of light.** Hint: from `abs_lt` get `-1 < u < 1`
and `-1 < v < 1`; show `0 < 1 + u * v` by `nlinarith`, rewrite with `abs_div`, `abs_of_pos`,
`div_lt_one` and `abs_lt`, and finish both inequalities with `nlinarith` (they are
`(1 - u)(1 - v) > 0` and `(1 + u)(1 + v) > 0`). -/
theorem velocity_addition {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    |(u + v) / (1 + u * v)| < 1 := by
  sorry
-- @endregion

-- @region ex.relativity.isco
-- @solution Lumenary.Relativity.isco
/-- **The innermost stable circular orbit is at `6M`.** Hint: substitute `L² = 12 M²`; the
circular-orbit equation becomes `M (r − 6M)² = 0`. -/
theorem isco {M L r : ℝ} (hM : 0 < M) (hL : L ^ 2 = 12 * M ^ 2)
    (hcirc : M * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2 = 0) : r = 6 * M := by
  sorry
-- @endregion

end LumenaryExercises.Relativity
