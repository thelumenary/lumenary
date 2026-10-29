/-
The Lumenary — Lean exercises: Mathematical biology.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/MathematicalBiology.lean`.
-/
import Lumenary.MathematicalBiology

namespace LumenaryExercises.MathematicalBiology

-- @region ex.mathematical_biology.sir_total_constant
-- @solution Lumenary.MathematicalBiology.sir_total_constant
/-- Show that the SIR model conserves the total population.
Hint: add the three derivative hypotheses with `HasDerivAt.add`, then use `convert … using 1`
and `ring` to see that the sum of the right-hand sides is `0`. -/
theorem sir_total_constant {β γ N : ℝ} {S I R : ℝ → ℝ} {t : ℝ}
    (hS : HasDerivAt S (-(β * S t * I t / N)) t)
    (hI : HasDerivAt I (β * S t * I t / N - γ * I t) t) (hR : HasDerivAt R (γ * I t) t) :
    HasDerivAt (fun s => S s + I s + R s) 0 t := by
  sorry
-- @endregion

-- @region ex.mathematical_biology.logistic_stable_iff
-- @solution Lumenary.MathematicalBiology.logistic_stable_iff
/-- Show that the non-trivial fixed point of the logistic map has multiplier of modulus less
than `1` exactly when `1 < r < 3`. Hint: `abs_lt` turns `|a| < 1` into `-1 < a ∧ a < 1`. -/
theorem logistic_stable_iff (r : ℝ) : |2 - r| < 1 ↔ 1 < r ∧ r < 3 := by
  sorry
-- @endregion

end LumenaryExercises.MathematicalBiology
