/-
The Lumenary — Lean exercises: Real analysis.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RealAnalysis.lean`.
-/
import Lumenary.RealAnalysis

namespace LumenaryExercises.RealAnalysis

open Lumenary.RealAnalysis

-- @region ex.real_analysis.converges_to_add
-- @solution Lumenary.RealAnalysis.convergesTo_add
/-- Prove that the limit of a sum is the sum of the limits, from the ε–N definition.
Hint: ask for `ε / 2` from each hypothesis, take `N = max N₁ N₂`, and finish with `abs_add_le`. -/
theorem convergesTo_add {a b : ℕ → ℝ} {A B : ℝ} (ha : ConvergesTo a A) (hb : ConvergesTo b B) :
    ConvergesTo (fun n => a n + b n) (A + B) := by
  sorry
-- @endregion

-- @region ex.real_analysis.cauchy_of_converges_to
-- @solution Lumenary.RealAnalysis.cauchy_of_convergesTo
/-- Prove that every convergent sequence is Cauchy.
Hint: write `aₘ - aₙ = (aₘ - L) - (aₙ - L)` and use `abs_sub`. -/
theorem cauchy_of_convergesTo {a : ℕ → ℝ} {L : ℝ} (h : ConvergesTo a L) : IsCauchy a := by
  sorry
-- @endregion

end LumenaryExercises.RealAnalysis
