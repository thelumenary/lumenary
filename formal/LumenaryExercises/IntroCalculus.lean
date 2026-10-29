/-
The Lumenary — Lean exercises: Introductory calculus.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/IntroCalculus.lean`.
-/
import Lumenary.IntroCalculus

namespace LumenaryExercises.IntroCalculus

open Finset

-- @region ex.intro_calculus.diff_quotient_sq
-- @solution Lumenary.IntroCalculus.diff_quotient_sq
/-- Simplify the difference quotient of `x²`. Hint: `field_simp` clears the denominator `h`
(it uses `hh : h ≠ 0`), and `ring` finishes. -/
theorem diff_quotient_sq (a h : ℝ) (hh : h ≠ 0) : ((a + h) ^ 2 - a ^ 2) / h = 2 * a + h := by
  sorry
-- @endregion

-- @region ex.intro_calculus.sum_squares
-- @solution Lumenary.IntroCalculus.sum_squares
/-- Prove the formula for the sum of the first squares by induction.
Hint: `induction n with | zero => simp | succ m ih => ?_`; in the step use `sum_range_succ`,
then `ih`, `push_cast` and `ring`. -/
theorem sum_squares (n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry
-- @endregion

end LumenaryExercises.IntroCalculus
