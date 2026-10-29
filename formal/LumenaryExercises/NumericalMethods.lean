/-
The Lumenary — Lean exercises: Numerical methods.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/NumericalMethods.lean`.
-/
import Lumenary.NumericalMethods

namespace LumenaryExercises.NumericalMethods

open Lumenary.NumericalMethods

-- @region ex.numerical_methods.heron_ge_sqrt
-- @solution Lumenary.NumericalMethods.heron_ge_sqrt
/-- Show that every Heron iterate from a positive start is at least `√a`.
Hint: use `heron_error` and the fact that `(x - √a) ^ 2 / (2 * x)` is non-negative
(`positivity`), then `linarith`. -/
theorem heron_ge_sqrt {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) : √a ≤ (x + a / x) / 2 := by
  sorry
-- @endregion

-- @region ex.numerical_methods.bisect_sign
-- @solution Lumenary.NumericalMethods.bisect_sign
/-- Prove the loop invariant of bisection.
Hint: induction on `n`; in the step, unfold `bisect` and `bisectStep` and split on the `if`
(`split_ifs with h`). In the `else` branch, `h : ¬ f m ≤ 0` gives `0 < f m`. -/
theorem bisect_sign (f : ℝ → ℝ) (a b : ℝ) (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    f (bisect f a b n).1 ≤ 0 ∧ 0 ≤ f (bisect f a b n).2 := by
  sorry
-- @endregion

end LumenaryExercises.NumericalMethods
