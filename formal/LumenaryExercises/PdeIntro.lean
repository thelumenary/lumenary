/-
The Lumenary — Lean exercises: Partial differential equations and Fourier series.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/PdeIntro.lean`.
-/
import Lumenary.PdeIntro

namespace LumenaryExercises.PdeIntro

open Lumenary.PdeIntro

-- @region ex.pde_intro.heat_step_bounded
-- @solution Lumenary.PdeIntro.heatStep_bounded
/-- Prove the one-step discrete maximum principle: if `0 ≤ r ≤ 1/2` and all values of `u` lie in
`[m, M]`, then so do all values of `heatStep r u`.
Hint: unfold `heatStep`; the weights `r`, `1 - 2r`, `r` are non-negative and sum to `1`. Multiply
the bounds for `u (j - 1)`, `u j`, `u (j + 1)` by these weights (`mul_le_mul_of_nonneg_left`) and
add (`nlinarith` or `linarith`). -/
theorem heatStep_bounded {r m M : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) {u : ℤ → ℝ}
    (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (j : ℤ) : m ≤ heatStep r u j ∧ heatStep r u j ≤ M := by
  sorry
-- @endregion

end LumenaryExercises.PdeIntro
