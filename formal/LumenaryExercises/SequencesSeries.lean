/-
The Lumenary — Lean exercises: Sequences and series.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/SequencesSeries.lean`.
-/
import Lumenary.SequencesSeries

namespace LumenaryExercises.SequencesSeries

open Finset

-- @region ex.sequences_series.geom_telescope
-- @solution Lumenary.SequencesSeries.geom_telescope
/-- Prove the telescoping identity behind the geometric sum, by induction on `n`.
Hint: in the step, `rw [sum_range_succ, mul_add, ih, pow_succ]` and then `ring`. -/
theorem geom_telescope (r : ℝ) (n : ℕ) : (1 - r) * ∑ k ∈ range n, r ^ k = 1 - r ^ n := by
  sorry
-- @endregion

-- @region ex.sequences_series.hanoi_formula
-- @solution Lumenary.SequencesSeries.hanoi_formula
/-- Prove that the Tower of Hanoi numbers satisfy `h(n) + 1 = 2ⁿ`.
Hint: induction on `n`; in the step, unfold one step of the recursion with
`rw [Lumenary.SequencesSeries.hanoi, pow_succ, ← ih]` and finish with `ring`. -/
theorem hanoi_formula (n : ℕ) : Lumenary.SequencesSeries.hanoi n + 1 = 2 ^ n := by
  sorry
-- @endregion

end LumenaryExercises.SequencesSeries
