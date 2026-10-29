/-
The Lumenary — Lean exercises: Mathematical writing.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/MathematicalWriting.lean`.
-/
import Lumenary.MathematicalWriting

namespace LumenaryExercises.MathematicalWriting

-- @region ex.mathematical_writing.not_exists_forall_gt
-- @solution Lumenary.MathematicalWriting.not_exists_forall_gt
/-- "There is a natural number bigger than every natural number" is false.
Hint: assume `⟨m, hm⟩` and apply `hm` to `m` itself; `lt_irrefl` finishes. -/
theorem not_exists_forall_gt : ¬ ∃ m : ℕ, ∀ n : ℕ, n < m := by
  sorry
-- @endregion

-- @region ex.mathematical_writing.sq_eq_four_int
-- @solution Lumenary.MathematicalWriting.sq_eq_four_int
/-- Over the integers, `x² = 4` does not force `x = 2`. Hint: find the counterexample, apply the
hypothesis to it, and let `norm_num` derive the contradiction. -/
theorem sq_eq_four_int : ¬ ∀ x : ℤ, x ^ 2 = 4 → x = 2 := by
  sorry
-- @endregion

end LumenaryExercises.MathematicalWriting
