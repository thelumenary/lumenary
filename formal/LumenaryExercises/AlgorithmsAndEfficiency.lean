/-
The Lumenary — Lean exercises: Algorithms, correctness and efficiency.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AlgorithmsAndEfficiency.lean`.
-/
import Lumenary.AlgorithmsAndEfficiency

namespace LumenaryExercises.AlgorithmsAndEfficiency

open Lumenary.AlgorithmsAndEfficiency

-- @region ex.algorithms_and_efficiency.linear_comparisons_le
-- @solution Lumenary.AlgorithmsAndEfficiency.linearComparisons_le
/-- Linear search makes at most `n` comparisons on a list of length `n`.
Hint: `induction xs with | nil => … | cons x xs ih => …`; in the `cons` case,
`simp only [linearComparisons, List.length_cons]` and then `split_ifs <;> omega`. -/
theorem linearComparisons_le (t : ℕ) (xs : List ℕ) : linearComparisons t xs ≤ xs.length := by
  sorry
-- @endregion

-- @region ex.algorithms_and_efficiency.sorting_lower_bound
-- @solution Lumenary.AlgorithmsAndEfficiency.sorting_lower_bound
/-- If a decision tree has at least `n!` leaves, then `n! ≤ 2 ^ height`.
Hint: chain `h` with `leaves_le_two_pow_height t` using `le_trans` (or `h.trans`). -/
theorem sorting_lower_bound (n : ℕ) (t : DecisionTree) (h : n.factorial ≤ t.leaves) :
    n.factorial ≤ 2 ^ t.height := by
  sorry
-- @endregion

end LumenaryExercises.AlgorithmsAndEfficiency
