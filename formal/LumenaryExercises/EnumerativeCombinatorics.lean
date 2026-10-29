/-
The Lumenary — Lean exercises: Enumerative combinatorics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/EnumerativeCombinatorics.lean`.
-/
import Lumenary.EnumerativeCombinatorics

namespace LumenaryExercises.EnumerativeCombinatorics

open Finset

-- @region ex.enumerative_combinatorics.burnside_double_count
-- @solution Lumenary.EnumerativeCombinatorics.burnside_double_count
/-- Double counting: both sides count the pairs `(g, x)` with `g • x = x`.
Hint: `Finset.card_filter` rewrites a filtered card as a sum of `if … then 1 else 0`;
then `Finset.sum_comm` swaps the order of summation. -/
theorem burnside_double_count {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    [DecidableEq X] :
    ∑ g : G, #(univ.filter fun x : X => g • x = x) =
      ∑ x : X, #(univ.filter fun g : G => g • x = x) := by
  sorry
-- @endregion

-- @region ex.enumerative_combinatorics.derangements_formula
-- @solution Lumenary.EnumerativeCombinatorics.derangements_formula
/-- The derangement formula. Hint: induction on `n`. In the step, cast Mathlib's
`numDerangements_succ` to `ℚ` (`exact_mod_cast`), split off the last term of the sum
(`Finset.sum_range_succ`), expand `(n + 1)! = (n + 1) * n!` (`Nat.factorial_succ`), and finish
with `push_cast`, `field_simp` and `ring`. -/
theorem derangements_formula (n : ℕ) :
    (numDerangements n : ℚ) =
      n.factorial * ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / k.factorial := by
  sorry
-- @endregion

end LumenaryExercises.EnumerativeCombinatorics
