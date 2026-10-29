/-
The Lumenary — Lean exercises: Combinatorics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Combinatorics.lean`.
-/
import Lumenary.Combinatorics

namespace LumenaryExercises.Combinatorics

open Finset

-- @region ex.combinatorics.row_sum
-- @solution Lumenary.Combinatorics.row_sum
/-- Each row of Pascal's triangle adds up to `2ⁿ`.
Hint: `Lumenary.Combinatorics.binomial_one_add (1 : ℕ) n` says
`(1 + 1) ^ n = ∑ k ∈ range (n + 1), (n.choose k : ℕ) * 1 ^ k`; `simpa` can tidy it up. -/
theorem row_sum (n : ℕ) : ∑ k ∈ range (n + 1), n.choose k = 2 ^ n := by
  sorry
-- @endregion

-- @region ex.combinatorics.incl_excl_three
-- @solution Lumenary.Combinatorics.incl_excl_three
/-- Inclusion–exclusion for three sets, from the two-set rule `card_union_add_card_inter`.
Hint: apply the two-set rule three times, rewrite `(A ∪ B) ∩ C` with
`union_inter_distrib_right`, and finish with `omega`. -/
theorem incl_excl_three {α : Type*} [DecidableEq α] (A B C : Finset α) :
    #(A ∪ B ∪ C) + #(A ∩ B) + #(A ∩ C) + #(B ∩ C) = #A + #B + #C + #(A ∩ B ∩ C) := by
  sorry
-- @endregion

end LumenaryExercises.Combinatorics
