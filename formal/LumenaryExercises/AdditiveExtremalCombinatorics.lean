/-
The Lumenary — Lean exercises: Extremal and additive combinatorics.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/AdditiveExtremalCombinatorics.lean`.
-/
import Lumenary.AdditiveExtremalCombinatorics

namespace LumenaryExercises.AdditiveExtremalCombinatorics

open Lumenary.AdditiveExtremalCombinatorics

-- @region ex.additive_extremal_combinatorics.ramsey_one_left
-- @solution Lumenary.AdditiveExtremalCombinatorics.ramsey_one_left
/-- `R(1, t) ≤ 1`: every non-empty vertex set contains a `1`-clique.
Hint: get a vertex `v ∈ W` from `Finset.card_pos`, and use `{v}` with
`SimpleGraph.isNClique_one`. -/
theorem ramsey_one_left {α : Type*} (t : ℕ) : RamseyProp α 1 t 1 := by
  sorry
-- @endregion

-- @region ex.additive_extremal_combinatorics.ramsey_diag
-- @solution Lumenary.AdditiveExtremalCombinatorics.ramsey_diag
/-- Deduce the diagonal bound `R(k + 1, k + 1) ≤ 4ᵏ` from `ramsey_binomial`.
Hint: `Nat.choose_le_two_pow` gives `C(2k, k) ≤ 2^(2k) = 4ᵏ`. -/
theorem ramsey_diag {α : Type*} [DecidableEq α] (k : ℕ) :
    RamseyProp α (k + 1) (k + 1) (4 ^ k) := by
  sorry
-- @endregion

end LumenaryExercises.AdditiveExtremalCombinatorics
