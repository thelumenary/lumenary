/-
The Lumenary — Lean exercises: forcing.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Forcing.lean`.
-/
import Lumenary.Forcing

namespace LumenaryExercises.Forcing

open Lumenary.Forcing Lumenary.Forcing.Cohen

-- @region ex.forcing.avoids_dense
-- @solution Lumenary.Forcing.Cohen.avoids_dense
/-- For every real `x`, the conditions that disagree with `x` somewhere form a dense set.
Hint: extend `p` by the single bit `!x p.bits.length`, i.e. use the condition
`⟨p.bits ++ [!x p.bits.length]⟩`; `List.prefix_append` shows it extends `p`, and `simp` computes
its bit at position `p.bits.length`. -/
theorem avoids_dense (x : ℕ → Bool) : IsCofinal {p : Cohen | ∃ i, bit p i = some (!x i)} := by
  sorry
-- @endregion

-- @region ex.forcing.cohen_real_not_in_list
-- @solution Lumenary.Forcing.cohen_real_not_in_list
/-- Every countable list of reals misses some real. Prove it *by forcing*: apply
`rasiowa_sikorski` to the dense sets `decides n` and `avoids (xs k)` (index them by `ℕ ⊕ ℕ`),
then use `generic_real`. -/
theorem cohen_real_not_in_list (xs : ℕ → ℕ → Bool) : ∃ g : ℕ → Bool, ∀ k, g ≠ xs k := by
  sorry
-- @endregion

end LumenaryExercises.Forcing
