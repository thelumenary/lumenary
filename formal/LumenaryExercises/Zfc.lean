/-
The Lumenary — Lean exercises: ZFC.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Zfc.lean`
(the `@solution` line names the solved theorem).
-/
import Lumenary.Zfc

namespace LumenaryExercises.Zfc

universe u

-- @region ex.zfc.not_mem_self
-- @solution Lumenary.Zfc.not_mem_self
/-- No set is a member of itself.
Hint: assume `hx : x ∈ x` and apply `Lumenary.Zfc.foundation` to the set `{x}`
(you must first show `({x} : ZFSet) ≠ ∅`). Useful lemmas: `ZFSet.mem_singleton`,
`ZFSet.mem_inter`, `ZFSet.notMem_empty`. -/
theorem not_mem_self (x : ZFSet.{u}) : x ∉ x := by
  sorry
-- @endregion

-- @region ex.zfc.no_universal_set
-- @solution Lumenary.Zfc.no_universal_set
/-- There is no set of all sets.
Hint: from `⟨U, hU⟩`, use `Lumenary.Zfc.separation (fun x => x ∉ x) U` to get Russell's set
`R`, show `R ∈ R ↔ R ∉ R`, and derive `False` without using excluded middle. -/
theorem no_universal_set : ¬ ∃ U : ZFSet.{u}, ∀ x, x ∈ U := by
  sorry
-- @endregion

end LumenaryExercises.Zfc
