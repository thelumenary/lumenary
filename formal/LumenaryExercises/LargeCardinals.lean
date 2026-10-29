/-
The Lumenary — Lean exercises: large cardinals.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LargeCardinals.lean`.
-/
import Lumenary.LargeCardinals

namespace LumenaryExercises.LargeCardinals

open Cardinal Set Lumenary.LargeCardinals

universe u

-- @region ex.large_cardinals.sunion_mem
-- @solution Lumenary.LargeCardinals.sUnion_mem
/-- The axiom of Union holds in `V_κ`. Hint: rewrite with `ZFSet.mem_vonNeumann` (membership in
`V_α` means rank below `α`) and use `ZFSet.rank_sUnion_le`. -/
theorem sUnion_mem {κ : Cardinal.{u}} {x : ZFSet.{u}} (hx : x ∈ ZFSet.vonNeumann κ.ord) :
    ZFSet.sUnion x ∈ ZFSet.vonNeumann κ.ord := by
  sorry
-- @endregion

-- @region ex.large_cardinals.principal_of_card_lt
-- @solution Lumenary.LargeCardinals.principal_of_card_lt
/-- A κ-complete ultrafilter on a set with fewer than `κ` elements is principal.
Hint: argue by contradiction (`by_contra! h`); then `U` is non-principal, so apply
`le_card_of_mem` to the set `univ ∈ U` and compare with `mk_univ`. -/
theorem principal_of_card_lt {κ : Cardinal.{u}} {α : Type u} {U : Ultrafilter α}
    (hc : IsComplete κ U) (hα : #α < κ) : ∃ a : α, ({a} : Set α) ∈ U := by
  sorry
-- @endregion

-- @region ex.large_cardinals.nat_countably_complete_principal
-- @solution Lumenary.LargeCardinals.nat_countably_complete_principal
/-- A countably complete ultrafilter on `ℕ` is principal, so `ℵ₀` is not measurable.
Hint: if no `{n}` is in `U`, every `{n}ᶜ` is (`Ultrafilter.compl_mem_iff_notMem`); use
`countable_iInter_mem` and show `⋂ n, {n}ᶜ = ∅`. -/
theorem nat_countably_complete_principal (U : Ultrafilter ℕ)
    [CountableInterFilter (U : Filter ℕ)] : ∃ n : ℕ, ({n} : Set ℕ) ∈ U := by
  sorry
-- @endregion

end LumenaryExercises.LargeCardinals
