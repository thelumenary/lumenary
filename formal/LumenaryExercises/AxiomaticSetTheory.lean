/-
The Lumenary — Lean exercises: axiomatic set theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AxiomaticSetTheory.lean`.
-/
import Lumenary.AxiomaticSetTheory

namespace LumenaryExercises.AxiomaticSetTheory

open Cardinal Ordinal

-- @region ex.axiomatic_set_theory.no_mem_two_cycle
-- @solution Lumenary.AxiomaticSetTheory.no_mem_two_cycle
/-- There are no membership 2-cycles `x ∈ y ∈ x`.
Hint: `ZFSet.rank_lt_of_mem : y ∈ x → rank y < rank x`; chain two of these and use `lt_irrefl`. -/
theorem no_mem_two_cycle (x y : ZFSet) : ¬ (x ∈ y ∧ y ∈ x) := by
  sorry
-- @endregion

-- @region ex.axiomatic_set_theory.gch_continuum
-- @solution Lumenary.AxiomaticSetTheory.gch_continuum
/-- The generalised continuum hypothesis implies the continuum hypothesis.
Hint: specialise `h` to `κ = ℵ₀` and rewrite with `Cardinal.succ_aleph0`. -/
theorem gch_continuum (h : Lumenary.AxiomaticSetTheory.GCH.{0}) :
    (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁ := by
  sorry
-- @endregion

end LumenaryExercises.AxiomaticSetTheory
