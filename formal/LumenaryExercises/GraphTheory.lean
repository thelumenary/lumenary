/-
The Lumenary — Lean exercises: Graph theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/GraphTheory.lean`.
-/
import Lumenary.GraphTheory

namespace LumenaryExercises.GraphTheory

open Finset

-- @region ex.graph_theory.planar_edge_bound
-- @solution Lumenary.GraphTheory.planar_edge_bound
/-- From Euler's formula and `3F ≤ 2E`, deduce `E ≤ 3V − 6`.
Hint: this is linear arithmetic over `ℤ`; the tactic `omega` can do it. Try it by hand first:
substitute `F = 2 − V + E` into `3F ≤ 2E`. -/
theorem planar_edge_bound (V E F : ℤ) (euler : V - E + F = 2) (faces : 3 * F ≤ 2 * E) :
    E ≤ 3 * V - 6 := by
  sorry
-- @endregion

-- @region ex.graph_theory.hall_necessary
-- @solution Lumenary.GraphTheory.hall_necessary
/-- The easy direction of Hall's theorem. Hint: show `s.image f ⊆ s.biUnion t`, then use
`card_image_of_injective` and `card_le_card`. -/
theorem hall_necessary {ι α : Type*} [DecidableEq α] (t : ι → Finset α) (f : ι → α)
    (hf : Function.Injective f) (hft : ∀ i, f i ∈ t i) (s : Finset ι) :
    #s ≤ #(s.biUnion t) := by
  sorry
-- @endregion

end LumenaryExercises.GraphTheory
