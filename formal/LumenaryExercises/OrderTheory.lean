/-
The Lumenary — Lean exercises: Orders, lattices and well-orders.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/OrderTheory.lean`.
-/
import Lumenary.OrderTheory

namespace LumenaryExercises.OrderTheory

-- @region ex.order_theory.absorption
-- @solution Lumenary.OrderTheory.absorption
/-- The absorption law in any lattice.
Hint: `le_antisymm`, with `sup_le le_rfl inf_le_left` for one inequality and `le_sup_left`
for the other. -/
theorem absorption {L : Type*} [Lattice L] (a b : L) : a ⊔ (a ⊓ b) = a := by
  sorry
-- @endregion

-- @region ex.order_theory.knaster_tarski
-- @solution Lumenary.OrderTheory.knaster_tarski
/-- Knaster–Tarski: a monotone map on a complete lattice has a least fixed point.
Hint: take `a := sInf {x | f x ≤ x}` and use `le_sInf` and `sInf_le`. -/
theorem knaster_tarski {L : Type*} [CompleteLattice L] (f : L → L) (hf : Monotone f) :
    ∃ a, f a = a ∧ ∀ b, f b = b → a ≤ b := by
  sorry
-- @endregion

end LumenaryExercises.OrderTheory
