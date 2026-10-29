/-
The Lumenary — Lean exercises: Adjunctions (Galois connections).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Adjunctions.lean`.
-/
import Lumenary.Adjunctions

namespace LumenaryExercises.Adjunctions

universe u

variable {α β : Type u}

-- @region ex.adjunctions.right_adjoint_unique
-- @solution Lumenary.Adjunctions.right_adjoint_unique
/-- Right adjoints between posets are unique.
Hint: `funext b`, then `le_antisymm`. For `u b ≤ u' b`, use `gc' (u b) b` to reduce to
`l (u b) ≤ b`, which is `(gc (u b) b).2 le_rfl`. The other inequality is symmetric. -/
theorem right_adjoint_unique [PartialOrder α] [Preorder β] {l : α → β} {u u' : β → α}
    (gc : GaloisConnection l u) (gc' : GaloisConnection l u') : u = u' := by
  sorry
-- @endregion

-- @region ex.adjunctions.left_adjoint_sup
-- @solution Lumenary.Adjunctions.left_adjoint_sup
/-- Left adjoints preserve binary joins.
Hint: `le_antisymm`. For `l (a ⊔ b) ≤ l a ⊔ l b`, rewrite with `gc` to get
`a ⊔ b ≤ u (l a ⊔ l b)` and use `sup_le`, turning each `l a ≤ l a ⊔ l b` back with `gc`.
For the other inequality use `gc.monotone_l`. -/
theorem left_adjoint_sup [SemilatticeSup α] [SemilatticeSup β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (a b : α) : l (a ⊔ b) = l a ⊔ l b := by
  sorry
-- @endregion

end LumenaryExercises.Adjunctions
