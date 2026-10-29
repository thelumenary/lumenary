/-
The Lumenary — Lean exercises: the Yoneda lemma.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Yoneda.lean`.
-/
import Lumenary.Yoneda

namespace LumenaryExercises.Yoneda

-- @region ex.yoneda.eq_of_same_lower
-- @solution Lumenary.Yoneda.eq_of_same_lower
/-- The Yoneda principle for partial orders: if exactly the same elements lie below `x` and
below `y`, then `x = y`. Hint: apply the hypothesis to `z = x` and to `z = y`, then use
`le_antisymm`. -/
theorem eq_of_same_lower {P : Type*} [PartialOrder P] {x y : P}
    (h : ∀ z, z ≤ x ↔ z ≤ y) : x = y := by
  sorry
-- @endregion

-- @region ex.yoneda.equivariant_eq_mul_left
-- @solution Lumenary.Yoneda.equivariant_eq_cayley
/-- Cayley, the Yoneda way: a function on a group that commutes with every right
multiplication is left multiplication by its value at `1`. Hint: `x = 1 * x`. -/
theorem equivariant_eq_mul_left {G : Type*} [Group G] (σ : G → G)
    (hσ : ∀ x h : G, σ (x * h) = σ x * h) (x : G) : σ x = σ 1 * x := by
  sorry
-- @endregion

end LumenaryExercises.Yoneda
