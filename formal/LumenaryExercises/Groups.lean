/-
The Lumenary — Lean exercises: Groups.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Groups.lean`.
-/
import Lumenary.Groups

namespace LumenaryExercises.Groups

-- @region ex.groups.comm_of_sq_eq_one
-- @solution Lumenary.Groups.comm_of_sq_eq_one
/-- If every element of a group squares to `1`, the group is abelian.
Hint: first show `x⁻¹ = x` for every `x` (`inv_eq_of_mul_eq_one_right`), then compute
`a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹` (`mul_inv_rev`). -/
theorem comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  sorry
-- @endregion

-- @region ex.groups.pow_card_eq_one
-- @solution Lumenary.Groups.pow_card_eq_one
/-- Every element satisfies `g ^ |G| = 1`.
Hint: `orderOf_dvd_natCard g` gives `k` with `Nat.card G = orderOf g * k`; then use `pow_mul`
and `pow_orderOf_eq_one`. -/
theorem pow_card_eq_one {G : Type*} [Group G] (g : G) : g ^ Nat.card G = 1 := by
  sorry
-- @endregion

-- @region ex.groups.cayley
-- @solution Lumenary.Groups.cayley
/-- Cayley's theorem: the left regular action `G → Perm G` is injective.
Hint: apply both permutations to `1`. -/
theorem cayley {G : Type*} [Group G] : Function.Injective (MulAction.toPermHom G G) := by
  sorry
-- @endregion

end LumenaryExercises.Groups
