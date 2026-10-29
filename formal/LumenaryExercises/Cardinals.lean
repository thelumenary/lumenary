/-
The Lumenary — Lean exercises: Ordinals and cardinals.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Cardinals.lean`
(the `@solution` line names the solved theorem).
-/
import Lumenary.Cardinals

namespace LumenaryExercises.Cardinals

universe u

open Ordinal

-- @region ex.cardinals.cantor_no_surjection
-- @solution Lumenary.Cardinals.cantor_no_surjection
/-- Cantor's theorem: no function `α → Set α` is surjective.
Hint: suppose `hf : Function.Surjective f`, obtain `a` with `f a = {x | x ∉ f x}`, and show
`a ∈ f a ↔ a ∉ f a`. You can finish without excluded middle. -/
theorem cantor_no_surjection {α : Type u} (f : α → Set α) : ¬ Function.Surjective f := by
  sorry
-- @endregion

-- @region ex.cardinals.add_not_comm
-- @solution Lumenary.Cardinals.add_not_comm
/-- Ordinal addition is not commutative: `1 + ω ≠ ω + 1`.
Hint: rewrite with `Ordinal.one_add_omega0`, then use `lt_add_one ω` and `ne_of_lt`. -/
theorem add_not_comm : (1 : Ordinal.{u}) + ω ≠ ω + 1 := by
  sorry
-- @endregion

end LumenaryExercises.Cardinals
