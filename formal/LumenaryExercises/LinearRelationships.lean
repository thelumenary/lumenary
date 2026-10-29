/-
The Lumenary — Lean exercises: Linear relationships and simultaneous equations.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LinearRelationships.lean`.
-/
import Lumenary.LinearRelationships

namespace LumenaryExercises.LinearRelationships

-- @region ex.linear_relationships.parallel_system
-- @solution Lumenary.LinearRelationships.parallel_system
/-- Show that the system `x + y = 3`, `2x + 2y = 10` has no solution.
Hint: `intro ⟨x, y, h₁, h₂⟩`. Doubling `h₁` gives `2x + 2y = 6`; combine it with `h₂` to get
`(6 : Rat) = 10` (`grind` can help), then finish with `absurd` and `decide`. -/
theorem parallel_system : ¬ ∃ x y : Rat, x + y = 3 ∧ 2 * x + 2 * y = 10 := by
  sorry
-- @endregion

-- @region ex.linear_relationships.comp_linear
-- @solution Lumenary.LinearRelationships.comp_linear
/-- Doing `x ↦ m₂·x + b₂` and then `x ↦ m₁·x + b₁` gives a linear function whose slope is the
product of the slopes. Hint: `Rat.mul_add` expands the bracket; `grind` collects the terms. -/
theorem comp_linear (m₁ b₁ m₂ b₂ x : Rat) :
    m₁ * (m₂ * x + b₂) + b₁ = (m₁ * m₂) * x + (m₁ * b₂ + b₁) := by
  sorry
-- @endregion

end LumenaryExercises.LinearRelationships
