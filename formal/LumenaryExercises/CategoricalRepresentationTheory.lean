/-
The Lumenary — Lean exercises: Categorical representation theory.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/CategoricalRepresentationTheory.lean`.
-/
import Lumenary.CategoricalRepresentationTheory

namespace LumenaryExercises.CategoricalRepresentationTheory

-- @region ex.categorical_representation_theory.fibonacci_no_integer_dimension
-- @solution Lumenary.CategoricalRepresentationTheory.fibonacci_no_integer_dimension
/-- No integer `n` satisfies `n² = 1 + n`, so the Fibonacci fusion rule `τ ⊗ τ = 1 ⊕ τ` has no
integer-valued dimension. Hint: bound `n` with `nlinarith`, then use `interval_cases n`. -/
theorem fibonacci_no_integer_dimension : ¬ ∃ n : ℤ, n ^ 2 = 1 + n := by
  sorry
-- @endregion

end LumenaryExercises.CategoricalRepresentationTheory
