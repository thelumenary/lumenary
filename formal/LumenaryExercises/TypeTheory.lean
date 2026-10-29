/-
The Lumenary — Lean exercises: type theory and propositions as types.
Replace each `sorry` with a proof term or tactic proof. Worked solutions are in
`Lumenary/TypeTheory.lean`.
-/
import Lumenary.TypeTheory

namespace LumenaryExercises.TypeTheory

-- @region ex.type_theory.not_not_em
-- @solution Lumenary.TypeTheory.not_not_em
/-- Excluded middle cannot be refuted — constructively. Write a λ-term: given
`h : ¬(A ∨ ¬A)`, build a proof of `¬A` and feed it to `h`. -/
theorem not_not_em (A : Prop) : ¬¬(A ∨ ¬A) :=
  sorry
-- @endregion

-- @region ex.type_theory.s_combinator
-- @solution Lumenary.TypeTheory.s_combinator
/-- The S combinator as a proof. -/
theorem s_combinator (A B C : Prop) : (A → B → C) → (A → B) → A → C :=
  sorry
-- @endregion

-- @region ex.type_theory.zero_add
-- @solution Lumenary.TypeTheory.N.zero_add
/-- `0 + n = n` for the home-made natural numbers, by induction. Hint: use
`Lumenary.TypeTheory.N.induction`, or the `induction` tactic. -/
theorem zero_add (n : Lumenary.TypeTheory.N) :
    Lumenary.TypeTheory.N.add Lumenary.TypeTheory.N.zero n = n := by
  sorry
-- @endregion

end LumenaryExercises.TypeTheory
