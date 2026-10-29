/-
The Lumenary — Lean exercises: the λ-calculus.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LambdaCalculus.lean`.
-/
import Lumenary.LambdaCalculus

namespace LumenaryExercises.LambdaCalculus

open Lumenary.LambdaCalculus Relation

-- @region ex.lambda_calculus.theta_fixed_point
-- @solution Lumenary.LambdaCalculus.theta_fixed_point
/-- Turing's combinator reaches `F (Θ F)` in two β-steps. Hint: the first step is a β-step in
the function position (`Step.appL`), the second a β-step at the top; combine them with
`ReflTransGen.head` and `ReflTransGen.single`. -/
theorem theta_fixed_point (F : Term) :
    ReflTransGen Step (Term.app theta F) (Term.app F (Term.app theta F)) := by
  sorry
-- @endregion

-- @region ex.lambda_calculus.diamond_confluent
-- @solution Lumenary.LambdaCalculus.diamond_confluent
/-- Diamond implies confluence. Hint: induct on `hab`, and use the strip lemma
`Lumenary.LambdaCalculus.strip` for each step. -/
theorem diamond_confluent {α : Type*} {r : α → α → Prop} (hd : Diamond r) {a b c : α}
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) :
    ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d := by
  sorry
-- @endregion

end LumenaryExercises.LambdaCalculus
