/-
The Lumenary — Lean exercises: Propositional logic and truth tables.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/PropositionalLogic.lean`.
-/
import Lumenary.PropositionalLogic

namespace LumenaryExercises.PropositionalLogic

-- @region ex.propositional_logic.contrapositive
-- @solution Lumenary.PropositionalLogic.contrapositive
/-- From `p → q`, prove `¬q → ¬p`.
Hint: `¬q` is a function from proofs of `q` to `False`. Start with `intro hnq hp`. -/
theorem contrapositive {p q : Prop} (h : p → q) : ¬q → ¬p := by
  sorry
-- @endregion

-- @region ex.propositional_logic.de_morgan_or
-- @solution Lumenary.PropositionalLogic.de_morgan_or
/-- De Morgan: "not (p or q)" is the same as "not p and not q".
Hint: use `constructor`; for each direction, `intro` the hypotheses and use `Or.inl`, `Or.inr`
or `Or.elim`. No classical logic is needed. -/
theorem de_morgan_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  sorry
-- @endregion

-- @region ex.propositional_logic.not_every_prime_odd
-- @solution Lumenary.PropositionalLogic.not_every_prime_odd
/-- Refute "every prime is odd" with a counterexample.
Hint: `intro h`, then apply `h` to `2` and `Nat.prime_two`, and use `decide` to see that `2` is
not odd. -/
theorem not_every_prime_odd : ¬ ∀ n : ℕ, n.Prime → Odd n := by
  sorry
-- @endregion

end LumenaryExercises.PropositionalLogic
