/-
The Lumenary — Lean exercises: Computability.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Computability.lean`.
-/
import Lumenary.Computability

namespace LumenaryExercises.Computability

-- @region ex.computability.cantor_diag
-- @solution Lumenary.Computability.cantor_diag
/-- Cantor's diagonal argument: no sequence of functions `ℕ → ℕ` contains every function.
Hint: consider `fun n => e n n + 1`, and evaluate the equation `e k = …` at `k`
(`congrFun`); `omega` finishes. -/
theorem cantor_diag (e : ℕ → ℕ → ℕ) : ¬ Function.Surjective e := by
  sorry
-- @endregion

-- @region ex.computability.no_halting_decider
-- @solution Lumenary.Computability.no_halting_decider
/-- The diagonal argument behind the halting problem. Specialise both hypotheses to the
diagonal program `e` on input `e`, and do a case split on the Boolean `d e e`. -/
theorem no_halting_decider {P : Type*} (Halts : P → P → Prop) (d : P → P → Bool)
    (diag : ∃ e : P, ∀ q, Halts e q ↔ d q q = false) :
    ¬ ∀ p q, Halts p q ↔ d p q = true := by
  sorry
-- @endregion

end LumenaryExercises.Computability
