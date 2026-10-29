/-
The Lumenary — Lean exercises: First steps in Lean.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/IntroLean.lean`.
You can try these in the Lean web editor; each one needs only a few lines.
-/
import Lumenary.IntroLean

namespace LumenaryExercises.IntroLean

open Lumenary.IntroLean

-- @region ex.intro_lean.and_swap
-- @solution Lumenary.IntroLean.and_swap_tactics
/-- Swap the two halves of an "and".
Hint: `intro h`, then `obtain ⟨hp, hq⟩ := h`, then `constructor`, then `exact` twice. -/
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p := by
  sorry
-- @endregion

-- @region ex.intro_lean.contrapositive
-- @solution Lumenary.IntroLean.contrapositive
/-- The contrapositive. Remember that `¬q` means `q → False`.
Hint: `intro hnq hp`, then `exact hnq (hpq hp)`. -/
theorem contrapositive (p q : Prop) (hpq : p → q) : ¬q → ¬p := by
  sorry
-- @endregion

-- @region ex.intro_lean.or_swap
-- @solution Lumenary.IntroLean.or_swap
/-- Swap the two sides of an "or".
Hint: `intro h`, then `cases h with | inl hp => … | inr hq => …`; use `Or.inr` and `Or.inl`. -/
theorem or_swap (p q : Prop) : p ∨ q → q ∨ p := by
  sorry
-- @endregion

-- @region ex.intro_lean.zero_add
-- @solution Lumenary.IntroLean.zero_add_induction
/-- `0 + n = n`. Try `rfl` first and read the error: it does not work, because addition is
defined by recursion on the *second* argument. Then use induction.
Hint: `induction n with | zero => rfl | succ k ih => rw [Nat.add_succ, ih]`. -/
theorem zero_add (n : ℕ) : 0 + n = n := by
  sorry
-- @endregion

end LumenaryExercises.IntroLean
