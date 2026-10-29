/-
The Lumenary — Lean exercises: Counting principles.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CountingPrinciples.lean`.
-/
import Lumenary.CountingPrinciples

namespace LumenaryExercises.CountingPrinciples

open Lumenary.CountingPrinciples

-- @region ex.counting_principles.perm_self
-- @solution Lumenary.CountingPrinciples.perm_self
/-- Arranging all `n` objects: `P(n, n) = n!`.
Hint: `have h := perm_mul_fact n n (Nat.le_refl n)`, then rewrite `h` with `Nat.sub_self`,
`fact` and `Nat.mul_one`. -/
theorem perm_self (n : Nat) : perm n n = fact n := by
  sorry
-- @endregion

-- @region ex.counting_principles.complement_principle
-- @solution Lumenary.CountingPrinciples.complement_principle
/-- Every item either has property `p` or does not.
Hint: `induction S with | nil => rfl | cons a S ih => ?_`, then `cases h : p a` and finish each
case with `simp [h]` followed by `omega`. -/
theorem complement_principle {α : Type} (S : List α) (p : α → Bool) :
    (S.filter p).length + (S.filter (fun x => !p x)).length = S.length := by
  sorry
-- @endregion

end LumenaryExercises.CountingPrinciples
