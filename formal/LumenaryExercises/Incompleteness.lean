/-
The Lumenary — Lean exercises: Gödel's incompleteness theorems.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Incompleteness.lean`.
-/
import Lumenary.Incompleteness

namespace LumenaryExercises.Incompleteness

open Lumenary.Incompleteness

-- @region ex.incompleteness.cantor_from_lawvere
-- @solution Lumenary.Incompleteness.cantor_from_lawvere
/-- Derive Cantor's theorem from Lawvere's fixed-point theorem: there is no surjection from `A`
onto the predicates on `A`.
Hint: apply `lawvere_fixed_point e he Not` and show that `¬P = P` is impossible
(`iff_not_self` and `Iff.of_eq` help). -/
theorem cantor_from_lawvere {A : Type*} (e : A → A → Prop) : ¬ Function.Surjective e := by
  sorry
-- @endregion

-- @region ex.incompleteness.first_incompleteness
-- @solution Lumenary.Incompleteness.DiagSystem.first_incompleteness
/-- In a sound diagonalisable system in which provability is expressible, some true sentence is
unprovable. Hint: use `S.diagonal_lemma` with the complement of the provable codes, and argue as
in the lesson: a provable `G` would be true, hence unprovable. -/
theorem true_but_unprovable (S : DiagSystem)
    (sound : ∀ s, S.Provable s → S.True s)
    (hprov : S.Expressible (S.scode '' {s | S.Provable s}))
    (hcompl : ∀ A : Set ℕ, S.Expressible A → S.Expressible Aᶜ)
    (hdiag : ∀ A : Set ℕ, S.Expressible A → S.Expressible (S.diag ⁻¹' A)) :
    ∃ G : S.Sentence, S.True G ∧ ¬ S.Provable G := by
  sorry
-- @endregion

end LumenaryExercises.Incompleteness
