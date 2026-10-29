/-
The Lumenary — Lean exercises: Completeness, compactness and Löwenheim–Skolem.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CompletenessTheorem.lean`
(the `@solution` line names the solved theorem).
-/
import Lumenary.CompletenessTheorem

namespace LumenaryExercises.CompletenessTheorem

universe u v

open FirstOrder FirstOrder.Language

-- @region ex.completeness_theorem.maximal_mem_or_neg_mem
-- @solution Lumenary.CompletenessTheorem.maximal_mem_or_neg_mem
/-- A maximal consistent set contains every sentence or its negation, provided consistency splits.
Hint: apply `hsplit Δ φ hΔ.prop` and, in each case, `Maximal.mem_of_prop_insert`. -/
theorem maximal_mem_or_neg_mem {S : Type u} (Con : Set S → Prop) (neg : S → S)
    (hsplit : ∀ Γ φ, Con Γ → Con (insert φ Γ) ∨ Con (insert (neg φ) Γ))
    {Δ : Set S} (hΔ : Maximal Con Δ) (φ : S) : φ ∈ Δ ∨ neg φ ∈ Δ := by
  sorry
-- @endregion

-- @region ex.completeness_theorem.satisfiable_split
-- @solution Lumenary.CompletenessTheorem.satisfiable_split
/-- If `T` has a model, then `T ∪ {φ}` or `T ∪ {¬φ}` has a model.
Hint: take a model `M` (`obtain ⟨M⟩ := hT`), split on `M ⊨ φ`, and use
`Theory.model_insert_iff`, `Sentence.realize_not` and `Theory.Model.isSatisfiable`. -/
theorem satisfiable_split {L : Language.{u, v}} (T : L.Theory) (φ : L.Sentence)
    (hT : T.IsSatisfiable) : (insert φ T).IsSatisfiable ∨ (insert φ.not T).IsSatisfiable := by
  sorry
-- @endregion

end LumenaryExercises.CompletenessTheorem
