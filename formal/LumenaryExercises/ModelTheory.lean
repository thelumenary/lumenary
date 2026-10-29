/-
The Lumenary — Lean exercises: Model theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ModelTheory.lean`.
-/
import Lumenary.ModelTheory

namespace LumenaryExercises.ModelTheory

-- @region ex.model_theory.nonstandard_ne_standard
-- @solution Lumenary.ModelTheory.nonstandard_ne_standard
/-- Show that the class of the identity sequence in the ultrapower `ℕ^ℕ/U` is not equal to the
class of any constant sequence. Hint: `Lumenary.ModelTheory.nonstandard_natural n` gives a strict
inequality, and `LT.lt.ne` turns `a < b` into `a ≠ b`. -/
theorem nonstandard_ne_standard (n : ℕ) :
    (↑(fun _ : ℕ => n) : (Filter.hyperfilter ℕ : Filter ℕ).Germ ℕ) ≠ ↑(id : ℕ → ℕ) := by
  sorry
-- @endregion

-- @region ex.model_theory.dlo_elim_core_fails_discrete
-- @solution Lumenary.ModelTheory.dlo_elim_core_fails_discrete
/-- Density is needed for the key lemma of quantifier elimination: in `ℤ`, the constraint
`0 < 1` holds but no integer lies strictly between `0` and `1`. Hint: after `refine ⟨by simp, ?_⟩`
and `rintro ⟨x, h0, h1⟩`, extract `0 < x` and `x < 1` and finish with `omega`. -/
theorem dlo_elim_core_fails_discrete :
    (∀ a ∈ ({0} : Finset ℤ), ∀ b ∈ ({1} : Finset ℤ), a < b) ∧
      ¬ ∃ x : ℤ, (∀ a ∈ ({0} : Finset ℤ), a < x) ∧ ∀ b ∈ ({1} : Finset ℤ), x < b := by
  sorry
-- @endregion

end LumenaryExercises.ModelTheory
