/-
The Lumenary — Lean exercises: proof theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProofTheory.lean`.
-/
import Lumenary.ProofTheory

namespace LumenaryExercises.ProofTheory

open Lumenary.ProofTheory Lumenary.ProofTheory.Fml

-- @region ex.proof_theory.consistency
-- @solution Lumenary.ProofTheory.consistency
/-- Consistency from soundness: the empty sequent has no derivation, even with cut.
Hint: `soundness d` is a validity statement; apply it to any valuation and look at the list. -/
theorem consistency : ¬ Deriv true [] := by
  sorry
-- @endregion

-- @region ex.proof_theory.not_derivable_atom
-- @solution Lumenary.ProofTheory.not_derivable_atom
/-- The sequent `⊢ p₀` is not derivable. Hint: find a valuation that makes `p₀` false and use
`soundness`. -/
theorem not_derivable_atom : ¬ Deriv true [pos 0] := by
  sorry
-- @endregion

end LumenaryExercises.ProofTheory
