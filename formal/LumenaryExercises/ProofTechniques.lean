/-
The Lumenary — Lean exercises: Proof techniques.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProofTechniques.lean`.
-/
import Lumenary.ProofTechniques

namespace LumenaryExercises.ProofTechniques

open Finset

-- @region ex.proof_techniques.odd_add_odd
-- @solution Lumenary.ProofTechniques.odd_add_odd
/-- A direct proof: the sum of two odd integers is even.
Hint: `obtain ⟨a, rfl⟩ := hm` unpacks `m = 2 * a + 1`; then give the witness for `Even`
(`Even k` means `k = r + r`) and finish with `ring`. -/
theorem odd_add_odd {m n : ℤ} (hm : Odd m) (hn : Odd n) : Even (m + n) := by
  sorry
-- @endregion

-- @region ex.proof_techniques.sum_odd
-- @solution Lumenary.ProofTechniques.sum_odd
/-- Induction: the first `n` odd numbers add up to `n²`.
Hint: `induction n with | zero => rfl | succ n ih => ?_`, then `rw [sum_range_succ, ih]` and
`ring`. -/
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  sorry
-- @endregion

end LumenaryExercises.ProofTechniques
