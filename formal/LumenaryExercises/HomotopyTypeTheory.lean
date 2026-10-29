/-
The Lumenary — Lean exercises: Homotopy type theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/HomotopyTypeTheory.lean`.
-/
import Lumenary.HomotopyTypeTheory

namespace LumenaryExercises.HomotopyTypeTheory

open Lumenary.HomotopyTypeTheory Lumenary.HomotopyTypeTheory.Paths

-- @region ex.homotopy_type_theory.concat_inv
-- @solution Lumenary.HomotopyTypeTheory.Paths.concat_inv
/-- The inverse law `p ⬝ p⁻¹ = refl`, as a path between paths, by path induction. Hint: use
`J` with the motive `fun _ p => Paths (concat p (inv p)) refl`; when `p` is `refl`, both sides
compute to `refl`, so the base case is `refl`. -/
def concat_inv {A : Type} {a b : A} (p : Paths a b) : Paths (concat p (inv p)) Paths.refl :=
  sorry
-- @endregion

-- @region ex.homotopy_type_theory.univalence_fails
-- @solution Lumenary.HomotopyTypeTheory.Paths.univalence_fails
/-- Univalence is false in Lean. Hint: if `idtoeqv` were surjective, pick paths `p` and `q` with
`idtoeqv p = Equiv.refl Bool` and `idtoeqv q = Equiv.boolNot`; `paths_subsingleton p q` gives
`p = q`; evaluate the two equivalences at `true` to get `true = false`. -/
theorem univalence_fails :
    ¬ Function.Surjective (idtoeqv : Paths Bool Bool → (Bool ≃ Bool)) := by
  sorry
-- @endregion

end LumenaryExercises.HomotopyTypeTheory
