/-
The Lumenary — Lean exercises: Quivers and path algebras (lengths of paths, idempotents).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/PathAlgebras.lean`.
-/
import Lumenary.PathAlgebras

namespace LumenaryExercises.PathAlgebras

open Lumenary.PathAlgebras

-- @region ex.path_algebras.path_length_le
-- @solution Lumenary.PathAlgebras.path_length_le
/-- If every arrow increases a height function, paths are short.
Hint: `induction p with | nil => simp | cons p e ih => ?_`; in the second case rewrite with
`Quiver.Path.length_cons`, record `hh e`, and finish with `omega`. -/
theorem path_length_le {V : Type*} [Quiver V] (h : V → ℕ)
    (hh : ∀ {a b : V}, (a ⟶ b) → h a < h b) {a b : V} (p : Quiver.Path a b) :
    h a + p.length ≤ h b := by
  sorry
-- @endregion

-- @region ex.path_algebras.lin_a_length
-- @solution Lumenary.PathAlgebras.lin_a_length
/-- Every path from `i` to `j` in the linear quiver `Aₙ` has length `j - i`.
Hint: the same induction; an arrow `e : b ⟶ c` carries the proof `e.down : c.val = b.val + 1`. -/
theorem lin_a_length {n : ℕ} {i j : LinA n} (p : Quiver.Path i j) :
    (i : Fin n).val + p.length = (j : Fin n).val := by
  sorry
-- @endregion

end LumenaryExercises.PathAlgebras
