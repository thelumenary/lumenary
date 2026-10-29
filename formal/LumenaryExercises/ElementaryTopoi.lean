/-
The Lumenary — Lean exercises: Elementary topos theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ElementaryTopoi.lean`.
-/
import Lumenary.ElementaryTopoi

namespace LumenaryExercises.ElementaryTopoi

open Lumenary.ElementaryTopoi

-- @region ex.elementary_topoi.chi_unique
-- @solution Lumenary.ElementaryTopoi.chi_unique
/-- **Uniqueness of characteristic maps.** If pulling `true` back along `φ` gives `S`, then `φ`
is the characteristic map of `S`.
Hint: rewrite the goal backwards with `h`, then use `chi_pullbackTrue`. -/
theorem chi_unique {A : Psh} (S : Sub A) (φ : Hom A Omega) (h : pullbackTrue φ = S) :
    φ = chi S := by
  sorry
-- @endregion

-- @region ex.elementary_topoi.le_himp_iff
-- @solution Lumenary.ElementaryTopoi.Sub.le_himp_iff
/-- **Residuation** for subpresheaves: `U ≤ (S ⇒ T) ↔ U ⊓ S ≤ T`.
Hint: `≤` is a pair of inclusions (stage 1, stage 0). For `←` at stage 1 you need that `U` is
closed under restriction: `U.closed x hx : A.res x ∈ U.S0`. -/
theorem le_himp_iff {A : Psh} (U S T : Sub A) : U ≤ Sub.himp S T ↔ U ⊓ S ≤ T := by
  sorry
-- @endregion

end LumenaryExercises.ElementaryTopoi
