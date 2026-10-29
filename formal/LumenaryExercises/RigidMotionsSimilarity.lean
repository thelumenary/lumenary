/-
The Lumenary — Lean exercises: rigid motions, congruence and similarity.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RigidMotionsSimilarity.lean`.
-/
import Lumenary.RigidMotionsSimilarity

namespace LumenaryExercises.RigidMotionsSimilarity

open Lumenary.RigidMotionsSimilarity

-- @region ex.rigid_motions_similarity.reflect_diag_isometry
-- @solution Lumenary.RigidMotionsSimilarity.reflectDiag_isometry
/-- Show that reflection in the line `y = x` is a rigid motion.
Hint: `intro P Q`, then `unfold d2 reflectDiag`; the two squared differences are swapped, and
`grind` can finish. -/
theorem reflectDiag_isometry : IsIsometry reflectDiag := by
  sorry
-- @endregion

-- @region ex.rigid_motions_similarity.translate_undo
-- @solution Lumenary.RigidMotionsSimilarity.translate_undo
/-- Show that translating by `(a, b)` and then by `(-a, -b)` brings every point back.
Hint: `cases P`, then `simp only [translate, Point.mk.injEq]` leaves one equation per
coordinate; `constructor <;> grind` finishes. -/
theorem translate_undo (a b : Rat) (P : Point) :
    translate (-a) (-b) (translate a b P) = P := by
  sorry
-- @endregion

end LumenaryExercises.RigidMotionsSimilarity
