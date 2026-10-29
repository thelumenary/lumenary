/-
The Lumenary — Lean exercises: Random structures.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RandomGeometry.lean`.
-/
import Lumenary.RandomGeometry

namespace LumenaryExercises.RandomGeometry

open Lumenary.RandomGeometry

-- @region ex.random_geometry.rot_injective
-- @solution Lumenary.RandomGeometry.rot_injective
/-- Show that the rotation `(x, y) ↦ (x + y, x − y)` is injective.
Hint: `intro u v h`, unfold with `simp only [rot, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
Prod.mk.injEq] at h`, then `ext <;> omega`. -/
theorem rot_injective : Function.Injective rot := by
  sorry
-- @endregion

end LumenaryExercises.RandomGeometry
