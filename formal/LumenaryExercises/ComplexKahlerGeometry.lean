/-
The Lumenary — Lean exercises: Complex and Kähler geometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ComplexKahlerGeometry.lean`.
-/
import Lumenary.ComplexKahlerGeometry

namespace LumenaryExercises.ComplexKahlerGeometry

open Lumenary.ComplexKahlerGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- @region ex.complex_kahler_geometry.kahler_form_self
-- @solution Lumenary.ComplexKahlerGeometry.kahler_form_self
/-- Show that the Kähler form is alternating: `ω(u, u) = 0`.
Hint: `kahler_form_antisymm u u` says `ω(u, u) = -ω(u, u)`; finish with `linarith`. -/
theorem kahler_form_self (u : E) : kahlerForm u u = 0 := by
  sorry
-- @endregion

end LumenaryExercises.ComplexKahlerGeometry
