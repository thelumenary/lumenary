/-
The Lumenary — Lean exercises: Symplectic geometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/SymplecticGeometry.lean`.
-/
import Lumenary.SymplecticGeometry

namespace LumenaryExercises.SymplecticGeometry

open Matrix Lumenary.SymplecticGeometry

-- @region ex.symplectic_geometry.shear_symplectic
-- @solution Lumenary.SymplecticGeometry.shear_symplectic
/-- Show that the shear `(q, p) ↦ (q + t p, p)` is symplectic.
Hint: rewrite with `symplectic_iff_det_eq_one`, then compute the determinant with
`Matrix.det_fin_two_of`. -/
theorem shear_symplectic (t : ℝ) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * J2 * !![1, t; 0, 1] = J2 := by
  sorry
-- @endregion

end LumenaryExercises.SymplecticGeometry
