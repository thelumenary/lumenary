/-
The Lumenary — Lean exercises: Projective geometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProjectiveGeometry.lean`.
-/
import Lumenary.ProjectiveGeometry

namespace LumenaryExercises.ProjectiveGeometry

open Matrix

-- @region ex.projective_geometry.mk_neg
-- @solution Lumenary.ProjectiveGeometry.mk_neg
/-- A vector and its negative are the same projective point.
Hint: rewrite with `Projectivization.mk_eq_mk_iff` and supply the unit `-1`. -/
theorem mk_neg {K : Type*} [Field K] (v : Fin 3 → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K (-v) (neg_ne_zero.mpr hv) := by
  sorry
-- @endregion

-- @region ex.projective_geometry.incident_cross_zero
-- @solution Lumenary.ProjectiveGeometry.incident_cross_zero
/-- A line through `p` and `q` is parallel to `p ⨯₃ q`.
Hint: `cross_cross_eq_smul_sub_smul'` expands `ℓ ⨯₃ (p ⨯₃ q)`; then use `dotProduct_comm`. -/
theorem incident_cross_zero {K : Type*} [CommRing K] (ℓ p q : Fin 3 → K) (hp : ℓ ⬝ᵥ p = 0)
    (hq : ℓ ⬝ᵥ q = 0) : ℓ ⨯₃ (p ⨯₃ q) = 0 := by
  sorry
-- @endregion

end LumenaryExercises.ProjectiveGeometry
