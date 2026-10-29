/-
The Lumenary — Lean exercises: Classical mechanics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ClassicalMechanics.lean`.
-/
import Lumenary.ClassicalMechanics

namespace LumenaryExercises.ClassicalMechanics

open Real Matrix

-- @region ex.classical_mechanics.motion_in_plane
-- @solution Lumenary.ClassicalMechanics.motion_in_plane
/-- Under a central force the motion stays in the plane perpendicular to `L = r(0) × v(0)`.
Hint: rewrite with `Lumenary.ClassicalMechanics.angular_momentum_conserved hr hv 0 t`, then use
`dot_self_cross`. -/
theorem motion_in_plane {r v : ℝ → Fin 3 → ℝ} {k : ℝ → ℝ}
    (hr : ∀ t, HasDerivAt r (v t) t) (hv : ∀ t, HasDerivAt v (k t • r t) t) (t : ℝ) :
    r t ⬝ᵥ (r 0 ⨯₃ v 0) = 0 := by
  sorry
-- @endregion

-- @region ex.classical_mechanics.orbit_is_conic
-- @solution Lumenary.ClassicalMechanics.orbit_is_conic
/-- A point on the orbit `r (1 + e cos θ) = p` lies on a conic.
Hint: `r = p - e x` where `x = r cos θ`, and `x² + y² = r²` by `sin_sq_add_cos_sq`. -/
theorem orbit_is_conic {r θ e p : ℝ} (horbit : r * (1 + e * cos θ) = p) :
    (1 - e ^ 2) * (r * cos θ) ^ 2 + 2 * p * e * (r * cos θ) + (r * sin θ) ^ 2 = p ^ 2 := by
  sorry
-- @endregion

end LumenaryExercises.ClassicalMechanics
