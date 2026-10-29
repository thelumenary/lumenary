/-
The Lumenary — Lean exercises: Non-Euclidean geometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/NonEuclideanGeometry.lean`.
-/
import Lumenary.NonEuclideanGeometry

namespace LumenaryExercises.NonEuclideanGeometry

open Matrix

-- @region ex.non_euclidean_geometry.girard_bookkeeping
-- @solution Lumenary.NonEuclideanGeometry.girard_bookkeeping
/-- The last step of Girard's theorem: from the lune count
`2(2αR² + 2βR² + 2γR²) = 4πR² + 4Δ`, deduce `Δ = R²(α + β + γ - π)`.
Hint: the hypothesis is linear in `Δ`. -/
theorem girard_bookkeeping {R α β γ Δ : ℝ}
    (hcover : 2 * (2 * α * R ^ 2 + 2 * β * R ^ 2 + 2 * γ * R ^ 2) =
      4 * Real.pi * R ^ 2 + 4 * Δ) :
    Δ = R ^ 2 * (α + β + γ - Real.pi) := by
  sorry
-- @endregion

-- @region ex.non_euclidean_geometry.spherical_law_of_cosines
-- @solution Lumenary.NonEuclideanGeometry.spherical_law_of_cosines
/-- The spherical law of cosines. Hint: start from
`Lumenary.NonEuclideanGeometry.normals_dot A B C hC`, rewrite with the four hypotheses, and
finish with `linarith`. -/
theorem spherical_law_of_cosines (A B C : Fin 3 → ℝ) (hC : C ⬝ᵥ C = 1) {a b c γ : ℝ}
    (ha : Real.cos a = B ⬝ᵥ C) (hb : Real.cos b = A ⬝ᵥ C) (hc : Real.cos c = A ⬝ᵥ B)
    (hγ : (C ⨯₃ A) ⬝ᵥ (C ⨯₃ B) = Real.sin b * Real.sin a * Real.cos γ) :
    Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ := by
  sorry
-- @endregion

end LumenaryExercises.NonEuclideanGeometry
