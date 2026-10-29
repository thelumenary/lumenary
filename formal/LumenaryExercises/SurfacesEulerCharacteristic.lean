/-
The Lumenary — Lean exercises: Surfaces, polyhedra and the Euler characteristic.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/SurfacesEulerCharacteristic.lean`.
-/
import Lumenary.SurfacesEulerCharacteristic

namespace LumenaryExercises.SurfacesEulerCharacteristic

-- @region ex.surfaces_euler_characteristic.twelve_pentagons
-- @solution Lumenary.SurfacesEulerCharacteristic.twelve_pentagons
/-- A polyhedron made of `P` pentagons and `H` hexagons, three at each vertex, has twelve
pentagons. Hint: all three hypotheses are linear, so a single tactic for linear arithmetic over
the natural numbers finishes the job. Which one? -/
theorem twelve_pentagons (P H V E : ℕ) (hfaces : 5 * P + 6 * H = 2 * E) (hvert : 3 * V = 2 * E)
    (hEuler : V + (P + H) = E + 2) : P = 12 := by
  sorry
-- @endregion

-- @region ex.surfaces_euler_characteristic.edge_bound
-- @solution Lumenary.SurfacesEulerCharacteristic.edge_bound
/-- A plane graph whose faces all have at least three sides satisfies `E + 6 ≤ 3V`.
Hint: multiply Euler's formula by `3` in your head; then `omega` can do the rest. -/
theorem edge_bound (V E F : ℕ) (hEuler : V + F = E + 2) (hfaces : 3 * F ≤ 2 * E) :
    E + 6 ≤ 3 * V := by
  sorry
-- @endregion

end LumenaryExercises.SurfacesEulerCharacteristic
