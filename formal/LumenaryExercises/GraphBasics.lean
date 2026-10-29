/-
The Lumenary — Lean exercises: Graphs.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/GraphBasics.lean`.
-/
import Lumenary.GraphBasics

namespace LumenaryExercises.GraphBasics

open Lumenary.GraphBasics

-- @region ex.graph_basics.euler_circuit_even
-- @solution Lumenary.GraphBasics.euler_circuit_even
/-- If a multigraph has an Euler circuit, every vertex has even degree.
Hint: write the walk as `a :: rest`; the circuit ends where it starts, so `rest.getLastD a = a`.
Then `degree_walkEdges a rest v` and `degree_perm` give
`degree G v + 2 * (if a = v then 1 else 0) = 2 * (a :: rest).count v`. -/
theorem euler_circuit_even {n : ℕ} {G : Multigraph n} {w : List (Fin n)}
    (h : IsEulerCircuit G w) (v : Fin n) : Even (degree G v) := by
  sorry
-- @endregion

end LumenaryExercises.GraphBasics
