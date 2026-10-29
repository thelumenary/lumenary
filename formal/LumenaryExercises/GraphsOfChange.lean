/-
The Lumenary — Lean exercises: Graphs of change.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/GraphsOfChange.lean`.
-/
import Lumenary.GraphsOfChange

namespace LumenaryExercises.GraphsOfChange

open Lumenary.GraphsOfChange

-- @region ex.graphs_of_change.avg_rate_const
-- @solution Lumenary.GraphsOfChange.avg_rate_const
/-- A quantity that never changes has average rate of change `0`.
Hint: `unfold avgRate`, then `k − k = 0` (`Rat.sub_self`), and `0 / x = 0 * x⁻¹ = 0`
(`Rat.div_def`, `Rat.zero_mul`). -/
theorem avg_rate_const (k a b : Rat) : avgRate (fun _ => k) a b = 0 := by
  sorry
-- @endregion

-- @region ex.graphs_of_change.round_trip_example
-- @solution Lumenary.GraphsOfChange.round_trip_example
/-- `60` km at `30` km/h and `60` km back at `60` km/h: the average speed is `40` km/h.
Hint: first work out the two times by hand. Then `grind` can check the arithmetic with
fractions. -/
theorem round_trip_example : (60 + 60 : Rat) / (60 / 30 + 60 / 60) = 40 := by
  sorry
-- @endregion

end LumenaryExercises.GraphsOfChange
