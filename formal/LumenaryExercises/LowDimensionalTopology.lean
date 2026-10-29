/-
The Lumenary — Lean exercises: Low-dimensional topology.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LowDimensionalTopology.lean`.
-/
import Lumenary.LowDimensionalTopology

namespace LumenaryExercises.LowDimensionalTopology

open Lumenary.LowDimensionalTopology

-- @region ex.low_dimensional_topology.lens_five_four
-- @solution Lumenary.LowDimensionalTopology.lens_five_four
/-- Show that the residues `1` and `4` modulo 5 satisfy the Reidemeister–Brody relation, so
`L(5, 1)` and `L(5, 4)` are homeomorphic.
Hint: unfold `LensHomeoRel`; the statement is about the four units of `ZMod 5`, so `decide`
can check it. Which of the four cases holds? -/
theorem lens_five_four : LensHomeoRel (p := 5) 1 (ZMod.unitOfCoprime 4 (by norm_num)) := by
  sorry
-- @endregion

-- @region ex.low_dimensional_topology.lens_homotopy_of_homeo
-- @solution Lumenary.LowDimensionalTopology.lensHomotopyRel_of_lensHomeoRel
/-- Show that the homeomorphism criterion implies the homotopy criterion.
Hint: split into the four cases `q' = q`, `q' = -q`, `q' = q⁻¹`, `q' = -q⁻¹` and rewrite. The
witness `n` is `q` in the first two cases and `1` in the last two. -/
theorem lensHomotopyRel_of_lensHomeoRel {p : ℕ} {q q' : (ZMod p)ˣ} (h : LensHomeoRel q q') :
    LensHomotopyRel q q' := by
  sorry
-- @endregion

end LumenaryExercises.LowDimensionalTopology
