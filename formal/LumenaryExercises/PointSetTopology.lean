/-
The Lumenary — Lean exercises: Metric spaces and point-set topology.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/PointSetTopology.lean`.
-/
import Lumenary.PointSetTopology

namespace LumenaryExercises.PointSetTopology

-- @region ex.point_set_topology.is_preconnected_image
-- @solution Lumenary.PointSetTopology.isPreconnected_image
/-- Prove that the continuous image of a connected set is connected.
Hint: start with `intro u v hu hv hcover ⟨_, ⟨x, hx, rfl⟩, hxu⟩ ⟨_, ⟨y, hy, rfl⟩, hyv⟩` and apply
`hs` to the preimages `f ⁻¹' u` and `f ⁻¹' v`, which are open by `IsOpen.preimage`. -/
theorem isPreconnected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsPreconnected s) {f : X → Y} (hf : Continuous f) :
    IsPreconnected (f '' s) := by
  sorry
-- @endregion

-- @region ex.point_set_topology.rat_not_preconnected
-- @solution Lumenary.PointSetTopology.rat_not_preconnected
/-- Prove that `ℚ` is not connected, using the clopen set
`Lumenary.PointSetTopology.rat_clopen : IsClopen {x : ℚ | x * x < 2}`.
Hint: `isClopen_iff` says that in a connected space a clopen set is `∅` or `Set.univ`. -/
theorem rat_not_preconnected : ¬ PreconnectedSpace ℚ := by
  sorry
-- @endregion

end LumenaryExercises.PointSetTopology
