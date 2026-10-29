/-
The Lumenary — Lean exercises: Algebraic topology.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AlgebraicTopology.lean`.
-/
import Lumenary.AlgebraicTopology

namespace LumenaryExercises.AlgebraicTopology

open Lumenary.AlgebraicTopology

-- @region ex.algebraic_topology.boundary_is_cycle
-- @solution Lumenary.AlgebraicTopology.boundary_isCycle
/-- Prove that every boundary is a cycle.
Hint: write the boundary as `K.d n y` with `obtain ⟨y, rfl⟩ := hz`, then split into the cases
`n = 0` (every `0`-chain is a cycle: `trivial`) and `n = m + 1` (use `K.d_d m y`). -/
theorem boundary_isCycle (K : ChainCx) (n : ℕ) (z : K.C n) (hz : IsBoundary K n z) :
    IsCycle K n z := by
  sorry
-- @endregion

-- @region ex.algebraic_topology.chain_map_boundary
-- @solution Lumenary.AlgebraicTopology.chainMap_boundary
/-- Prove that a chain map sends boundaries to boundaries.
Hint: if `z = d y` then `f z = f (d y) = d (f y)`; the last step is `φ.comm`. -/
theorem chainMap_boundary {K L : ChainCx} (φ : ChainMap K L) (n : ℕ) (z : K.C n)
    (hz : IsBoundary K n z) : IsBoundary L n (φ.f n z) := by
  sorry
-- @endregion

end LumenaryExercises.AlgebraicTopology
