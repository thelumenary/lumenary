/-
The Lumenary — Lean exercises: Computational complexity.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ComplexityTheory.lean`.
-/
import Lumenary.ComplexityTheory

namespace LumenaryExercises.ComplexityTheory

-- @region ex.complexity_theory.indep_iff_cover_compl
-- @solution Lumenary.ComplexityTheory.indepSet_iff_vertexCover_compl
/-- Independent sets are exactly the complements of vertex covers.
Hint: unfold the definitions. `G.IsIndepSet s` says any two distinct vertices of `s` are
non-adjacent; `G.IsVertexCover c` says every edge has an endpoint in `c`. For `→`, argue by
contradiction; `hadj.ne` gives `v ≠ w` from `hadj : G.Adj v w`. -/
theorem indepSet_iff_vertexCover_compl {V : Type*} (G : SimpleGraph V) (s : Set V) :
    G.IsIndepSet s ↔ G.IsVertexCover sᶜ := by
  sorry
-- @endregion

-- @region ex.complexity_theory.clique_iff_indep_compl
-- @solution Lumenary.ComplexityTheory.clique_iff_indepSet_compl
/-- Cliques in `G` are independent sets in the complement graph.
Hint: `SimpleGraph.compl_adj G v w : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬ G.Adj v w`. -/
theorem clique_iff_indepSet_compl {V : Type*} (G : SimpleGraph V) (s : Set V) :
    G.IsClique s ↔ Gᶜ.IsIndepSet s := by
  sorry
-- @endregion

end LumenaryExercises.ComplexityTheory
