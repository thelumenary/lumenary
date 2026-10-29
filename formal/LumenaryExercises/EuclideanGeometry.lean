/-
The Lumenary — Lean exercises: Euclidean geometry and proof.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/EuclideanGeometry.lean`.
-/
import Lumenary.EuclideanGeometry

open EuclideanGeometry
open scoped EuclideanGeometry RealInnerProductSpace

namespace LumenaryExercises.EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

-- @region ex.euclidean_geometry.thales
-- @solution Lumenary.EuclideanGeometry.thales
/-- Thales' theorem with vectors: if `‖c‖ = ‖a‖` (so `c` is on the circle with diameter from
`a` to `-a`), the two sides `a - c` and `-a - c` are perpendicular.
Hint: expand the inner product with `inner_sub_left`, `inner_sub_right`, `inner_neg_right`,
then use `real_inner_self_eq_norm_sq` and `real_inner_comm`. -/
theorem thales (a c : V) (h : ‖c‖ = ‖a‖) : ⟪a - c, -a - c⟫ = 0 := by
  sorry
-- @endregion

-- @region ex.euclidean_geometry.perp_bisectors_concurrent
-- @solution Lumenary.EuclideanGeometry.perp_bisectors_concurrent
/-- If `O` is on the perpendicular bisectors of `AB` and `BC`, it is on that of `CA`.
Hint: `AffineSubspace.mem_perpBisector_iff_dist_eq` turns each membership into an equation
between distances. -/
theorem perp_bisectors_concurrent {A B C O : P} (hAB : O ∈ AffineSubspace.perpBisector A B)
    (hBC : O ∈ AffineSubspace.perpBisector B C) : O ∈ AffineSubspace.perpBisector C A := by
  sorry
-- @endregion

end LumenaryExercises.EuclideanGeometry
