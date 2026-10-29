/-
The Lumenary — Lean exercises: Geometric group theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/GeometricGroupTheory.lean`.
-/
import Lumenary.GeometricGroupTheory

namespace LumenaryExercises.GeometricGroupTheory

open Lumenary.GeometricGroupTheory

-- @region ex.geometric_group_theory.isometry_is_qi_embedding
-- @solution Lumenary.GeometricGroupTheory.isometry_isQIEmbedding
/-- Show that an isometric embedding is a `(1, 0)`-quasi-isometric embedding.
Hint: `Isometry.dist_eq` rewrites `dist (f x) (f x')` to `dist x x'`; then `simp` finishes
both inequalities. -/
theorem isometry_isQIEmbedding {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Isometry f) : IsQIEmbedding f 1 0 := by
  sorry
-- @endregion

-- @region ex.geometric_group_theory.upper_ping
-- @solution Lumenary.GeometricGroupTheory.upper_ping
/-- The "ping" half of Sanov's ping-pong: a non-zero power `Aⁿ = [[1, 2n], [0, 1]]` sends a vector
with `|x| < |y|` to one with `|x'| > |y'|`.
Hint: first compute the two coordinates of `Aⁿ • v` (use `change` to see the matrix and
`simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]`), then use `Int.one_le_abs`, `abs_mul` and
the triangle inequality `abs_sub`. -/
theorem upper_ping (n : ℤ) (hn : n ≠ 0) (v : Fin 2 → ℤ) (hv : |v 0| < |v 1|) :
    |(upperHom (Multiplicative.ofAdd n) • v) 1| < |(upperHom (Multiplicative.ofAdd n) • v) 0| := by
  sorry
-- @endregion

end LumenaryExercises.GeometricGroupTheory
