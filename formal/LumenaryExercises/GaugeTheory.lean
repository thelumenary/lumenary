/-
The Lumenary — Lean exercises: Gauge theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/GaugeTheory.lean`.
-/
import Lumenary.GaugeTheory

namespace LumenaryExercises.GaugeTheory

open Lumenary.GaugeTheory

-- @region ex.gauge_theory.holonomy_loop_abelian
-- @solution Lumenary.GaugeTheory.holonomy_loop_abelian
/-- For a commutative structure group, holonomies of closed loops are gauge invariant.
Hint: rewrite with `holonomy_gauge` and the hypothesis `hp`; then the factors `g x` and
`(g x)⁻¹` commute past the holonomy and cancel (`mul_comm`, `mul_assoc`, `mul_inv_cancel`). -/
theorem holonomy_loop_abelian {G : Type*} [CommGroup G] (g : ℤ × ℤ → G)
    (A : LatticeConnection G) (x : ℤ × ℤ) (p : List Step) (hp : endpoint x p = x) :
    holonomy (gauge g A) x p = holonomy A x p := by
  sorry
-- @endregion

end LumenaryExercises.GaugeTheory
