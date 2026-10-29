/-
The Lumenary — Lean exercises: Algebraic geometry (the cusp and the Zariski topology).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AlgebraicGeometry.lean`.
-/
import Lumenary.AlgebraicGeometry

namespace LumenaryExercises.AlgebraicGeometry

open Polynomial

-- @region ex.algebraic_geometry.cusp_param_injective
-- @solution Lumenary.AlgebraicGeometry.cusp_param_injective
/-- The parametrisation `t ↦ (t², t³)` of the cusp `y² = x³` is injective.
Hint: split on `s = 0` (then `t ^ 2 = 0`, and `pow_eq_zero_iff` finishes); otherwise write
`s = s ^ 3 / s ^ 2` and use `field_simp` in a `calc` block. -/
theorem cusp_param_injective {k : Type*} [Field k] {s t : k} (h2 : s ^ 2 = t ^ 2)
    (h3 : s ^ 3 = t ^ 3) : s = t := by
  sorry
-- @endregion

-- @region ex.algebraic_geometry.basic_opens_meet
-- @solution Lumenary.AlgebraicGeometry.basic_opens_meet
/-- Over an infinite field, two non-empty basic open sets of the affine line meet.
Hint: the product `f * g` is non-zero, so its roots form a finite set
(`(f * g).roots.toFinset`); `Infinite.exists_notMem_finset` gives a point outside it, and
`Polynomial.eval_mul` splits the value. Start with `classical`. -/
theorem basic_opens_meet {k : Type*} [Field k] [Infinite k] {f g : k[X]} (hf : f ≠ 0)
    (hg : g ≠ 0) : ∃ a : k, f.eval a ≠ 0 ∧ g.eval a ≠ 0 := by
  sorry
-- @endregion

end LumenaryExercises.AlgebraicGeometry
