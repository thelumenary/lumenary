/-
The Lumenary — Lean exercises: Computational reproducibility.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/ComputationalReproducibility.lean`.
-/
import Lumenary.ComputationalReproducibility

namespace LumenaryExercises.ComputationalReproducibility

open Lumenary.ComputationalReproducibility

-- @region ex.computational_reproducibility.add_mem
-- @solution Lumenary.ComputationalReproducibility.Ival.add_mem
/-- Interval addition is sound: if `x ∈ I` and `y ∈ J` then `x + y ∈ I + J`.
Hint: destructure the two memberships, unfold `Ival.Mem` and `Ival.add` with `simp only`
(you will need `Rat.cast_add`), then finish each inequality with `linarith`. -/
theorem add_mem {I J : Ival} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x + y) := by
  sorry
-- @endregion

-- @region ex.computational_reproducibility.gcd_certificate
-- @solution Lumenary.ComputationalReproducibility.gcd_certificate
/-- A Bézout identity certifies a gcd.
Hint: show `d ∣ gcd a b` (`Int.dvd_coe_gcd`) and `gcd a b ∣ d` (rewrite `d` as `a * x + b * y`),
then use `Int.dvd_antisymm`. -/
theorem gcd_certificate {a b d x y : ℤ} (hd : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hbez : a * x + b * y = d) : d = Int.gcd a b := by
  sorry
-- @endregion

end LumenaryExercises.ComputationalReproducibility
