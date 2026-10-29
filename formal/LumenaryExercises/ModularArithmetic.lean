/-
The Lumenary — Lean exercises: clock arithmetic.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ModularArithmetic.lean`.
-/
import Lumenary.ModularArithmetic

namespace LumenaryExercises.ModularArithmetic

-- @region ex.modular_arithmetic.four_no_partner_mod_ten
-- @solution Lumenary.ModularArithmetic.four_no_partner_mod_ten
/-- Show that `4` has no multiplicative partner modulo `10`.
Hint: `4` and `10` have the common factor `2`. Use
`Lumenary.ModularArithmetic.no_partner_of_common_factor (d := 2)`; each of its three side
conditions can be closed `by decide`. -/
theorem four_no_partner_mod_ten (b : Nat) : (4 * b) % 10 ≠ 1 := by
  sorry
-- @endregion

-- @region ex.modular_arithmetic.ten_pow_mod_nine
-- @solution Lumenary.ModularArithmetic.ten_pow_mod_nine
/-- Casting out nines: show that `10^k` leaves remainder `1` on division by `9`.
Hint: induction on `k`. In the step, rewrite `10^(k+1)` as `10^k * 10` (`Nat.pow_succ`), then
use `Lumenary.ModularArithmetic.mul_mod_of_division` and the induction hypothesis. -/
theorem ten_pow_mod_nine (k : Nat) : 10 ^ k % 9 = 1 := by
  sorry
-- @endregion

end LumenaryExercises.ModularArithmetic
