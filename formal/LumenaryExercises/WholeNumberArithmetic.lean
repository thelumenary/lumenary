/-
The Lumenary — Lean exercises: Whole-number arithmetic.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/WholeNumberArithmetic.lean`.
-/
import Lumenary.WholeNumberArithmetic

namespace LumenaryExercises.WholeNumberArithmetic

-- @region ex.whole_number_arithmetic.area_model
-- @solution Lumenary.WholeNumberArithmetic.area_model
/-- Prove the area model: `(a + b) × (c + d)` is the sum of four partial products.
Hint: `Nat.add_mul` splits the first factor, `Nat.mul_add` splits the second,
and `Nat.add_assoc` regroups the sum. -/
theorem area_model (a b c d : Nat) :
    (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
-- @endregion

-- @region ex.whole_number_arithmetic.no_division_by_zero
-- @solution Lumenary.WholeNumberArithmetic.no_division_by_zero
/-- Show that no number `q` satisfies `q × 0 = 5`.
Hint: after `intro ⟨q, hq⟩`, rewrite `hq` with `Nat.mul_zero`. -/
theorem no_division_by_zero : ¬ ∃ q : Nat, q * 0 = 5 := by
  sorry
-- @endregion

end LumenaryExercises.WholeNumberArithmetic
