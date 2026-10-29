/-
The Lumenary — Lean exercises: Algebraic number theory (units of quadratic rings).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AlgebraicNumberTheory.lean`.
-/
import Lumenary.AlgebraicNumberTheory

namespace LumenaryExercises.AlgebraicNumberTheory

-- @region ex.algebraic_number_theory.one_add_sqrt_two_unit
-- @solution Lumenary.AlgebraicNumberTheory.one_add_sqrt_two_unit
/-- `1 + √2` is a unit of `ℤ[√2]`.
Hint: its inverse is `-1 + √2`, i.e. `⟨-1, 1⟩`. Use `IsUnit.of_mul_eq_one` and check the
product coordinate by coordinate with `ext` and `simp [Zsqrtd.re_mul, Zsqrtd.im_mul]`. -/
theorem one_add_sqrt_two_unit : IsUnit (⟨1, 1⟩ : ℤ√2) := by
  sorry
-- @endregion

-- @region ex.algebraic_number_theory.norm_ne_two
-- @solution Lumenary.AlgebraicNumberTheory.norm_ne_two
/-- No element of `ℤ[√−5]` has norm `2`.
Hint: rewrite with `Lumenary.AlgebraicNumberTheory.norm_sqrt_neg_five`, show the imaginary
part is `0` with `nlinarith`, then bound the real part and use `interval_cases`. -/
theorem norm_ne_two (z : ℤ√(-5)) : z.norm ≠ 2 := by
  sorry
-- @endregion

end LumenaryExercises.AlgebraicNumberTheory
