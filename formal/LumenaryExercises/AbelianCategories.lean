/-
The Lumenary — Lean exercises: Abelian categories (the free abelian group counterexample).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AbelianCategories.lean`.
-/
import Lumenary.AbelianCategories

namespace LumenaryExercises.AbelianCategories

-- @region ex.abelian_categories.two_mul_not_surjective
-- @solution Lumenary.AbelianCategories.two_mul_not_surjective
/-- Multiplication by `2` on `ℤ` is not surjective.
Hint: assume a preimage `n` of `1`, simplify the hypothesis (`simp only at hn`) and use `omega`. -/
theorem two_mul_not_surjective : ¬ Function.Surjective (fun n : ℤ => 2 * n) := by
  sorry
-- @endregion

end LumenaryExercises.AbelianCategories
