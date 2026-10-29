/-
The Lumenary — Lean exercises: Constructing ℤ, ℚ and ℝ.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/NumberSystemConstructions.lean`.
-/
import Lumenary.NumberSystemConstructions

namespace LumenaryExercises.NumberSystemConstructions

-- @region ex.number_system_constructions.add_respects
-- @solution Lumenary.NumberSystemConstructions.add_respects
/-- Addition of pairs respects `(a, b) ~ (c, d) ⟺ a + d = c + b`.
Hint: regroup with `ring` and rewrite with both hypotheses, or simply use `omega`. -/
theorem add_respects {a b c d a' b' c' d' : ℕ} (h₁ : a + b' = a' + b) (h₂ : c + d' = c' + d) :
    (a + c) + (b' + d') = (a' + c') + (b + d) := by
  sorry
-- @endregion

-- @region ex.number_system_constructions.frac_trans
-- @solution Lumenary.NumberSystemConstructions.frac_trans
/-- Equality of fractions is transitive when there are no zero divisors.
Hint: prove `(a * f) * d = (e * b) * d` with a `calc`, then cancel with `mul_right_cancel₀`. -/
theorem frac_trans {R : Type*} [CommRing R] [NoZeroDivisors R] {a b c d e f : R} (hd : d ≠ 0)
    (h₁ : a * d = c * b) (h₂ : c * f = e * d) : a * f = e * b := by
  sorry
-- @endregion

end LumenaryExercises.NumberSystemConstructions
