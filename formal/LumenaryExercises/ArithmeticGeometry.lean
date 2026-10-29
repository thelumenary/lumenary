/-
The Lumenary — Lean exercises: Arithmetic geometry and elliptic curves.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ArithmeticGeometry.lean`.
-/
import Lumenary.ArithmeticGeometry

namespace LumenaryExercises.ArithmeticGeometry

-- @region ex.arithmetic_geometry.tangent_third_point
-- @solution Lumenary.ArithmeticGeometry.tangent_third_point
/-- The tangent construction: if `ℓ` is the tangent slope at `(x₁, y₁)` on `y² = x³ + ax + b`,
the third intersection point `(ℓ² − 2x₁, ℓ(x₃ − x₁) + y₁)` is on the curve.
Hint: copy the strategy of `chord_third_point` — solve the two hypotheses for `a` and `b`
(`linear_combination` does this), rewrite, and finish with `ring`. -/
theorem tangent_third_point {F : Type*} [Field F] {a b x₁ y₁ ℓ : F}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (hℓ : 2 * y₁ * ℓ = 3 * x₁ ^ 2 + a) :
    (ℓ * ((ℓ ^ 2 - 2 * x₁) - x₁) + y₁) ^ 2 =
      (ℓ ^ 2 - 2 * x₁) ^ 3 + a * (ℓ ^ 2 - 2 * x₁) + b := by
  sorry
-- @endregion

-- @region ex.arithmetic_geometry.curve_37a_discriminant
-- @solution Lumenary.ArithmeticGeometry.curve_37a_discriminant
/-- Show that the discriminant of `y² + y = x³ − x` is `37`.
Hint: `simp only [curve37a, WeierstrassCurve.Δ, WeierstrassCurve.b₂, …]`, then `norm_num`. -/
theorem curve_37a_discriminant : Lumenary.ArithmeticGeometry.curve37a.Δ = 37 := by
  sorry
-- @endregion

end LumenaryExercises.ArithmeticGeometry
