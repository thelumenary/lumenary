/-
The Lumenary — Lean exercises: Trigonometry.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Trigonometry.lean`.
-/
import Lumenary.Trigonometry

namespace LumenaryExercises.Trigonometry

open Real

-- @region ex.trigonometry.law_of_cosines_coord
-- @solution Lumenary.Trigonometry.law_of_cosines_coord
/-- The coordinate computation behind the law of cosines. With `C` at the origin, `B = (a, 0)`
and `A = (b cos γ, b sin γ)`, the squared distance `AB²` is `a² + b² − 2ab cos γ`.
Hint: rewrite the left side as `b² (sin² γ + cos² γ) + a² − 2ab cos γ` with `ring`, then use
`Real.sin_sq_add_cos_sq`. -/
theorem law_of_cosines_coord (a b γ : ℝ) :
    (b * cos γ - a) ^ 2 + (b * sin γ) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cos γ := by
  sorry
-- @endregion

-- @region ex.trigonometry.sin_add_ne_add
-- @solution Lumenary.Trigonometry.sin_add_ne_add
/-- Show that `sin (α + β) = sin α + sin β` is not an identity.
Hint: try `α = β = π / 2`, and use `add_halves`, `sin_pi` and `sin_pi_div_two`. -/
theorem sin_add_ne_add : ¬ ∀ α β : ℝ, sin (α + β) = sin α + sin β := by
  sorry
-- @endregion

end LumenaryExercises.Trigonometry
