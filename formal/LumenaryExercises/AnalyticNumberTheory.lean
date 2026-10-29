/-
The Lumenary — Lean exercises: Analytic number theory (Möbius inversion and the 3–4–1 trick).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/AnalyticNumberTheory.lean`.
-/
import Lumenary.AnalyticNumberTheory

namespace LumenaryExercises.AnalyticNumberTheory

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

-- @region ex.analytic_number_theory.three_four_one
-- @solution Lumenary.AnalyticNumberTheory.three_four_one
/-- `3 + 4 cos θ + cos 2θ ≥ 0`.
Hint: rewrite `cos (2θ)` with `Real.cos_two_mul`; the expression is then `2 (1 + cos θ)²`, so
`nlinarith [sq_nonneg (1 + Real.cos θ)]` finishes. -/
theorem three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  sorry
-- @endregion

-- @region ex.analytic_number_theory.moebius_inversion
-- @solution Lumenary.AnalyticNumberTheory.moebius_inversion
/-- Möbius inversion: if `g = f * ζ` then `f = g * μ`.
Hint: a `calc` chain `f = f * 1 = f * (ζ * μ) = (f * ζ) * μ = g * μ`, using `mul_one`,
`coe_zeta_mul_moebius` and `mul_assoc`. -/
theorem moebius_inversion (f g : ArithmeticFunction ℤ) (h : g = f * ζ) : f = g * μ := by
  sorry
-- @endregion

end LumenaryExercises.AnalyticNumberTheory
