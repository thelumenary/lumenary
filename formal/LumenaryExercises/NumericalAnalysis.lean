/-
The Lumenary — Lean exercises: Numerical analysis.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/NumericalAnalysis.lean`.
-/
import Lumenary.NumericalAnalysis

namespace LumenaryExercises.NumericalAnalysis

-- @region ex.numerical_analysis.explicit_euler_iterate
-- @solution Lumenary.NumericalAnalysis.explicit_euler_iterate
/-- Show that `n` steps of explicit Euler for `y' = λ y` multiply the initial value by
`(1 + hλ)ⁿ`.
Hint: induction on `n`; rewrite with `Function.iterate_succ_apply'` and the induction hypothesis,
then `ring`. -/
theorem explicit_euler_iterate (h lam y₀ : ℝ) (n : ℕ) :
    (fun y => y + h * (lam * y))^[n] y₀ = (1 + h * lam) ^ n * y₀ := by
  sorry
-- @endregion

-- @region ex.numerical_analysis.backward_euler_contracts
-- @solution Lumenary.NumericalAnalysis.backward_euler_contracts
/-- Show that the backward Euler factor `1 / (1 - hλ)` lies in `(0, 1)` whenever `h > 0` and
`λ < 0`.
Hint: first prove `1 < 1 - h * lam` (`nlinarith`), then use `positivity` and `div_lt_one`. -/
theorem backward_euler_contracts {h lam : ℝ} (hh : 0 < h) (hlam : lam < 0) :
    0 < 1 / (1 - h * lam) ∧ 1 / (1 - h * lam) < 1 := by
  sorry
-- @endregion

end LumenaryExercises.NumericalAnalysis
