/-
The Lumenary — Lean exercises: Divisibility, Euclid's algorithm and unique factorisation.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/DivisibilityGcd.lean`.
-/
import Lumenary.DivisibilityGcd

namespace LumenaryExercises.DivisibilityGcd

-- @region ex.divisibility_gcd.dvd_linear_combination
-- @solution Lumenary.DivisibilityGcd.dvd_linear_combination
/-- A common divisor of `a` and `b` divides every combination `a * x + b * y`.
Hint: `obtain ⟨k, rfl⟩ := ha`, `obtain ⟨l, rfl⟩ := hb`, then give the witness `k * x + l * y`
and finish with `ring`. -/
theorem dvd_linear_combination {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) (x y : ℤ) :
    d ∣ a * x + b * y := by
  sorry
-- @endregion

-- @region ex.divisibility_gcd.four_counterexample
-- @solution Lumenary.DivisibilityGcd.four_counterexample
/-- Euclid's lemma needs primality: `4` divides `2 * 2` but not `2`.
Hint: this is a finite check — `decide` can do it. -/
theorem four_counterexample : 4 ∣ 2 * 2 ∧ ¬ 4 ∣ 2 := by
  sorry
-- @endregion

end LumenaryExercises.DivisibilityGcd
