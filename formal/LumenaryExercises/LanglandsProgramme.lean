/-
The Lumenary — Lean exercises: The Langlands programme.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LanglandsProgramme.lean`.
-/
import Lumenary.LanglandsProgramme

namespace LumenaryExercises.LanglandsProgramme

-- @region ex.langlands_programme.sum_two_squares_mod_four
-- @solution Lumenary.LanglandsProgramme.sum_two_squares_mod_four
/-- An odd prime that is a sum of two squares is `1` mod `4`.
Hint: show `(a ^ 2 + b ^ 2) % 4 ≠ 3` by splitting into the cases `a % 4` and `b % 4`
(`Nat.add_mod`, `Nat.pow_mod`, `interval_cases`), then finish with `omega` using that `p` is odd
(`Nat.Prime.eq_two_or_odd`). -/
theorem sum_two_squares_mod_four (p a b : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : a ^ 2 + b ^ 2 = p) : p % 4 = 1 := by
  sorry
-- @endregion

end LumenaryExercises.LanglandsProgramme
