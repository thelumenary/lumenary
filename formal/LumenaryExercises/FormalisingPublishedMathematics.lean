/-
The Lumenary — Lean exercises: formalising published mathematics.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/FormalisingPublishedMathematics.lean`.
-/
import Lumenary.FormalisingPublishedMathematics

namespace LumenaryExercises.FormalisingPublishedMathematics

open Lumenary.FormalisingPublishedMathematics

-- @region ex.formalising_published_mathematics.zagier_map_eq_one
-- @solution Lumenary.FormalisingPublishedMathematics.zagierMap_eq_one
/-- Blueprint lemma: the first case of Zagier's map preserves `x² + 4yz`.
Hint: write `y = x + z + d` with `obtain ⟨d, rfl⟩ : ∃ d, y = x + z + d := ⟨y - (x + z), by omega⟩`,
simplify the truncated subtraction `x + z + d - x - z` to `d` with `omega`, and finish with
`ring`. -/
theorem zagierMap_eq_one {x y z : ℕ} (h : x + z < y) :
    (x + 2 * z) ^ 2 + 4 * z * (y - x - z) = x ^ 2 + 4 * y * z := by
  sorry
-- @endregion

-- @region ex.formalising_published_mathematics.prime_one_mod_four
-- @solution Lumenary.FormalisingPublishedMathematics.prime_one_mod_four
/-- Check the formal statement against the published one: deduce "every prime `p ≡ 1 (mod 4)` is
a sum of two squares" from `zagier_two_squares`, which is stated for `p = 4k + 1`.
Hint: take `k = p / 4`; `omega` proves `4 * (p / 4) + 1 = p` from `p % 4 = 1`. -/
theorem prime_one_mod_four {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  sorry
-- @endregion

-- @region ex.formalising_published_mathematics.primality_needed
-- @solution Lumenary.FormalisingPublishedMathematics.primality_needed
/-- Show that the hypothesis "p is prime" cannot be dropped: for `21 = 4·5 + 1` Zagier's map has
two fixed points, and `21` is not a sum of two squares.
Hint: `decide` evaluates `zagierMap` on explicit triples. For the last part, bound `a` and `b`
with `nlinarith`, then use `interval_cases`. -/
theorem primality_needed :
    (1 ^ 2 + 4 * 1 * 5 = 21 ∧ zagierMap (1, 1, 5) = (1, 1, 5)) ∧
    (3 ^ 2 + 4 * 3 * 1 = 21 ∧ zagierMap (3, 3, 1) = (3, 3, 1)) ∧
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 21 := by
  sorry
-- @endregion

end LumenaryExercises.FormalisingPublishedMathematics
