/-
The Lumenary — Lean exercises: Congruences.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Congruences.lean`.
-/
import Lumenary.Congruences

namespace LumenaryExercises.Congruences

open Lumenary.Congruences

-- @region ex.congruences.mod_eq_mul
-- @solution Lumenary.Congruences.modEq_mul
/-- Congruences can be multiplied.
Hint: rewrite with `modEq_iff_dvd_sub`, use `a * c - b * d = a * (c - d) + d * (a - b)`
(proved by `ring`), then `dvd_add` and `dvd_mul_of_dvd_right`. -/
theorem modEq_mul {n a b c d : ℤ} (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  sorry
-- @endregion

-- @region ex.congruences.crt_unique
-- @solution Lumenary.Congruences.crt_unique
/-- Uniqueness in the Chinese remainder theorem.
Hint: `IsCoprime.mul_dvd` combines `m ∣ x - y` and `n ∣ x - y`. -/
theorem crt_unique {m n x y : ℤ} (h : IsCoprime m n) (hm : x ≡ y [ZMOD m])
    (hn : x ≡ y [ZMOD n]) : x ≡ y [ZMOD m * n] := by
  sorry
-- @endregion

end LumenaryExercises.Congruences
