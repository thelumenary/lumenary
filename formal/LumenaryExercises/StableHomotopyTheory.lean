/-
The Lumenary — Lean exercises: Stable homotopy theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/StableHomotopyTheory.lean`.
-/
import Lumenary.StableHomotopyTheory

namespace LumenaryExercises.StableHomotopyTheory

open Lumenary.StableHomotopyTheory

-- @region ex.stable_homotopy_theory.one_add_mul_fgl
-- @solution Lumenary.StableHomotopyTheory.one_add_mulFGL
/-- Show that the multiplicative formal group law is multiplication in disguise:
`1 + F(x, y) = (1 + x)(1 + y)`.
Hint: unfold `mulFGL` with `simp only [mulFGL]` and finish with `ring`. -/
theorem one_add_mulFGL {A : Type*} [CommRing A] (x y : A) :
    1 + mulFGL x y = (1 + x) * (1 + y) := by
  sorry
-- @endregion

-- @region ex.stable_homotopy_theory.rp_even_top_sw
-- @solution Lumenary.StableHomotopyTheory.rp_even_top_sw
/-- Show that `C(2m + 1, 2m)` is odd, so the top Stiefel–Whitney number of `ℝP²ᵐ` is non-zero.
Hint: `Nat.choose_succ_self_right` says `C(n + 1, n) = n + 1`; then `omega`. -/
theorem rp_even_top_sw (m : ℕ) : ¬ 2 ∣ Nat.choose (2 * m + 1) (2 * m) := by
  sorry
-- @endregion

end LumenaryExercises.StableHomotopyTheory
