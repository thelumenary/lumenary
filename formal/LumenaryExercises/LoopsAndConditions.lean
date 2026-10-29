/-
The Lumenary — Lean exercises: Repetition and decisions.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/LoopsAndConditions.lean`.
-/
import Lumenary.LoopsAndConditions

namespace LumenaryExercises.LoopsAndConditions

open Lumenary.LoopsAndConditions

-- @region ex.loops_and_conditions.square_returns
-- @solution Lumenary.LoopsAndConditions.square_returns
/-- Show that the loop "repeat 4 times: forward, turn right" brings the robot home.
Hint: Lean can follow the whole program itself — try `decide`. -/
theorem square_returns : run home (repeatBlock 4 [.forward, .turnRight]) = home := by
  sorry
-- @endregion

-- @region ex.loops_and_conditions.carry_le_one
-- @solution Lumenary.LoopsAndConditions.carry_le_one
/-- Show that the carry in column addition is never more than 1.
Hint: the biggest possible column total is 9 + 9 + 1 = 19. The tactic `omega` can finish. -/
theorem carry_le_one (a b c : Nat) (ha : a ≤ 9) (hb : b ≤ 9) (hc : c ≤ 1) :
    (a + b + c) / 10 ≤ 1 := by
  sorry
-- @endregion

-- @region ex.loops_and_conditions.odd_minus_twos
-- @solution Lumenary.LoopsAndConditions.odd_minus_twos
/-- Show that starting at 9 and taking away 2 again and again never gives exactly 0.
Hint: `9 - 2 * k` is always odd. `omega` knows about odd and even numbers. -/
theorem odd_minus_twos (k : Nat) : (9 : Int) - 2 * k ≠ 0 := by
  sorry
-- @endregion

end LumenaryExercises.LoopsAndConditions
