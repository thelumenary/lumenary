/-
The Lumenary — Lean exercises: Probability.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProbabilityIntro.lean`.
-/
import Lumenary.ProbabilityIntro

namespace LumenaryExercises.ProbabilityIntro

open Lumenary.ProbabilityIntro

-- @region ex.probability_intro.prob_sum_seven
-- @solution Lumenary.ProbabilityIntro.prob_sum_seven
/-- With two dice, the probability of a sum of `7` is `1/6`.
Hint: this is a finite computation that Lean can carry out itself — try `decide +kernel`.
Then change `7` to `8` and `1 / 6` to the right answer for a sum of `8`. -/
theorem prob_sum_seven : prob twoDice (fun p => p.1 + p.2 == 7) = 1 / 6 := by
  sorry
-- @endregion

-- @region ex.probability_intro.count_compl
-- @solution Lumenary.ProbabilityIntro.count_compl
/-- Every outcome is in `A` or in "not `A`": `|A| + |not A| = |S|`.
Hint: `induction S with | nil => rfl | cons a S ih => ?_`, then `unfold count at ih ⊢` and
split into the cases `A a = true` and `A a = false` with `cases h : A a`. In each case `simp [h]`
followed by `omega` finishes. -/
theorem count_compl {α : Type} (S : List α) (A : α → Bool) :
    count S A + count S (fun x => !A x) = S.length := by
  sorry
-- @endregion

end LumenaryExercises.ProbabilityIntro
