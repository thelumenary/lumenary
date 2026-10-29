/-
The Lumenary — Lean exercises: Homotopy and the fundamental group.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FundamentalGroup.lean`.
-/
import Lumenary.FundamentalGroup

namespace LumenaryExercises.FundamentalGroup

-- @region ex.fundamental_group.brouwer_interval
-- @solution Lumenary.FundamentalGroup.brouwer_interval
/-- Prove the one-dimensional Brouwer fixed-point theorem.
Hint: apply `intermediate_value_Icc'` to `g x = f x - x` on `[0, 1]`; it says that `g` takes
every value between `g 1` and `g 0`. `ContinuousOn.sub` and `continuousOn_id` give continuity. -/
theorem brouwer_interval (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hmaps : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = x := by
  sorry
-- @endregion

-- @region ex.fundamental_group.loop_nullhomotopic
-- @solution Lumenary.FundamentalGroup.loop_nullhomotopic
/-- Prove that every loop in a real normed space is null-homotopic.
Hint: `Lumenary.FundamentalGroup.straightLineHomotopy γ (Path.refl x)` is a homotopy, and
`Path.Homotopic` means `Nonempty (Path.Homotopy _ _)`. -/
theorem loop_nullhomotopic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (γ : Path x x) : γ.Homotopic (Path.refl x) := by
  sorry
-- @endregion

end LumenaryExercises.FundamentalGroup
