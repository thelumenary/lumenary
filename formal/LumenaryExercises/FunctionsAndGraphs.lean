/-
The Lumenary — Lean exercises: Functions and their graphs.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/FunctionsAndGraphs.lean`.
-/
import Lumenary.FunctionsAndGraphs

namespace LumenaryExercises.FunctionsAndGraphs

-- @region ex.functions_and_graphs.inj_on_of_strict_mono_on
-- @solution Lumenary.FunctionsAndGraphs.injOn_of_strictMonoOn
/-- A strictly increasing function is injective.
Hint: after `intro x hx y hy hxy`, split into the cases `x < y`, `x = y`, `x > y` with
`rcases lt_trichotomy x y with hlt | heq | hgt`. In the first case `hf hx hy hlt : f x < f y`. -/
theorem injOn_of_strictMonoOn {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictMonoOn f s) :
    Set.InjOn f s := by
  sorry
-- @endregion

-- @region ex.functions_and_graphs.comp_not_comm
-- @solution Lumenary.FunctionsAndGraphs.comp_not_comm
/-- Composition is not commutative: squaring after adding 1 differs from adding 1 after squaring.
Hint: assume they are equal (`intro h`), evaluate both sides at `1` with `congrFun h 1`, and let
`norm_num` find the contradiction `4 = 2`. -/
theorem comp_not_comm :
    (fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => x + 1) ≠ (fun x : ℝ => x + 1) ∘ (fun x : ℝ => x ^ 2) := by
  sorry
-- @endregion

end LumenaryExercises.FunctionsAndGraphs
