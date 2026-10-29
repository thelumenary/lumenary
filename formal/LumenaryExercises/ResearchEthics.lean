/-
The Lumenary — Lean exercises: research ethics and attribution.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ResearchEthics.lean`.
-/
import Lumenary.ResearchEthics

namespace LumenaryExercises.ResearchEthics

open Lumenary.ResearchEthics

-- @region ex.research_ethics.euler_conjecture_false
-- @solution Lumenary.ResearchEthics.euler_conjecture_false
/-- Refute Euler's conjecture for fifth powers with Lander and Parkin's counterexample
`27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵`. Hint: assume the statement (`intro H`), apply it to these five
numbers, and let `norm_num` check the arithmetic. -/
theorem euler_conjecture_false :
    ¬ ∀ a b c d e : ℕ, 0 < a → 0 < b → 0 < c → 0 < d → a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 ≠ e ^ 5 := by
  sorry
-- @endregion

-- @region ex.research_ethics.ceiling_lt_one
-- @solution Lumenary.ResearchEthics.ceiling_lt_one
/-- With a possible shared blind spot (`ρq > 0`), agreement never yields certainty.
Hint: `div_lt_one` turns the goal into `prior < prior + (1 - prior) * (ρ * q)`; the extra term
is positive by `mul_pos`. -/
theorem ceiling_lt_one {prior q ρ : ℝ} (hp₀ : 0 < prior) (hp₁ : prior < 1) (hρq : 0 < ρ * q) :
    prior / (prior + (1 - prior) * (ρ * q)) < 1 := by
  sorry
-- @endregion

-- @region ex.research_ethics.author_order_eq_of_perm
-- @solution Lumenary.ResearchEthics.authorOrder_eq_of_perm
/-- An alphabetical author list depends only on the set of authors. Hint: both sides are sorted
(`List.sortedLE_mergeSort`) and are permutations of each other (`List.mergeSort_perm`); a sorted
list is determined by its elements (`List.Perm.eq_of_sortedLE`). -/
theorem authorOrder_eq_of_perm {l₁ l₂ : List String} (h : l₁.Perm l₂) :
    authorOrder l₁ = authorOrder l₂ := by
  sorry
-- @endregion

end LumenaryExercises.ResearchEthics
