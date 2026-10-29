/-
The Lumenary — Lean exercises: Number theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ElementaryNumberTheory.lean`.
-/
import Lumenary.ElementaryNumberTheory

namespace LumenaryExercises.ElementaryNumberTheory

-- @region ex.elementary_number_theory.pell_composition
-- @solution Lumenary.ElementaryNumberTheory.pell_composition
/-- Two solutions of Pell's equation compose to a third.
Hint: the left side minus `1` equals `(x₂² − d y₂²)(x₁² − d y₁² − 1) + (x₂² − d y₂² − 1)`;
`linear_combination` can use `h₁` and `h₂` with polynomial coefficients. -/
theorem pell_composition (d x₁ y₁ x₂ y₂ : ℤ) (h₁ : x₁ ^ 2 - d * y₁ ^ 2 = 1)
    (h₂ : x₂ ^ 2 - d * y₂ ^ 2 = 1) :
    (x₁ * x₂ + d * y₁ * y₂) ^ 2 - d * (x₁ * y₂ + x₂ * y₁) ^ 2 = 1 := by
  sorry
-- @endregion

-- @region ex.elementary_number_theory.no_primitive_root_mod_eight
-- @solution Lumenary.ElementaryNumberTheory.no_primitive_root_mod_eight
/-- There is no primitive root modulo 8.
Hint: a generator `g` would have `orderOf g = 4` (`orderOf_eq_card_of_forall_mem_zpowers`), but
`units_mod_eight_sq g` shows `g ^ 2 = 1`, so `orderOf g ∣ 2`. -/
theorem no_primitive_root_mod_eight : ¬ IsCyclic (ZMod 8)ˣ := by
  sorry
-- @endregion

end LumenaryExercises.ElementaryNumberTheory
