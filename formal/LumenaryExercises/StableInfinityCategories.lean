/-
The Lumenary — Lean exercises: Stable ∞-categories.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/StableInfinityCategories.lean`.
-/
import Lumenary.StableInfinityCategories

namespace LumenaryExercises.StableInfinityCategories

open CategoryTheory Limits ZeroObject

-- @region ex.stable_infinity_categories.is_zero_of_loop_square_is_pushout
-- @solution Lumenary.StableInfinityCategories.isZero_of_loop_square_isPushout
/-- In a category with a zero object, if the loop square of `X` (three corners `0`, fourth corner
`X`) is a pushout, then `X` is zero. Hints: `rw [IsZero.iff_id_eq_zero]` turns the goal into
`𝟙 X = 0`; `h.hom_ext` says two maps out of the pushout are equal if they agree after both legs;
and `(isZero_zero C).eq_of_src f g` says any two maps out of the zero object are equal. -/
theorem isZero_of_loop_square_isPushout {C : Type*} [Category C] [HasZeroObject C]
    [HasZeroMorphisms C] (X : C)
    (h : IsPushout (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ X) (0 : (0 : C) ⟶ X)) :
    IsZero X := by
  sorry
-- @endregion

end LumenaryExercises.StableInfinityCategories
