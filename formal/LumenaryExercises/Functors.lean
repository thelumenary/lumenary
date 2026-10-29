/-
The Lumenary — Lean exercises: Functors.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Functors.lean`.
-/
import Lumenary.Functors

namespace LumenaryExercises.Functors

open CategoryTheory

universe u v u₂ v₂

-- @region ex.functors.map_inverse
-- @solution Lumenary.Functors.map_inverse
/-- Functors carry inverse pairs to inverse pairs. Hint: rewrite with `← F.map_comp`, then use
the hypothesis and `F.map_id`. -/
theorem map_inverse {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} (h₁ : f ≫ g = 𝟙 X) (h₂ : g ≫ f = 𝟙 Y) :
    F.map f ≫ F.map g = 𝟙 (F.obj X) ∧ F.map g ≫ F.map f = 𝟙 (F.obj Y) := by
  sorry
-- @endregion

-- @region ex.functors.zmod4_not_iso_klein
-- @solution Lumenary.Functors.zmod4_not_iso_klein
/-- `ℤ/4` and `ℤ/2 × ℤ/2` are not isomorphic. Hint: every `y : ZMod 2 × ZMod 2` has
`y + y = 0` (`by decide`), so `e 2 = e 1 + e 1 = 0 = e 0`; then use `e.injective`. -/
theorem zmod4_not_iso_klein : IsEmpty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  sorry
-- @endregion

end LumenaryExercises.Functors
