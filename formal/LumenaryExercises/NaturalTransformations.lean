/-
The Lumenary — Lean exercises: Natural transformations.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/NaturalTransformations.lean`.
-/
import Lumenary.NaturalTransformations

namespace LumenaryExercises.NaturalTransformations

open CategoryTheory

universe v₁ v₂ u₁ u₂ u

-- @region ex.natural_transformations.natural_id_to_id
-- @solution Lumenary.NaturalTransformations.natural_id_to_id
/-- A natural family of maps `α X : X → X` on all types must be the identity.
Hint: to learn `α X x`, apply naturality to the function `fun _ => x : PUnit → X` at the point
`PUnit.unit`. -/
theorem natural_id_to_id (α : ∀ X : Type u, X → X)
    (nat : ∀ (X Y : Type u) (f : X → Y) (x : X), α Y (f x) = f (α X x)) :
    ∀ (X : Type u) (x : X), α X x = x := by
  sorry
-- @endregion

-- @region ex.natural_transformations.ess_surj
-- @solution Lumenary.NaturalTransformations.essSurj_of_counitIso
/-- A functor with a quasi-inverse is essentially surjective.
Hint: `F.EssSurj` asks, for each `Y`, for an object `X` and an isomorphism `F.obj X ≅ Y`.
Try `X = G.obj Y` and the component `ε.app Y`. The anonymous-constructor syntax is
`⟨G.obj Y, ⟨ε.app Y⟩⟩`. -/
theorem essSurj_of_counitIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (G : D ⥤ C) (ε : G ⋙ F ≅ 𝟭 D) : F.EssSurj where
  mem_essImage Y := sorry
-- @endregion

end LumenaryExercises.NaturalTransformations
