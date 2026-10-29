/-
The Lumenary — Lean exercises: Products by maps, a first universal property.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/IntroUniversalProperties.lean`.
-/
import Lumenary.IntroUniversalProperties

namespace LumenaryExercises.IntroUniversalProperties

open Lumenary.IntroUniversalProperties

universe u

-- @region ex.intro_universal_properties.pair_unique
-- @solution Lumenary.IntroUniversalProperties.pair_unique
/-- A function into `A × B` is determined by its two components.
Hint: `funext x` reduces the goal to one point; then `Prod.ext` splits it into the two
coordinates, and `congrFun h₁ x` turns `h₁ : Prod.fst ∘ h = f` into `(h x).1 = f x`. -/
theorem pair_unique {X A B : Type u} {f : X → A} {g : X → B} (h : X → A × B)
    (h₁ : Prod.fst ∘ h = f) (h₂ : Prod.snd ∘ h = g) : h = pair f g := by
  sorry
-- @endregion

-- @region ex.intro_universal_properties.swap_is_product
-- @solution Lumenary.IntroUniversalProperties.swap_isProduct
/-- `B × A`, with the maps reading off the second and the first coordinate, is a product of
`A` and `B`. Hint: start with `intro X f g`, and offer `fun x => (g x, f x)` as the map. -/
theorem swap_isProduct (A B : Type u) : IsProduct (Prod.snd : B × A → A) Prod.fst := by
  sorry
-- @endregion

end LumenaryExercises.IntroUniversalProperties
