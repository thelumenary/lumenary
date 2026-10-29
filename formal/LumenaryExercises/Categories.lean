/-
The Lumenary — Lean exercises: Categories.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Categories.lean`.
Remember that Mathlib writes composition in diagrammatic order: `f ≫ g` is "first `f`, then `g`".
-/
import Lumenary.Categories

namespace LumenaryExercises.Categories

open CategoryTheory

universe u v

-- @region ex.categories.left_inv_eq_right_inv
-- @solution Lumenary.Categories.left_inv_eq_right_inv
/-- A left inverse equals a right inverse. Hint: write a `calc` block starting
`g = 𝟙 Y ≫ g` and use `Category.id_comp`, `Category.assoc` and `Category.comp_id`. -/
theorem left_inv_eq_right_inv {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}
    {g h : Y ⟶ X} (hg : f ≫ g = 𝟙 X) (hh : h ≫ f = 𝟙 Y) : g = h := by
  sorry
-- @endregion

-- @region ex.categories.mono_comp
-- @solution Lumenary.Categories.mono_comp
/-- A composite of monomorphisms is a monomorphism. Hint: after `constructor; intro W a b hab`,
rewrite `hab` with `Category.assoc` and use `Mono.right_cancellation` twice. -/
theorem mono_comp {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  sorry
-- @endregion

-- @region ex.categories.preorder_iso_eq
-- @solution Lumenary.Categories.preorder_iso_eq
/-- In a partial order regarded as a category, isomorphic objects are equal.
Hint: `leOfHom` turns a morphism `x ⟶ y` into a proof of `x ≤ y`. -/
theorem preorder_iso_eq {α : Type u} [PartialOrder α] {x y : α} (e : x ≅ y) : x = y := by
  sorry
-- @endregion

end LumenaryExercises.Categories
