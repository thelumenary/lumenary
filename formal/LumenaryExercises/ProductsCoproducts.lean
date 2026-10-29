/-
The Lumenary — Lean exercises: Products, coproducts, initial and terminal objects.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/ProductsCoproducts.lean`.
-/
import Lumenary.ProductsCoproducts

namespace LumenaryExercises.ProductsCoproducts

open CategoryTheory Lumenary.ProductsCoproducts

universe v u

-- @region ex.products_coproducts.hom_ext
-- @solution Lumenary.ProductsCoproducts.IsBinaryProduct.hom_ext
/-- Two morphisms into a product that agree after both projections are equal.
Hint: the uniqueness clause `hP.uniq f g h h₁ h₂` says any `h` with `h ≫ π₁ = f` and
`h ≫ π₂ = g` equals `hP.lift f g`. Apply it to `h` and to `k` with the same `f` and `g`
(take `f := h ≫ π₁`, `g := h ≫ π₂`), then rewrite. -/
theorem hom_ext {C : Type u} [Category.{v} C] {A B P : C} {π₁ : P ⟶ A} {π₂ : P ⟶ B}
    (hP : IsBinaryProduct π₁ π₂) {X : C} {h k : X ⟶ P} (h₁ : h ≫ π₁ = k ≫ π₁)
    (h₂ : h ≫ π₂ = k ≫ π₂) : h = k := by
  sorry
-- @endregion

-- @region ex.products_coproducts.product_eq_inf
-- @solution Lumenary.ProductsCoproducts.product_eq_inf
/-- In a poset, a product of `a` and `b` is their meet.
Hint: use `le_antisymm`. One inequality is `le_inf (leOfHom π₁) (leOfHom π₂)`; for the other,
apply the universal property `hp.lift` to the two morphisms `homOfLE inf_le_left` and
`homOfLE inf_le_right` out of `a ⊓ b`, and turn the result into an inequality with `leOfHom`. -/
theorem product_eq_inf {α : Type u} [SemilatticeInf α] {a b p : α} {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (hp : IsBinaryProduct π₁ π₂) : p = a ⊓ b := by
  sorry
-- @endregion

end LumenaryExercises.ProductsCoproducts
