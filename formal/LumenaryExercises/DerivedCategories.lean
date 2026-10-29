/-
The Lumenary — Lean exercises: Derived categories (chain homotopies).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/DerivedCategories.lean`.
-/
import Lumenary.DerivedCategories

namespace LumenaryExercises.DerivedCategories

variable {R : Type*} [Ring R] {A₁ A₀ B₁ : Type*}
  [AddCommGroup A₁] [AddCommGroup A₀] [AddCommGroup B₁]
  [Module R A₁] [Module R A₀] [Module R B₁]

-- @region ex.derived_categories.cycles_map_eq_of_homotopy
-- @solution Lumenary.DerivedCategories.cycles_map_eq_of_homotopy
/-- Homotopic chain maps of two-term complexes agree on the cycles `ker d`.
Hint: show `f₁ x - g₁ x = h (d x)` from `hom₁` (`LinearMap.sub_apply`, `LinearMap.comp_apply`),
then use `hx` and `sub_eq_zero`. -/
theorem cycles_map_eq_of_homotopy (d : A₁ →ₗ[R] A₀) (f₁ g₁ : A₁ →ₗ[R] B₁) (h : A₀ →ₗ[R] B₁)
    (hom₁ : f₁ - g₁ = h ∘ₗ d) (x : A₁) (hx : d x = 0) : f₁ x = g₁ x := by
  sorry
-- @endregion

end LumenaryExercises.DerivedCategories
