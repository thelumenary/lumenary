/-
The Lumenary — Lean exercises: representable functors.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RepresentableFunctors.lean`.
-/
import Lumenary.RepresentableFunctors

namespace LumenaryExercises.RepresentableFunctors

open CategoryTheory

-- @region ex.representable_functors.int_hom_determined
-- @solution Lumenary.RepresentableFunctors.int_hom_eq_zpow
/-- Two homomorphisms out of `ℤ` that agree on `1` agree everywhere. Hint: rewrite both sides
with `Lumenary.RepresentableFunctors.int_hom_eq_zpow`. -/
theorem int_hom_determined {G : Type*} [Group G] (φ ψ : Multiplicative ℤ →* G)
    (h : φ (Multiplicative.ofAdd 1) = ψ (Multiplicative.ofAdd 1)) (n : ℤ) :
    φ (Multiplicative.ofAdd n) = ψ (Multiplicative.ofAdd n) := by
  sorry
-- @endregion

-- @region ex.representable_functors.subsingleton_of_corepresentable
-- @solution Lumenary.RepresentableFunctors.subsingleton_of_corepresentable
/-- A corepresentable functor on types has at most one element over the one-point type.
Hint: write `y` and `y'` as `e.homEquiv` of morphisms `A ⟶ PUnit`, and show those morphisms are
equal. -/
theorem subsingleton_of_corepresentable {F : Type ⥤ Type} {A : Type}
    (e : F.CorepresentableBy A) : Subsingleton (F.obj PUnit) := by
  sorry
-- @endregion

end LumenaryExercises.RepresentableFunctors
