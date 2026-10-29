/-
The Lumenary — Lean exercises: Representation theory (Schur's lemma, a shear of order 2).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/RepresentationTheory.lean`.
-/
import Lumenary.RepresentationTheory

namespace LumenaryExercises.RepresentationTheory

open Lumenary.RepresentationTheory

-- @region ex.representation_theory.schur
-- @solution Lumenary.RepresentationTheory.schur
/-- Schur's lemma: a non-zero map between simple modules is bijective.
Hint: `IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker f)` splits into two cases; use
`LinearMap.ker_eq_bot` and `LinearMap.ker_eq_top`. Do the same for `LinearMap.range f` with
`LinearMap.range_eq_bot` and `LinearMap.range_eq_top`. -/
theorem schur {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) (hf : f ≠ 0) :
    Function.Bijective f := by
  sorry
-- @endregion

-- @region ex.representation_theory.shear_sq
-- @solution Lumenary.RepresentationTheory.shear_sq
/-- Over `𝔽₂` the shear `(x, y) ↦ (x + y, y)` squares to the identity.
Hint: `apply LinearMap.ext`, `rintro ⟨x, y⟩`, unfold with
`simp only [shear, LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.id_apply]`, then
`revert x y` and `decide` (there are only four vectors). -/
theorem shear_sq : shear ∘ₗ shear = LinearMap.id := by
  sorry
-- @endregion

end LumenaryExercises.RepresentationTheory
