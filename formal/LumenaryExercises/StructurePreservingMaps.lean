/-
The Lumenary — Lean exercises: Structure-preserving maps.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/StructurePreservingMaps.lean`.
-/
import Lumenary.StructurePreservingMaps

namespace LumenaryExercises.StructurePreservingMaps

open Lumenary.StructurePreservingMaps

universe u v w

-- @region ex.structure_preserving_maps.preserves_op_comp
-- @solution Lumenary.StructurePreservingMaps.PreservesOp.comp
/-- Composites of homomorphisms are homomorphisms.
Hint: `intro x y`, then a `calc` block with three steps: unfold `(g ∘ f) (opA x y)` to
`g (f (opA x y))` (`rfl`), rewrite with `hf`, finish with `hg`. -/
theorem PreservesOp.comp {A : Type u} {B : Type v} {C : Type w}
    {opA : A → A → A} {opB : B → B → B} {opC : C → C → C} {f : A → B} {g : B → C}
    (hf : PreservesOp f opA opB) (hg : PreservesOp g opB opC) :
    PreservesOp (g ∘ f) opA opC := by
  sorry
-- @endregion

-- @region ex.structure_preserving_maps.comm_of_surjective
-- @solution Lumenary.StructurePreservingMaps.comm_of_surjective
/-- A surjective homomorphism carries commutativity across.
Hint: `obtain ⟨x, rfl⟩ := hsurj u` writes `u` as `f x`; do the same for `v`, then
`rw [← hf, ← hf, hcomm]`. -/
theorem comm_of_surjective {A : Type u} {B : Type v} {opA : A → A → A} {opB : B → B → B}
    {f : A → B} (hf : PreservesOp f opA opB) (hsurj : Function.Surjective f)
    (hcomm : ∀ x y, opA x y = opA y x) : ∀ u v, opB u v = opB v u := by
  sorry
-- @endregion

end LumenaryExercises.StructurePreservingMaps
