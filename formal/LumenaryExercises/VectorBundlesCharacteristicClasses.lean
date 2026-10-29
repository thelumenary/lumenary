/-
The Lumenary — Lean exercises: Vector bundles and characteristic classes.
Replace each `sorry` with a proof. Worked solutions are in
`Lumenary/VectorBundlesCharacteristicClasses.lean`.
-/
import Lumenary.VectorBundlesCharacteristicClasses

namespace LumenaryExercises.VectorBundlesCharacteristicClasses

-- @region ex.vector_bundles_characteristic_classes.mobius_not_trivial
-- @solution Lumenary.VectorBundlesCharacteristicClasses.mobius_not_trivial
/-- Deduce that the Möbius bundle has no nowhere-zero section.
Hint: use `Lumenary.VectorBundlesCharacteristicClasses.mobius_section_vanishes` to find a zero
of `s`, contradicting `∀ t, s t ≠ 0`. -/
theorem mobius_not_trivial :
    ¬ ∃ s : ℝ → ℝ, Continuous s ∧ (∀ t, s (t + 1) = -s t) ∧ ∀ t, s t ≠ 0 := by
  sorry
-- @endregion

-- @region ex.vector_bundles_characteristic_classes.mobius_section_vanishes
-- @solution Lumenary.VectorBundlesCharacteristicClasses.mobius_section_vanishes
/-- Prove that every continuous antiperiodic function `s(t + 1) = -s(t)` has a zero in `[0, 1]`.
Hint: compare the signs of `s 0` and `s 1 = -s 0` with `le_total (s 0) 0`, then apply
`intermediate_value_Icc` or `intermediate_value_Icc'` on `[0, 1]`. -/
theorem mobius_section_vanishes (s : ℝ → ℝ) (hs : Continuous s) (anti : ∀ t, s (t + 1) = -s t) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, s t = 0 := by
  sorry
-- @endregion

end LumenaryExercises.VectorBundlesCharacteristicClasses
