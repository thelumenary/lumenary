/-
The Lumenary — Lean exercises: descriptive set theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/DescriptiveSetTheory.lean`.
-/
import Lumenary.DescriptiveSetTheory

namespace LumenaryExercises.DescriptiveSetTheory

open MeasureTheory Set

-- @region ex.descriptive_set_theory.projection_analytic
-- @solution Lumenary.DescriptiveSetTheory.projection_analytic
/-- Projections of Borel sets are analytic. Hint: a Borel set is analytic
(`MeasurableSet.analyticSet`) and `Prod.fst` is continuous (`continuous_fst`); use
`AnalyticSet.image_of_continuous`. -/
theorem projection_analytic {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {B : Set (X × Y)} (hB : MeasurableSet B) :
    AnalyticSet (Prod.fst '' B) := by
  sorry
-- @endregion

-- @region ex.descriptive_set_theory.suslin_from_lusin
-- @solution Lumenary.DescriptiveSetTheory.suslin_from_lusin
/-- Suslin's theorem from Lusin separation. Hint: `hA.measurablySeparable hAc disjoint_compl_right`
gives a Borel `B` with `A ⊆ B` and `Disjoint Aᶜ B`; show `B ⊆ A`. -/
theorem suslin_from_lusin {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {A : Set X} (hA : AnalyticSet A) (hAc : AnalyticSet Aᶜ) :
    MeasurableSet A := by
  sorry
-- @endregion

end LumenaryExercises.DescriptiveSetTheory
