/-
The Lumenary — formal mathematics
Descriptive set theory: Polish spaces, the bottom of the Borel hierarchy, analytic sets, Suslin's
theorem and the perfect set property for closed sets.

Mathlib has a substantial library here: `PolishSpace`, `IsGδ`, the Borel σ-algebra, analytic sets
(`MeasureTheory.AnalyticSet`, defined as continuous images of Baire space `ℕ → ℕ`), the Lusin
separation theorem, Suslin's theorem, the Lusin–Souslin theorem on injective images, and the
Cantor–Bendixson theorem. Proved here from these: that `ℚ` is not a `G_δ` subset of `ℝ` (a Baire
category argument), that projections of Borel sets are analytic, that Borel separation is
countably additive, and Suslin's theorem from the Lusin separation theorem — the same route as
the lesson. Not formalised here (nor, as far as we know, in Mathlib): the Borel hierarchy
indexed by countable ordinals, the perfect set theorem for *analytic* sets, and the existence of
an analytic non-Borel set.
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

namespace Lumenary.DescriptiveSetTheory

open MeasureTheory Set

/-! ### Polish spaces and the bottom of the Borel hierarchy -/

-- @region descriptive_set_theory.baire_space_polish
-- @provenance library
/-- **Baire space** `𝒩 = ℕ^ℕ`, with the product of discrete topologies, is Polish (separable
and completely metrisable): a countable product of Polish spaces is Polish. Mathlib provides the
instance. -/
theorem baire_space_polish : PolishSpace (ℕ → ℕ) :=
  inferInstance
-- @endregion

-- @region descriptive_set_theory.closed_is_gdelta
-- @provenance library
/-- In a metric space every closed set `F` is `G_δ` (`Π⁰₂`): `F = ⋂ₙ {x | d(x, F) < 1/(n+1)}`.
So `Σ⁰₁ ∪ Π⁰₁ ⊆ Δ⁰₂`, the first step of the Borel hierarchy. This applies Mathlib's
`IsClosed.isGδ` (metric spaces are perfectly normal). -/
theorem closed_isGδ {s : Set ℝ} (hs : IsClosed s) : IsGδ s :=
  hs.isGδ
-- @endregion

-- @region descriptive_set_theory.rat_not_is_gdelta
-- @provenance independent
/-- **`ℚ` is not a `G_δ` subset of `ℝ`** (so it is `Σ⁰₂` but not `Π⁰₂`). Proof by the Baire
category theorem: the irrationals are a dense `G_δ` (intersection of the open dense sets
`ℝ ∖ {q}`); if `ℚ` were a `G_δ` too, the intersection of these two dense `G_δ` sets would be
dense — but it is empty. -/
theorem rat_not_isGδ : ¬ IsGδ (Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  have hd := Dense.inter_of_Gδ h IsGδ.setOfPred_irrational Rat.denseRange_cast dense_irrational
  have hempty : Set.range ((↑) : ℚ → ℝ) ∩ {x | Irrational x} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨q, rfl⟩ hq
    exact hq.ne_rat q rfl
  rw [hempty] at hd
  exact Set.not_nonempty_empty hd.nonempty
-- @endregion

/-! ### Analytic sets -/

-- @region descriptive_set_theory.borel_analytic
-- @provenance library
/-- Every Borel subset of a Polish space is **analytic** (a continuous image of `ℕ^ℕ`, or empty).
This applies Mathlib's `MeasurableSet.analyticSet`. -/
theorem borel_analytic {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} (hs : MeasurableSet s) : AnalyticSet s :=
  hs.analyticSet
-- @endregion

-- @region descriptive_set_theory.analytic_image
-- @provenance library
/-- Continuous images of analytic sets are analytic. This applies Mathlib's
`AnalyticSet.image_of_continuous`. -/
theorem analytic_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : Set X}
    (hs : AnalyticSet s) {f : X → Y} (hf : Continuous f) : AnalyticSet (f '' s) :=
  hs.image_of_continuous hf
-- @endregion

-- @region descriptive_set_theory.projection_analytic
-- @provenance independent
/-- **Projections of Borel sets are analytic.** If `B ⊆ X × Y` is Borel (with `X`, `Y` Polish),
its projection `{x | ∃ y, (x, y) ∈ B}` is analytic: `B` is analytic and the projection is
continuous. Lebesgue (1905) claimed such projections are always Borel; Suslin (1917) found the
error — they need not be. -/
theorem projection_analytic {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {B : Set (X × Y)} (hB : MeasurableSet B) :
    AnalyticSet (Prod.fst '' B) :=
  analytic_image (borel_analytic hB) continuous_fst
-- @endregion

/-! ### Suslin's theorem -/

-- @region descriptive_set_theory.separation_iunion
-- @provenance independent
/-- **Separation is countably additive** (the lemma behind Lusin's separation theorem). If each
`P m` is separated from each `Q n` by a measurable (Borel) set `C m n`, then `⋃ₘ P m` is
separated from `⋃ₙ Q n` by `C = ⋃ₘ ⋂ₙ C m n`: it contains every `P m`, and a point of `Q n`
in `C` would lie in some `C m n`. (Mathlib's version is `MeasurablySeparable.iUnion`.) -/
theorem separation_iUnion {α : Type*} [MeasurableSpace α] {P Q : ℕ → Set α}
    (h : ∀ m n, MeasurablySeparable (P m) (Q n)) :
    MeasurablySeparable (⋃ m, P m) (⋃ n, Q n) := by
  choose C hPC hQC hC using h
  refine ⟨⋃ m, ⋂ n, C m n, ?_, ?_, ?_⟩
  · -- every `P m` lies in `⋂ n, C m n`
    exact Set.iUnion_mono fun m => Set.subset_iInter fun n => hPC m n
  · -- no point of `Q n` lies in any `⋂ n', C m n'`
    rw [Set.disjoint_iUnion_left]
    intro n
    rw [Set.disjoint_iUnion_right]
    intro m
    exact (hQC m n).mono_right (Set.iInter_subset _ n)
  · exact MeasurableSet.iUnion fun m => MeasurableSet.iInter fun n => hC m n
-- @endregion

-- @region descriptive_set_theory.suslin_from_lusin
-- @provenance independent
/-- **Suslin's theorem, from the Lusin separation theorem.** If `A` and its complement are both
analytic, then `A` is Borel. Proof: `A` and `Aᶜ` are disjoint analytic sets, so by Lusin's
separation theorem (Mathlib's `AnalyticSet.measurablySeparable`) some Borel set `B` satisfies
`A ⊆ B` and `B ∩ Aᶜ = ∅`; the second condition says `B ⊆ A`, so `A = B` is Borel. -/
theorem suslin_from_lusin {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {A : Set X} (hA : AnalyticSet A) (hAc : AnalyticSet Aᶜ) :
    MeasurableSet A := by
  obtain ⟨B, hAB, hdisj, hB⟩ := hA.measurablySeparable hAc disjoint_compl_right
  have hBA : B ⊆ A := fun x hxB => by
    by_contra hxA
    exact Set.disjoint_left.mp hdisj hxA hxB
  rwa [Set.Subset.antisymm hAB hBA]
-- @endregion

-- @region descriptive_set_theory.suslin
-- @provenance library
/-- **Suslin's theorem** (Mathlib's version): Borel = analytic ∩ coanalytic. This applies
`AnalyticSet.measurableSet_of_compl`; the converse direction is `borel_analytic` applied to
`A` and to its (Borel) complement. -/
theorem suslin {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {A : Set X} (hA : AnalyticSet A) (hAc : AnalyticSet Aᶜ) :
    MeasurableSet A :=
  hA.measurableSet_of_compl hAc
-- @endregion

-- @region descriptive_set_theory.lusin_souslin
-- @provenance library
/-- **Lusin–Souslin**: the image of a Borel set under an injective continuous map from a Polish
space is Borel — injectivity is exactly what fails in Lebesgue's projection argument. This
applies Mathlib's `MeasurableSet.image_of_continuousOn_injOn`. -/
theorem lusin_souslin {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {s : Set X} (hs : MeasurableSet s) {f : X → Y} (hf : Continuous f) (hinj : Set.InjOn f s) :
    MeasurableSet (f '' s) :=
  hs.image_of_continuousOn_injOn hf.continuousOn hinj
-- @endregion

/-! ### The perfect set property -/

-- @region descriptive_set_theory.cantor_bendixson
-- @provenance library
/-- **Cantor–Bendixson**: every closed set in a second-countable space is the union of a countable
set and a perfect set. This applies Mathlib's `exists_countable_union_perfect_of_isClosed`. -/
theorem cantor_bendixson {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {C : Set X} (hC : IsClosed C) : ∃ V D : Set X, V.Countable ∧ Perfect D ∧ C = V ∪ D :=
  exists_countable_union_perfect_of_isClosed hC
-- @endregion

-- @region descriptive_set_theory.perfect_set_closed
-- @provenance library
/-- **The perfect set property for closed sets**: an uncountable closed subset of a Polish space
contains a continuous injective image of Cantor space `2^ℕ`, hence has cardinality `2^ℵ₀`. So
no closed set is a counterexample to CH. This applies Mathlib's
`IsClosed.exists_nat_bool_injection_of_not_countable`. -/
theorem perfect_set_closed {X : Type*} [TopologicalSpace X] [PolishSpace X] {C : Set X}
    (hC : IsClosed C) (hunc : ¬ C.Countable) :
    ∃ f : (ℕ → Bool) → X, Set.range f ⊆ C ∧ Continuous f ∧ Function.Injective f :=
  hC.exists_nat_bool_injection_of_not_countable hunc
-- @endregion

end Lumenary.DescriptiveSetTheory
