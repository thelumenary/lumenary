/-
The Lumenary — formal mathematics
Measure theory and integration: Lebesgue measure, null sets, Markov's inequality, the convergence
theorems, a sequence whose mass escapes, Tonelli's theorem and the completeness of `Lᵖ`.

Mathlib builds Lebesgue measure `volume` on `ℝ` from outer measure by Carathéodory's criterion
(via Stieltjes functions), and proves the monotone and dominated convergence theorems, Fatou's
lemma, Tonelli and Fubini, and the Riesz–Fischer theorem that `Lᵖ` is complete. Proved here from
more basic facts: that `ℚ` is Lebesgue-null (countable subadditivity), Markov's inequality, and
the "escaping mass" example `fₙ = n · 1_(0, 1/n)` (integral `1` for every `n`, pointwise limit
`0`), which shows why the convergence theorems need hypotheses.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Lumenary.MeasureTheory

/-! ### Lebesgue measure and null sets -/

-- @region measure_theory.volume_icc
-- @provenance library
/-- Lebesgue measure extends length: `λ([a, b]) = b − a` (as an extended non-negative real;
`ENNReal.ofReal` sends negative numbers to `0`, so the formula also covers `b < a`). Mathlib
constructs `volume` on `ℝ` by Carathéodory's criterion and proves this as `Real.volume_Icc`. -/
theorem volume_Icc (a b : ℝ) : volume (Icc a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Icc
-- @endregion

-- @region measure_theory.volume_rat_eq_zero
-- @provenance independent
/-- **The rationals form a Lebesgue-null set.** `ℚ ⊂ ℝ` is the countable union of the
singletons `{q}`, each of measure `0`; by countable subadditivity the union has measure `0`.
This is the lesson's proof, using Mathlib's `measure_iUnion_null` (a countable union of null
sets is null) and `Real.volume_singleton`. -/
theorem volume_rat_eq_zero : volume (range ((↑) : ℚ → ℝ)) = 0 := by
  rw [← iUnion_singleton_eq_range]
  exact measure_iUnion_null fun q => Real.volume_singleton
-- @endregion

-- @region measure_theory.countable_null
-- @provenance library
/-- More generally, every countable subset of `ℝ` is Lebesgue-null (`Set.Countable.measure_zero`;
the hypothesis Mathlib needs is that singletons are null). The converse is false: the Cantor
set is uncountable and null. -/
theorem countable_null {s : Set ℝ} (hs : s.Countable) : volume s = 0 :=
  hs.measure_zero volume
-- @endregion

/-! ### Markov's inequality -/

-- @region measure_theory.markov
-- @provenance independent
/-- **Markov's inequality.** For a measurable `f : α → [0, ∞]` and `ε ∈ [0, ∞]`,
`ε · μ{f ≥ ε} ≤ ∫ f dμ`. Proof: the simple function `ε · 1_{f ≥ ε}` lies below `f`, and its
integral is `ε · μ{f ≥ ε}`; integrals are monotone. (Mathlib: `mul_meas_ge_le_lintegral`.) -/
theorem markov {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) (ε : ℝ≥0∞) : ε * μ {x | ε ≤ f x} ≤ ∫⁻ x, f x ∂μ := by
  have hs : MeasurableSet {x | ε ≤ f x} := measurableSet_le measurable_const hf
  calc ε * μ {x | ε ≤ f x} = ∫⁻ x, {x | ε ≤ f x}.indicator (fun _ => ε) x ∂μ :=
        (lintegral_indicator_const hs ε).symm
    _ ≤ ∫⁻ x, f x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : ε ≤ f x
        · simpa [indicator_of_mem (show x ∈ {x | ε ≤ f x} from hx)] using hx
        · simp [indicator_of_notMem (show x ∉ {x | ε ≤ f x} from hx)]
-- @endregion

/-! ### The convergence theorems -/

-- @region measure_theory.monotone_convergence
-- @provenance library
/-- **Monotone convergence theorem** (Beppo Levi). If `0 ≤ f₀ ≤ f₁ ≤ ⋯` are measurable, then
`∫ sup fₙ = sup ∫ fₙ`. No integrability hypothesis is needed for non-negative functions. This is
Mathlib's `lintegral_iSup`. -/
theorem monotone_convergence {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    ∫⁻ x, ⨆ n, f n x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ :=
  lintegral_iSup hf hmono
-- @endregion

-- @region measure_theory.dominated_convergence
-- @provenance library
/-- **Dominated convergence theorem** (Lebesgue). If `Fₙ → f` almost everywhere and
`‖Fₙ‖ ≤ g` almost everywhere for one integrable `g`, then `∫ Fₙ → ∫ f`. This is Mathlib's
`tendsto_integral_of_dominated_convergence`. -/
theorem dominated_convergence {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F : ℕ → α → ℝ} {f g : α → ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hg : Integrable g μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence g hF hg hbound hlim
-- @endregion

/-! ### Mass can escape: why the hypotheses matter -/

-- @region measure_theory.escaping_mass
-- @provenance definition
/-- The "escaping mass" sequence `fₙ = n · 1_(0, 1/n)`: a tower of height `n` over an interval
of length `1/n`. -/
noncomputable def escapingMass (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioo (0 : ℝ) (1 / n)).indicator fun _ => (n : ℝ≥0∞)
-- @endregion

-- @region measure_theory.escaping_mass_lintegral
-- @provenance independent
/-- Every `fₙ` (with `n ≥ 1`) has integral exactly `1`: the integral of `c · 1_A` is
`c · λ(A)`, and here `n · (1/n) = 1`. -/
theorem escapingMass_lintegral {n : ℕ} (hn : 1 ≤ n) : ∫⁻ x, escapingMass n x = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [escapingMass, lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n), mul_one_div_cancel hn',
    ENNReal.ofReal_one]
-- @endregion

-- @region measure_theory.escaping_mass_tendsto_zero
-- @provenance independent
/-- …yet `fₙ(x) → 0` for **every** `x ∈ ℝ`: if `x ≤ 0` every term is `0`; if `x > 0`, then as
soon as `n > 1/x` we have `x ∉ (0, 1/n)`, so `fₙ(x) = 0`. Hence `∫ lim fₙ = 0 ≠ 1 = lim ∫ fₙ`:
there is no integrable dominating function and the sequence is not monotone. -/
theorem escapingMass_tendsto_zero (x : ℝ) :
    Tendsto (fun n => escapingMass n x) atTop (𝓝 0) := by
  -- It suffices that `fₙ(x) = 0` for all large `n`.
  apply tendsto_const_nhds.congr'
  rcases le_or_gt x 0 with hx | hx
  · -- `x ≤ 0`: `x` is never in `(0, 1/n)`.
    refine Eventually.of_forall fun n => ?_
    have hmem : x ∉ Ioo (0 : ℝ) (1 / n) := fun h => (not_lt.2 hx) h.1
    show (0 : ℝ≥0∞) = escapingMass n x
    rw [escapingMass, indicator_of_notMem hmem]
  · -- `x > 0`: choose `N > 1/x`; for `n ≥ N` we have `1/n ≤ x`.
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNpos (by exact_mod_cast hn)
    have hle : 1 / (n : ℝ) ≤ x := by
      rw [div_le_iff₀ hnpos]
      have h1 : 1 < N * x := by rwa [div_lt_iff₀ hx] at hN
      nlinarith [show (N : ℝ) ≤ n by exact_mod_cast hn]
    have hmem : x ∉ Ioo (0 : ℝ) (1 / n) := fun h => (not_lt.2 hle) h.2
    show (0 : ℝ≥0∞) = escapingMass n x
    rw [escapingMass, indicator_of_notMem hmem]
-- @endregion

/-! ### Product measures and `Lᵖ` -/

-- @region measure_theory.tonelli
-- @provenance library
/-- **Tonelli's theorem.** For a measurable `f : α × β → [0, ∞]` and σ-finite (in Mathlib:
s-finite) measures, the integral over the product equals either iterated integral. This is
Mathlib's `lintegral_prod`. -/
theorem tonelli {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite ν] (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  lintegral_prod f hf
-- @endregion

-- @region measure_theory.lp_complete
-- @provenance library
/-- **Riesz–Fischer.** For `1 ≤ p ≤ ∞`, the space `Lᵖ(μ)` (functions modulo equality almost
everywhere) is complete, hence a Banach space. Mathlib provides the instance
`MeasureTheory.Lp.instCompleteSpace`. -/
theorem lp_complete {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : CompleteSpace (Lp ℝ p μ) :=
  inferInstance
-- @endregion

-- @region measure_theory.borel_cantelli
-- @provenance library
/-- **First Borel–Cantelli lemma.** If `∑ μ(Aₙ) < ∞`, then almost every point lies in only
finitely many `Aₙ`: `μ(limsup Aₙ) = 0`. This is Mathlib's `measure_limsup_atTop_eq_zero`. -/
theorem borel_cantelli {α : Type*} [MeasurableSpace α] (μ : Measure α) {A : ℕ → Set α}
    (hA : ∑' n, μ (A n) ≠ ∞) : μ (limsup A atTop) = 0 :=
  measure_limsup_atTop_eq_zero hA
-- @endregion

end Lumenary.MeasureTheory
