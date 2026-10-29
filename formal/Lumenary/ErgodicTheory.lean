/-
The Lumenary — formal mathematics
Ergodic theory: Poincaré recurrence, Birkhoff sums of coboundaries, von Neumann's mean ergodic
theorem, and ergodicity of the doubling map and of irrational rotations.

Mathlib has measure-preserving maps (`MeasurePreserving`), conservative systems and the Poincaré
recurrence theorem (`Conservative.ae_mem_imp_frequently_image_mem`), ergodicity (`Ergodic`),
Birkhoff sums and averages (`birkhoffSum`, `birkhoffAverage`), von Neumann's mean ergodic theorem
in Hilbert space, and ergodicity of `x ↦ n • x` (`n ≥ 2`) and of rotations of infinite order on
the circle. Proved here: a pigeonhole version of Poincaré recurrence (some point of a set of
positive measure returns), the telescoping of Birkhoff sums of coboundaries and the vanishing of
their averages — the key step in von Neumann's proof — and the criterion "a rotation is ergodic
iff its angle is irrational". Not in Mathlib (nor here): Birkhoff's pointwise ergodic theorem,
mixing, entropy, and the invariance of the Gauss measure.
-/
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

open MeasureTheory Filter Topology Set

namespace Lumenary.ErgodicTheory

/-! ### Poincaré recurrence -/

-- @region ergodic_theory.recurrence_pigeonhole
-- @provenance independent
/-- **Recurrence by pigeonhole.** Let `f` preserve a finite measure `μ` and let `μ(s) > 0`. Then
some point of `s` returns to `s`. Proof: choose `N` with `N · μ(s) > μ(X)`. The sets
`s, f⁻¹s, …, f^{-(N-1)}s` all have measure `μ(s)`, so their measures add up to more than
`μ(X)`, and two of them meet (Mathlib's measure-theoretic pigeonhole principle
`exists_nonempty_inter_of_measure_univ_lt_sum_measure`). If `y ∈ f^{-i}s ∩ f^{-j}s` with
`i < j`, then `x = fⁱ(y) ∈ s` and `f^{j-i}(x) = fʲ(y) ∈ s`. -/
theorem recurrence_pigeonhole {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → α} (hf : MeasurePreserving f μ μ) {s : Set α}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) : ∃ x ∈ s, ∃ k, 0 < k ∧ f^[k] x ∈ s := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hpos (measure_ne_top μ univ)
  have hmeas : ∀ i ∈ Finset.range N, NullMeasurableSet (f^[i] ⁻¹' s) μ :=
    fun i _ => ((hf.iterate i).measurable hs).nullMeasurableSet
  have hsum : ∑ i ∈ Finset.range N, μ (f^[i] ⁻¹' s) = N * μ s := by
    rw [Finset.sum_congr rfl fun i _ => (hf.iterate i).measure_preimage hs.nullMeasurableSet]
    simp
  obtain ⟨i, -, j, -, hij, y, hyi, hyj⟩ :=
    exists_nonempty_inter_of_measure_univ_lt_sum_measure μ hmeas (hsum ▸ hN)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨f^[i] y, hyi, j - i, Nat.sub_pos_of_lt h, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
    exact hyj
  · refine ⟨f^[j] y, hyj, i - j, Nat.sub_pos_of_lt h, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
    exact hyi
-- @endregion

-- @region ergodic_theory.poincare_recurrence
-- @provenance library
/-- **Poincaré recurrence theorem.** If `f` preserves a finite measure and `s` is measurable,
then almost every point of `s` returns to `s` infinitely often. A measure-preserving map of a
finite measure space is conservative (`MeasurePreserving.conservative`), and Mathlib proves
recurrence for conservative maps (`Conservative.ae_mem_imp_frequently_image_mem`). -/
theorem poincare_recurrence {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ) {s : Set α} (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s :=
  hf.conservative.ae_mem_imp_frequently_image_mem hs
-- @endregion

/-! ### Birkhoff sums and the mean ergodic theorem -/

-- @region ergodic_theory.birkhoff_sum_coboundary
-- @provenance independent
/-- **Birkhoff sums of a coboundary telescope.** If `g = h ∘ f − h`, then
`g(x) + g(f x) + ⋯ + g(f^{n−1} x) = h(fⁿ x) − h(x)`. By induction on `n`, using Mathlib's
`birkhoffSum_succ_apply`. -/
theorem birkhoff_sum_coboundary {α : Type*} (f : α → α) (h : α → ℝ) (n : ℕ) (x : α) :
    birkhoffSum f (fun y => h (f y) - h y) n x = h (f^[n] x) - h x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ih, Function.iterate_succ_apply']
    ring
-- @endregion

-- @region ergodic_theory.coboundary_average_tendsto_zero
-- @provenance independent
/-- **Time averages of a bounded coboundary vanish.** If `|h| ≤ C`, the Birkhoff averages of
`h ∘ f − h` are at most `2C/n` in absolute value, so they tend to `0` at every point. In von
Neumann's proof of the mean ergodic theorem, `L²` splits into invariant functions (where averages
are constant) and the closure of such coboundaries (where averages tend to `0`). -/
theorem coboundary_average_tendsto_zero {α : Type*} (f : α → α) (h : α → ℝ) {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) (x : α) :
    Tendsto (fun n => birkhoffAverage ℝ f (fun y => h (f y) - h y) n x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 2 * C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [birkhoffAverage, birkhoff_sum_coboundary, smul_eq_mul, norm_mul, norm_inv,
    Real.norm_natCast, Real.norm_eq_abs, inv_mul_eq_div]
  gcongr
  calc |h (f^[n] x) - h x| ≤ |h (f^[n] x)| + |h x| := abs_sub _ _
    _ ≤ C + C := add_le_add (hC _) (hC _)
    _ = 2 * C := by ring
-- @endregion

-- @region ergodic_theory.mean_ergodic
-- @provenance library
/-- **Von Neumann's mean ergodic theorem.** For a contraction `U` (`‖U‖ ≤ 1`) of a Hilbert space —
for instance the Koopman operator `φ ↦ φ ∘ T` of a measure-preserving `T` on `L²(μ)` — the
averages `(1/N) ∑_{n<N} Uⁿ x` converge in norm to the orthogonal projection of `x` onto the
subspace of `U`-invariant vectors. This is Mathlib's
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`. -/
theorem mean_ergodic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : E →L[ℝ] E) (hU : ‖U‖ ≤ 1) (x : E) :
    Tendsto (birkhoffAverage ℝ U _root_.id · x) atTop
      (𝓝 ((U.eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto x)) :=
  U.tendsto_birkhoffAverage_orthogonalProjection hU x
-- @endregion

/-! ### Examples on the circle -/

-- @region ergodic_theory.doubling_ergodic
-- @provenance library
/-- **The doubling map `x ↦ 2x mod 1` is ergodic** for Lebesgue (Haar) measure on the circle
`ℝ/Tℤ`. Mathlib proves this for `x ↦ n • x` with `n ≥ 2` (`AddCircle.ergodic_nsmul`), via
Lebesgue's density theorem. -/
theorem doubling_ergodic (T : ℝ) [Fact (0 < T)] : Ergodic fun y : AddCircle T => 2 • y :=
  AddCircle.ergodic_nsmul (by norm_num)
-- @endregion

-- @region ergodic_theory.rotation_ergodic_iff
-- @provenance library
/-- **A rotation of the circle `ℝ/ℤ` by `α` is ergodic iff `α` is irrational.** Mathlib shows that
a rotation is ergodic iff the angle has infinite additive order (`AddCircle.ergodic_add_left`),
iff its multiples are dense (`AddCircle.denseRange_zsmul_iff`), iff `α` is irrational
(`AddCircle.denseRange_zsmul_coe_iff`). -/
theorem rotation_ergodic_iff (α : ℝ) :
    Ergodic (fun y : AddCircle (1 : ℝ) => (α : AddCircle (1 : ℝ)) + y) ↔ Irrational α := by
  rw [AddCircle.ergodic_add_left, ← AddCircle.denseRange_zsmul_iff,
    AddCircle.denseRange_zsmul_coe_iff, div_one]
-- @endregion

end Lumenary.ErgodicTheory
