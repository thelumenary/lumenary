/-
The Lumenary — formal mathematics
Partial differential equations, modern theory: the Lax–Milgram theorem and the stability of
weak solutions, weak derivatives, the maximum principle, the mean value property and Hadamard's
example of an ill-posed problem.

Mathlib has the Lax–Milgram theorem (`IsCoercive.continuousLinearEquivOfBilin`), integration by
parts, convexity from second derivatives, and harmonic functions in the plane with the mean value
property (`HarmonicOnNhd.circleAverage_eq`). It does not (yet) have Sobolev spaces `H¹₀(Ω)`, the
Poincaré inequality or elliptic regularity, so here we formalise the abstract Hilbert-space core
of the weak theory and one-dimensional instances of the other ideas. Proved here: uniqueness and
the stability estimate `C‖u‖ ≤ ‖ℓ‖` for Lax–Milgram, that classical derivatives are weak
derivatives (integration by parts against a test function), the one-dimensional maximum
principle, and the blow-up in Hadamard's example.
-/
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Filter Topology Set
open scoped InnerProductSpace

namespace Lumenary.PdeTheory

/-! ### Lax–Milgram: existence, uniqueness, stability -/

-- @region pde_theory.lax_milgram
-- @provenance library
/-- **Lax–Milgram theorem.** Let `B` be a bounded bilinear form on a real Hilbert space `V`
which is coercive (`C ‖u‖² ≤ B(u, u)` for some `C > 0`). Then every bounded linear functional
`ℓ` is represented by `B`: there is `u` with `B(u, v) = ℓ(v)` for all `v`. This combines
Mathlib's `IsCoercive.continuousLinearEquivOfBilin` (the operator `u ↦ B(u, ·)` is an
isomorphism) with the Riesz representation `InnerProductSpace.toDual`. -/
theorem lax_milgram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v, B u v = ℓ v := by
  refine ⟨hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm ℓ),
    fun v => ?_⟩
  rw [← IsCoercive.continuousLinearEquivOfBilin_apply hB,
    ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
-- @endregion

-- @region pde_theory.lax_milgram_unique
-- @provenance independent
/-- **Uniqueness of weak solutions.** If `B` is coercive and `B(u₁, v) = B(u₂, v)` for all `v`,
then `u₁ = u₂`: with `w = u₁ − u₂`, coercivity gives `C ‖w‖² ≤ B(w, w) = 0`. -/
theorem lax_milgram_unique {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B) {u₁ u₂ : V} (h : ∀ v, B u₁ v = B u₂ v) :
    u₁ = u₂ := by
  obtain ⟨C, hC, hcoer⟩ := hB
  have h0 : B (u₁ - u₂) (u₁ - u₂) = 0 := by
    rw [map_sub B u₁ u₂, sub_apply, h, sub_self]
  have hw := hcoer (u₁ - u₂)
  rw [h0] at hw
  have hn : ‖u₁ - u₂‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖u₁ - u₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := mul_pos (mul_pos hC hpos) hpos
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
-- @endregion

-- @region pde_theory.lax_milgram_bound
-- @provenance independent
/-- **Stability (continuous dependence on the data).** If `C ‖u‖² ≤ B(u, u)` and
`B(u, v) = ℓ(v)` for all `v`, then `C ‖u‖ ≤ ‖ℓ‖`: indeed
`C ‖u‖² ≤ B(u, u) = ℓ(u) ≤ ‖ℓ‖ ‖u‖`; divide by `‖u‖` (the case `u = 0` is trivial). For
`−Δu = f` this is the energy estimate `‖u‖_{H¹₀} ≤ C⁻¹ ‖f‖_{H⁻¹}`. -/
theorem lax_milgram_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} {C : ℝ} (hcoer : ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u)
    (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, B u v = ℓ v) : C * ‖u‖ ≤ ‖ℓ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h, mul_zero]
    exact norm_nonneg ℓ
  · have h1 : C * ‖u‖ * ‖u‖ ≤ ‖ℓ‖ * ‖u‖ :=
      calc C * ‖u‖ * ‖u‖ ≤ B u u := hcoer u
        _ = ℓ u := hu u
        _ ≤ |ℓ u| := le_abs_self _
        _ = ‖ℓ u‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u
    exact le_of_mul_le_mul_right h1 h
-- @endregion

/-! ### Weak derivatives -/

-- @region pde_theory.classical_is_weak
-- @provenance independent
/-- **Classical derivatives are weak derivatives.** If `u` is differentiable on `[a, b]` with
integrable derivative `u'`, then for every test function `φ` vanishing at `a` and `b`,
`∫ u φ' = − ∫ u' φ`. This identity is the *definition* of "`u'` is the weak derivative of `u`",
so the weak notion extends the classical one. Proof: integration by parts (Mathlib's
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`); the boundary terms vanish. -/
theorem classical_is_weak {u u' φ φ' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hu' : IntervalIntegrable u' MeasureTheory.volume a b)
    (hφ' : IntervalIntegrable φ' MeasureTheory.volume a b) (ha : φ a = 0) (hb : φ b = 0) :
    ∫ x in a..b, u x * φ' x = -∫ x in a..b, u' x * φ x := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hφ hu' hφ', ha, hb]
  ring
-- @endregion

/-! ### Maximum principle and mean value property -/

-- @region pde_theory.max_principle_1d
-- @provenance independent
/-- **Weak maximum principle in one dimension.** If `u'' ≥ 0` on `(a, b)` (`u` is
*subharmonic*: `−Δu ≤ 0`) and `u` is continuous on `[a, b]`, then `u ≤ max(u(a), u(b))` on
`[a, b]`: the maximum is attained on the boundary. In one dimension subharmonic means convex,
so this follows from Mathlib's `convexOn_of_deriv2_nonneg` and `ConvexOn.le_on_segment`. -/
theorem max_principle_1d {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn u (Icc a b)) (hd : DifferentiableOn ℝ u (Ioo a b))
    (hd2 : DifferentiableOn ℝ (deriv u) (Ioo a b))
    (hsub : ∀ x ∈ Ioo a b, 0 ≤ deriv^[2] u x) {x : ℝ} (hx : x ∈ Icc a b) :
    u x ≤ max (u a) (u b) := by
  have hconv : ConvexOn ℝ (Icc a b) u :=
    convexOn_of_deriv2_nonneg (convex_Icc a b) hc (by rwa [interior_Icc])
      (by rwa [interior_Icc]) (by rwa [interior_Icc])
  exact hconv.le_on_segment (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
    (by rwa [segment_eq_Icc hab])
-- @endregion

-- @region pde_theory.mean_value_property
-- @provenance library
/-- **Mean value property.** A function harmonic on a neighbourhood of the closed disc of radius
`R` about `c` equals its average over the circle of radius `R` about `c`. (The maximum
principle for harmonic functions in the plane follows from it.) This is Mathlib's
`HarmonicOnNhd.circleAverage_eq`. -/
theorem mean_value_property {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall c |R|)) :
    Real.circleAverage f c R = f c :=
  hf.circleAverage_eq
-- @endregion

/-! ### Hadamard's example: the Cauchy problem for Laplace's equation is ill-posed -/

-- @region pde_theory.hadamard_blowup
-- @provenance independent
/-- **Hadamard's example.** `uₙ(x, y) = sin(n x) sinh(n y) / n²` solves `Δuₙ = 0` with Cauchy
data `uₙ(x, 0) = 0` and `∂_y uₙ(x, 0) = sin(n x)/n`, which tends to `0` uniformly. Yet at
`x = π/(2n)`, `y = 1` the solution equals `sinh(n)/n²`, which tends to `+∞`. Proof:
`sinh n ≥ (eⁿ − 1)/2` and `eⁿ/n² → ∞` (Mathlib's `Real.tendsto_exp_div_pow_atTop`). So the
solution does not depend continuously on the data. -/
theorem hadamard_blowup :
    Tendsto (fun n : ℕ => Real.sinh n / (n : ℝ) ^ 2) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.exp x / x ^ 2 / 2 - 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((Real.tendsto_exp_div_pow_atTop 2).atTop_div_const (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ (h1.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : Real.exp (-(n : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have key : Real.exp (-(n : ℝ)) / (2 * (n : ℝ) ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hsplit : Real.exp n / (n : ℝ) ^ 2 / 2 = Real.exp n / (2 * (n : ℝ) ^ 2) := by
    rw [div_div, mul_comm]
  show Real.exp (n : ℝ) / (n : ℝ) ^ 2 / 2 - 1 / 2 ≤ Real.sinh n / (n : ℝ) ^ 2
  rw [hsplit]
  calc Real.exp n / (2 * (n : ℝ) ^ 2) - 1 / 2
      ≤ Real.exp n / (2 * (n : ℝ) ^ 2) - Real.exp (-(n : ℝ)) / (2 * (n : ℝ) ^ 2) := by linarith
    _ = Real.sinh n / (n : ℝ) ^ 2 := by rw [Real.sinh_eq]; ring
-- @endregion

end Lumenary.PdeTheory
