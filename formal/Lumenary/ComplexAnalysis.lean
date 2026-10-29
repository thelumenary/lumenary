/-
The Lumenary — formal mathematics
Complex analysis: complex differentiability and the Cauchy–Riemann equations, Cauchy's theorem
and integral formula on discs, holomorphic functions are analytic, Liouville's theorem and the
fundamental theorem of algebra.

What is proved here and what Mathlib provides. Mathlib's holomorphic functions are functions
`f : ℂ → E` with `DifferentiableOn ℂ f U`; contour integrals over circles are `circleIntegral`,
written `∮ z in C(c, R), f z`. Mathlib proves Cauchy's theorem for rectangles and discs (via a
version of Green's theorem), the Cauchy integral formula, analyticity of holomorphic functions,
the Cauchy estimates and Liouville's theorem. The *independent* declarations below mirror the
lesson's human proofs: a complex derivative gives the directional derivatives `f'` (along `ℝ`)
and `i f'` (along `iℝ`) — the Cauchy–Riemann equations; complex conjugation is therefore nowhere
complex-differentiable; Liouville's theorem from the Cauchy estimate; the fundamental theorem of
algebra from Liouville's theorem; and the fact that `1/z` has no entire extension because its
integral around the unit circle is `2πi ≠ 0`. The general residue theorem and the argument
principle are not formalised here (Mathlib has no general residue theorem at this version).
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Lumenary.ComplexAnalysis

open Complex Filter Topology Metric Set

/-! ### Complex differentiability and the Cauchy–Riemann equations -/

-- @region complex_analysis.holomorphic_on
-- @provenance definition
/-- `HolomorphicOn f U`: `f` is complex-differentiable at every point of `U` (the lesson's
definition, for open `U`). This is just a name for Mathlib's `DifferentiableOn ℂ f U`. -/
abbrev HolomorphicOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U
-- @endregion

-- @region complex_analysis.directional_derivatives
-- @provenance independent
/-- **The Cauchy–Riemann equations, in derivative form.** If `f` has complex derivative `f'` at
`z`, then moving from `z` in the real direction, `t ↦ f(z + t)`, has derivative `f'`, and moving
in the imaginary direction, `t ↦ f(z + t i)`, has derivative `f' · i` (chain rule: the inner map
`t ↦ z + t i` has derivative `i`). Writing `f = u + i v`, comparing the two gives
`u_y = -v_x` and `v_y = u_x`. -/
theorem directional_derivatives {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z) :
    HasDerivAt (fun t : ℝ => f (z + t)) f' 0 ∧
      HasDerivAt (fun t : ℝ => f (z + t * I)) (f' * I) 0 := by
  constructor
  · have h0 : HasDerivAt f f' (z + ((0 : ℝ) : ℂ)) := by simpa using h
    exact (HasDerivAt.comp_const_add z ((0 : ℝ) : ℂ) h0).comp_ofReal
  · have hin : HasDerivAt (fun w : ℂ => z + w * I) I ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const I).const_add z
    have h0 : HasDerivAt f f' (z + ((0 : ℝ) : ℂ) * I) := by simpa using h
    exact (h0.comp ((0 : ℝ) : ℂ) hin).comp_ofReal
-- @endregion

-- @region complex_analysis.conj_not_differentiable_at
-- @provenance independent
/-- **`z ↦ z̄` is complex-differentiable nowhere.** In the real direction `conj (z + t) = z̄ + t`
changes at rate `1`; in the imaginary direction `conj (z + t i) = z̄ - t i` changes at rate `-i`.
A complex derivative `f'` would need `f' = 1` and `f' i = -i` (`directional_derivatives`), so
`i = -i` — impossible. Yet conjugation is real-linear, so as a map `ℝ² → ℝ²` it is as smooth as
can be: it fails the Cauchy–Riemann equations (`u = x`, `v = -y`, so `u_x = 1 ≠ -1 = v_y`). -/
theorem conj_not_differentiableAt (z : ℂ) : ¬ DifferentiableAt ℂ (starRingEnd ℂ) z := by
  intro hd
  obtain ⟨h1, h2⟩ := directional_derivatives hd.hasDerivAt
  have e1 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (z + t)) 1 0 := by
    have hfun : (fun t : ℝ => (starRingEnd ℂ) (z + t)) = fun t : ℝ => (starRingEnd ℂ) z + (t : ℂ) := by
      funext t; simp
    rw [hfun]
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add ((starRingEnd ℂ) z)
  have e2 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (z + t * I)) (-I) 0 := by
    have hfun : (fun t : ℝ => (starRingEnd ℂ) (z + t * I))
        = fun t : ℝ => (starRingEnd ℂ) z + (t : ℂ) * (-I) := by
      funext t; simp
    rw [hfun]
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (-I)).const_add ((starRingEnd ℂ) z)
  have u1 := h1.unique e1
  have u2 := h2.unique e2
  rw [u1, one_mul] at u2
  have : (2 : ℂ) * I = 0 := by rw [two_mul]; nth_rewrite 1 [u2]; ring
  simp at this
-- @endregion

/-! ### Cauchy's theorem and the Cauchy integral formula -/

-- @region complex_analysis.cauchy_theorem_disc
-- @provenance library
/-- **Cauchy's theorem for a disc.** If `f` is holomorphic on a neighbourhood of the closed disc
`|z - c| ≤ R`, then `∮_{|z - c| = R} f(z) dz = 0`. This applies Mathlib's
`DiffContOnCl.circleIntegral_eq_zero` (Mathlib proves it from Cauchy's theorem for rectangles). -/
theorem cauchy_theorem_disc {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) : (∮ z in C(c, R), f z) = 0 :=
  (hf.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hR
-- @endregion

-- @region complex_analysis.circle_integral_inv
-- @provenance library
/-- **The basic integral:** `∮_{|z - c| = R} dz / (z - w) = 2πi` for every `w` inside the circle.
This applies Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`. It is not `0`, so
`1/(z - w)` has no primitive on the punctured plane. -/
theorem circle_integral_inv {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * (Real.pi : ℂ) * I :=
  circleIntegral.integral_sub_inv_of_mem_ball hw
-- @endregion

-- @region complex_analysis.cauchy_integral_formula
-- @provenance library
/-- **Cauchy's integral formula.** If `f` is holomorphic on the closed disc `|z - c| ≤ R` and
`|w - c| < R`, then `∮_{|z - c| = R} f(z)/(z - w) dz = 2πi f(w)`: the values of `f` inside the
disc are determined by its values on the boundary circle. This applies Mathlib's
`DifferentiableOn.circleIntegral_sub_inv_smul`. -/
theorem cauchy_integral_formula {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ * f z) = 2 * (Real.pi : ℂ) * I * f w := by
  simpa [smul_eq_mul] using hf.circleIntegral_sub_inv_smul hw
-- @endregion

-- @region complex_analysis.holomorphic_is_analytic
-- @provenance library
/-- **Holomorphic functions are analytic.** If `f` is complex-differentiable on a neighbourhood of
`z`, then `f` equals the sum of its Taylor series near `z`. This applies Mathlib's
`DifferentiableOn.analyticAt`, which expands the Cauchy kernel `1/(ζ - w)` in a geometric series,
exactly as in the lesson's proof. -/
theorem holomorphic_is_analytic {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} (hf : HolomorphicOn f U)
    (hU : U ∈ 𝓝 z) : AnalyticAt ℂ f z :=
  DifferentiableOn.analyticAt hf hU
-- @endregion

-- @region complex_analysis.inv_no_entire_extension
-- @provenance independent
/-- **`1/z` does not extend to an entire function.** If an entire `g` agreed with `1/z` away from
`0`, then on the unit circle `g = 1/z`, so `∮ g = ∮ dz/z = 2πi`; but Cauchy's theorem says
`∮ g = 0`. (In fact no holomorphic function on any punctured disc around `0` with a
non-removable singularity extends: Riemann's removable singularity theorem says boundedness near
the point is exactly what is needed, and `1/z` is unbounded.) -/
theorem inv_no_entire_extension :
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ≠ 0, g z = z⁻¹ := by
  rintro ⟨g, hg, hgz⟩
  have h0 : (∮ z in C(0, 1), g z) = 0 := cauchy_theorem_disc zero_le_one hg.differentiableOn
  have hcongr : (∮ z in C(0, 1), g z) = ∮ z in C(0, 1), (z - 0)⁻¹ := by
    apply circleIntegral.integral_congr zero_le_one
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, mem_sphere, dist_self] at hz
      exact zero_ne_one hz
    simp [hgz z hz0]
  have h1 : (∮ z in C(0, 1), (z - 0)⁻¹) = 2 * (Real.pi : ℂ) * I :=
    circle_integral_inv (by simp)
  rw [hcongr, h1] at h0
  simp [I_ne_zero] at h0
-- @endregion

/-! ### Liouville's theorem and the fundamental theorem of algebra -/

-- @region complex_analysis.cauchy_estimate
-- @provenance library
/-- **Cauchy's estimate.** If `f` is holomorphic on the disc `|z - c| < R`, continuous up to the
boundary, and `|f| ≤ C` on the circle `|z - c| = R`, then `|f'(c)| ≤ C / R`. This applies
Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`; on paper it is one line from the
Cauchy integral formula for `f'`. -/
theorem cauchy_estimate {f : ℂ → ℂ} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R :=
  norm_deriv_le_of_forall_mem_sphere_norm_le hR hf hC
-- @endregion

-- @region complex_analysis.liouville_from_cauchy_estimate
-- @provenance independent
/-- **Liouville's theorem, from the Cauchy estimate.** A bounded entire function is constant. If
`|f| ≤ M` everywhere, the Cauchy estimate on a circle of radius `R` around any `c` gives
`|f'(c)| ≤ M / R`; letting `R → ∞` forces `f'(c) = 0`. A function with zero derivative
everywhere on the connected set `ℂ` is constant. (Concretely: if `d = |f'(c)| > 0`, the radius
`R = (M + 1)/d` gives `d ≤ M d /(M + 1) < d`.) -/
theorem liouville_from_cauchy_estimate {f : ℂ → ℂ} (hf : Differentiable ℂ f) {M : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (z w : ℂ) : f z = f w := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hderiv : ∀ c, deriv f c = 0 := by
    intro c
    by_contra hne
    set d := ‖deriv f c‖ with hd
    have hdpos : 0 < d := norm_pos_iff.mpr hne
    have hR : 0 < (M + 1) / d := by positivity
    have key : d ≤ M / ((M + 1) / d) :=
      cauchy_estimate hR hf.diffContOnCl (fun z _ => hM z)
    rw [div_div_eq_mul_div, le_div_iff₀ (by linarith)] at key
    nlinarith
  exact is_const_of_deriv_eq_zero hf hderiv z w
-- @endregion

-- @region complex_analysis.liouville_library
-- @provenance library
/-- Liouville's theorem as stated in Mathlib: a complex-differentiable function with bounded range
is constant. This applies `Differentiable.apply_eq_apply_of_bounded` (which allows any complex
normed spaces as domain and target). -/
theorem liouville_library {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (range f)) (z w : ℂ) : f z = f w :=
  hf.apply_eq_apply_of_bounded hb z w
-- @endregion

-- @region complex_analysis.fta_from_liouville
-- @provenance independent
/-- **The fundamental theorem of algebra, from Liouville's theorem.** Let `p` be a non-constant
complex polynomial and suppose it has no root. Then `1/p` is entire, and `|p(z)| → ∞` as
`|z| → ∞`, so `1/p(z) → 0`. An entire function with limit `0` at infinity is bounded, hence
constant (Liouville), hence identically `0` — but `1/p(z)` is never `0`. Contradiction. -/
theorem fta_from_liouville (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z, p.eval z = 0 := by
  by_contra hroot
  push Not at hroot
  -- `1/p` is entire, because `p` never vanishes.
  have hdiff : Differentiable ℂ (fun z => (p.eval z)⁻¹) := p.differentiable.inv hroot
  -- `|p(z)| → ∞` as `|z| → ∞`, so `1/p(z) → 0` at infinity.
  have htend : Tendsto (fun z => (p.eval z)⁻¹) (cocompact ℂ) (𝓝 0) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
      simpa only [tendsto_norm_atTop_iff_cobounded]
        using p.tendsto_norm_atTop hp tendsto_norm_cobounded_atTop)
  -- Liouville: an entire function tending to `0` at infinity is identically `0`.
  have hzero : (p.eval 0)⁻¹ = 0 := hdiff.apply_eq_of_tendsto_cocompact 0 htend
  exact inv_ne_zero (hroot 0) hzero
-- @endregion

-- @region complex_analysis.fta_library
-- @provenance library
/-- The fundamental theorem of algebra in Mathlib: `Complex.exists_root`. Mathlib also records
the consequence that `ℂ` is algebraically closed (`Complex.isAlgClosed`), so every complex
polynomial splits into linear factors. -/
theorem fta_library {p : Polynomial ℂ} (hp : 0 < p.degree) : ∃ z, p.IsRoot z :=
  Complex.exists_root hp
-- @endregion

/-! ### A real integral that residues evaluate -/

-- @region complex_analysis.integral_inv_one_add_sq
-- @provenance library
/-- `∫_{-∞}^{∞} dx / (1 + x²) = π`. The lesson evaluates this by residues (`2πi` times the residue
`1/(2i)` of `1/(1 + z²)` at `i`); Mathlib proves it with the real antiderivative `arctan`, in
`integral_univ_inv_one_add_sq`. Two proofs of one fact. -/
theorem integral_inv_one_add_sq : ∫ x : ℝ, (1 + x ^ 2)⁻¹ = Real.pi :=
  _root_.integral_univ_inv_one_add_sq
-- @endregion

end Lumenary.ComplexAnalysis
