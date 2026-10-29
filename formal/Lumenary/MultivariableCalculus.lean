/-
The Lumenary — formal mathematics
Multivariable and vector calculus: the derivative as a linear map, directional derivatives and
the gradient, a function with partial derivatives that is not differentiable, the gradient
theorem for line integrals, Lagrange multipliers, change of variables in polar coordinates,
the Gaussian integral, Green's theorem on a rectangle, and the vortex field.

What is proved here and what Mathlib provides. Mathlib's derivative of `f : E → F` between
normed spaces is the Fréchet derivative `HasFDerivAt f f' x`, with `f' : E →L[ℝ] F` a continuous
linear map — exactly the lesson's "derivative as a linear map". The *independent* declarations
re-prove lesson results from basic library facts: directional derivatives from the chain rule,
the steepest-ascent property of the gradient, the counterexample `xy/(x² + y²)`, the gradient
theorem, a constrained maximum, and the curl and circulation of the vortex field. The *library*
declarations cite Mathlib's chain rule, Lagrange multiplier theorem, symmetry of second
derivatives, polar change of variables, Gaussian integral and divergence theorem on rectangles.
-/
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

namespace Lumenary.MultivariableCalculus

open Set Filter Topology Real MeasureTheory

/-! ### The derivative as a linear map -/

-- @region multivariable_calculus.chain_rule
-- @provenance library
/-- **The chain rule**: `D(g ∘ f)(a) = Dg(f(a)) ∘ Df(a)`, a composite of linear maps (in
coordinates, a product of Jacobian matrices). This applies Mathlib's `HasFDerivAt.comp`. -/
theorem chain_rule {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {f' : E →L[ℝ] F} {g' : F →L[ℝ] G} {a : E}
    (hf : HasFDerivAt f f' a) (hg : HasFDerivAt g g' (f a)) :
    HasFDerivAt (g ∘ f) (g'.comp f') a :=
  hg.comp a hf
-- @endregion

-- @region multivariable_calculus.directional_deriv
-- @provenance independent
/-- If `f` is differentiable at `a` with derivative `f'`, then the directional derivative of `f`
at `a` in the direction `v` exists and equals `f' v`: the derivative of `t ↦ f (a + t v)` at
`t = 0`. Proof: the line `γ t = a + t v` has velocity `v`, and the chain rule
(`HasFDerivAt.comp_hasDerivAt`) gives `(f ∘ γ)'(0) = f'(γ'(0)) = f' v`. -/
theorem directional_deriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasFDerivAt f f' a) (v : E) :
    HasDerivAt (fun t : ℝ => f (a + t • v)) (f' v) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have hf0 : HasFDerivAt f f' (a + (0 : ℝ) • v) := by simpa using hf
  exact hf0.comp_hasDerivAt (x := (0 : ℝ)) hγ
-- @endregion

-- @region multivariable_calculus.steepest_ascent
-- @provenance independent
/-- **The gradient points uphill fastest.** For a unit vector `v`, the directional derivative
`⟪∇f, v⟫` is at most `‖∇f‖` (Cauchy–Schwarz, `real_inner_le_norm`), and the value `‖∇f‖` is
attained in the direction `∇f / ‖∇f‖` when `∇f ≠ 0`. -/
theorem steepest_ascent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g v : E) (hv : ‖v‖ = 1) :
    inner ℝ g v ≤ ‖g‖ ∧ (g ≠ 0 → inner ℝ g (‖g‖⁻¹ • g) = ‖g‖) := by
  constructor
  · calc inner ℝ g v ≤ ‖g‖ * ‖v‖ := real_inner_le_norm g v
      _ = ‖g‖ := by rw [hv, mul_one]
  · intro hg
    have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
-- @endregion

-- @region multivariable_calculus.gradient_directional
-- @provenance independent
/-- With a gradient: if `f : E → ℝ` has gradient `∇f(a) = g` (Mathlib's `HasGradientAt`), the
directional derivative in direction `v` is the inner product `⟪g, v⟫`. This combines
`directional_deriv` with `hasGradientAt_iff_hasFDerivAt`: the derivative is `v ↦ ⟪g, v⟫`. -/
theorem gradient_directional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {g a : E} (hf : HasGradientAt f g a) (v : E) :
    HasDerivAt (fun t : ℝ => f (a + t • v)) (inner ℝ g v) 0 := by
  have := directional_deriv (hasGradientAt_iff_hasFDerivAt.mp hf) v
  simpa using this
-- @endregion

/-! ### Partial derivatives do not imply differentiability -/

-- @region multivariable_calculus.xy_quot
-- @provenance definition
/-- The standard counterexample `f(x, y) = xy / (x² + y²)`. At the origin the formula reads
`0 / 0`, which Lean evaluates to `0` (division by zero is `0` in Mathlib), matching the lesson's
convention `f(0, 0) = 0`. -/
noncomputable def xyQuot (p : ℝ × ℝ) : ℝ := p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)
-- @endregion

-- @region multivariable_calculus.xy_quot_partials
-- @provenance independent
/-- Both partial derivatives of `xyQuot` exist at the origin and equal `0`: along each axis the
function is identically zero (`f(t, 0) = 0` and `f(0, t) = 0`), so its derivative there is `0`. -/
theorem xyQuot_partials :
    HasDerivAt (fun t => xyQuot (t, 0)) 0 0 ∧ HasDerivAt (fun t => xyQuot (0, t)) 0 0 := by
  have h1 : (fun t => xyQuot (t, 0)) = fun _ => (0 : ℝ) := by
    funext t; simp [xyQuot]
  have h2 : (fun t => xyQuot (0, t)) = fun _ => (0 : ℝ) := by
    funext t; simp [xyQuot]
  rw [h1, h2]
  exact ⟨hasDerivAt_const 0 0, hasDerivAt_const 0 0⟩
-- @endregion

-- @region multivariable_calculus.xy_quot_not_continuous_at
-- @provenance independent
/-- …but `xyQuot` is not even continuous at the origin: on the diagonal, `f(t, t) = 1/2` for
every `t ≠ 0`, while `f(0, 0) = 0`. If `f` were continuous at `0`, then `f(t, t)` would tend to
`f(0, 0) = 0` as `t → 0`, but it is constantly `1/2` near `0`, so `1/2 = 0`. -/
theorem xyQuot_not_continuousAt : ¬ ContinuousAt xyQuot 0 := by
  intro hc
  -- Restrict to the diagonal `t ↦ (t, t)`.
  have hdiag : ContinuousAt (fun t : ℝ => xyQuot (t, t)) 0 := by
    have hγ : ContinuousAt (fun t : ℝ => ((t, t) : ℝ × ℝ)) 0 :=
      (continuous_id.prodMk continuous_id).continuousAt
    have hc' : ContinuousAt xyQuot ((0 : ℝ), (0 : ℝ)) := hc
    exact ContinuousAt.comp (g := xyQuot) (f := fun t : ℝ => ((t, t) : ℝ × ℝ)) hc' hγ
  have hlim0 : Tendsto (fun t : ℝ => xyQuot (t, t)) (𝓝[≠] 0) (𝓝 0) := by
    have := hdiag.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simpa [xyQuot] using this
  have hlimhalf : Tendsto (fun t : ℝ => xyQuot (t, t)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    have : t ^ 2 + t ^ 2 ≠ 0 := by positivity
    simp only [xyQuot]
    field_simp
    ring
  have := tendsto_nhds_unique hlim0 hlimhalf
  norm_num at this
-- @endregion

-- @region multivariable_calculus.xy_quot_not_differentiable_at
-- @provenance independent
/-- Hence `xyQuot` is not differentiable at the origin, although both partial derivatives exist
there: differentiability implies continuity (`DifferentiableAt.continuousAt`). -/
theorem xyQuot_not_differentiableAt : ¬ DifferentiableAt ℝ xyQuot 0 :=
  fun h => xyQuot_not_continuousAt h.continuousAt
-- @endregion

-- @region multivariable_calculus.schwarz
-- @provenance library
/-- **Symmetry of second derivatives** (Schwarz–Clairaut): if `f` is differentiable everywhere and
its derivative `f'` is differentiable at `x` with derivative `f''`, then `f'' v w = f'' w v`; in
coordinates, `∂²f/∂x∂y = ∂²f/∂y∂x`. This applies Mathlib's `second_derivative_symmetric`. -/
theorem schwarz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E → E →L[ℝ] F}
    {f'' : E →L[ℝ] E →L[ℝ] F} {x : E} (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v :=
  second_derivative_symmetric hf hx v w
-- @endregion

/-! ### Line integrals -/

-- @region multivariable_calculus.gradient_theorem
-- @provenance independent
/-- **The gradient theorem** (fundamental theorem for line integrals): for a `C¹` function
`f : E → ℝ` and a `C¹` path `γ`, the line integral of the derivative of `f` along `γ` from
`t = a` to `t = b` is `f (γ b) - f (γ a)`. Proof: by the chain rule `(f ∘ γ)'(t) = Df(γ t)(γ'(t))`,
which is continuous, so the one-variable fundamental theorem applies. -/
theorem gradient_theorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {γ : ℝ → E} (hf : ContDiff ℝ 1 f) (hγ : ContDiff ℝ 1 γ) (a b : ℝ) :
    ∫ t in a..b, fderiv ℝ f (γ t) (deriv γ t) = f (γ b) - f (γ a) := by
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (f ∘ γ) (fderiv ℝ f (γ t) (deriv γ t)) t := by
    intro t _
    have hfd : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) :=
      ((hf.differentiable one_ne_zero) (γ t)).hasFDerivAt
    have hγd : HasDerivAt γ (deriv γ t) t :=
      ((hγ.differentiable one_ne_zero) t).hasDerivAt
    exact hfd.comp_hasDerivAt t hγd
  have hcont : Continuous fun t => fderiv ℝ f (γ t) (deriv γ t) :=
    ((hf.continuous_fderiv one_ne_zero).comp hγ.continuous).clm_apply
      (hγ.continuous_deriv le_rfl)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)]
  rfl
-- @endregion

-- @region multivariable_calculus.closed_loop_zero
-- @provenance independent
/-- Corollary: the line integral of a gradient around a **closed** `C¹` loop (`γ a = γ b`) is
zero. -/
theorem closed_loop_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {γ : ℝ → E} (hf : ContDiff ℝ 1 f) (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hclosed : γ a = γ b) :
    ∫ t in a..b, fderiv ℝ f (γ t) (deriv γ t) = 0 := by
  rw [gradient_theorem hf hγ a b, hclosed, sub_self]
-- @endregion

/-! ### The vortex field: curl zero, circulation 2π -/

-- @region multivariable_calculus.vortex_curl_zero
-- @provenance independent
/-- The vortex field `F = (P, Q) = (-y/(x² + y²), x/(x² + y²))` has zero curl away from the
origin: `∂Q/∂x = (y² - x²)/(x² + y²)² = ∂P/∂y`. Each partial derivative is computed with the
quotient rule in one variable, the other variable held fixed. -/
theorem vortex_curl_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun s => s / (s ^ 2 + y ^ 2)) ((y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2) x ∧
      HasDerivAt (fun s => -s / (x ^ 2 + s ^ 2)) ((y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2) y := by
  constructor
  · have hd : HasDerivAt (fun s => s ^ 2 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
    convert (hasDerivAt_id' x).div hd h using 1
    ring
  · have hd : HasDerivAt (fun s => x ^ 2 + s ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (x ^ 2)
    convert (hasDerivAt_neg' y).div hd h using 1
    ring
-- @endregion

-- @region multivariable_calculus.vortex_circulation
-- @provenance independent
/-- …yet its circulation around the unit circle `γ(t) = (cos t, sin t)`, `0 ≤ t ≤ 2π`, is `2π`:
on the circle `F(γ t) = (-sin t, cos t) = γ'(t)`, so the integrand `F · γ'` is
`sin² t + cos² t = 1`. By the gradient theorem, `F` is therefore not the gradient of any `C¹`
function on the punctured plane (that step is explained in the lesson, not formalised here). -/
theorem vortex_circulation :
    ∫ t in (0 : ℝ)..2 * π,
      ((-sin t / (cos t ^ 2 + sin t ^ 2)) * (-sin t) +
        (cos t / (cos t ^ 2 + sin t ^ 2)) * cos t) = 2 * π := by
  have h : ∀ t : ℝ, (-sin t / (cos t ^ 2 + sin t ^ 2)) * (-sin t) +
      (cos t / (cos t ^ 2 + sin t ^ 2)) * cos t = 1 := by
    intro t
    rw [cos_sq_add_sin_sq]
    have := sin_sq_add_cos_sq t
    simp only [div_one]
    nlinarith [this]
  simp only [h, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
-- @endregion

/-! ### Constrained optimisation -/

-- @region multivariable_calculus.lagrange
-- @provenance library
/-- **Lagrange multipliers** (one constraint): if `φ` has a local extremum at `x₀` on the level
set `{x | f x = f x₀}`, and `f`, `φ` are strictly differentiable at `x₀`, then `f'` and `φ'` are
linearly dependent: `a • f' + b • φ' = 0` with `(a, b) ≠ 0`. When `f' ≠ 0` this forces `b ≠ 0`,
i.e. `∇φ = λ ∇f`. This applies Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`. -/
theorem lagrange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f φ : E → ℝ} {x₀ : E} {f' φ' : StrongDual ℝ E}
    (hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) : ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • f' + b • φ' = 0 :=
  hextr.exists_multipliers_of_hasStrictFDerivAt_1d hf' hφ'
-- @endregion

-- @region multivariable_calculus.circle_max_xy
-- @provenance independent
/-- The answer the multiplier method finds for "maximise `xy` on the circle `x² + y² = 2`":
the maximum is `1`, attained at `(1, 1)`. A certificate: `2xy ≤ x² + y²` because
`(x - y)² ≥ 0`. -/
theorem circle_max_xy :
    (∀ x y : ℝ, x ^ 2 + y ^ 2 = 2 → x * y ≤ 1) ∧ ((1 : ℝ) ^ 2 + 1 ^ 2 = 2 ∧ (1 : ℝ) * 1 = 1) := by
  refine ⟨fun x y h => ?_, by norm_num, by norm_num⟩
  nlinarith [sq_nonneg (x - y)]
-- @endregion

/-! ### Multiple integrals and change of variables -/

-- @region multivariable_calculus.polar_jacobian
-- @provenance library
/-- The Jacobian determinant of polar coordinates `(r, θ) ↦ (r cos θ, r sin θ)` is `r`:
`det [[cos θ, -r sin θ], [sin θ, r cos θ]] = r (cos² θ + sin² θ) = r`. This applies Mathlib's
`det_fderivPolarCoordSymm`. -/
theorem polar_jacobian (p : ℝ × ℝ) : (fderivPolarCoordSymm p).det = p.1 :=
  det_fderivPolarCoordSymm p
-- @endregion

-- @region multivariable_calculus.polar_change_of_variables
-- @provenance library
/-- **Change of variables to polar coordinates**: `∬ f(x, y) dx dy = ∬ f(r cos θ, r sin θ) r dr dθ`,
the integral on the right over `r > 0`, `-π < θ < π`. The factor `r` is the Jacobian
determinant above. This applies Mathlib's `integral_comp_polarCoord_symm`. -/
theorem polar_change_of_variables (f : ℝ × ℝ → ℝ) :
    ∫ p in polarCoord.target, p.1 * f (polarCoord.symm p) = ∫ p, f p := by
  simpa [smul_eq_mul] using integral_comp_polarCoord_symm f
-- @endregion

-- @region multivariable_calculus.gaussian_integral
-- @provenance library
/-- **The Gaussian integral** `∫ e^{-x²} dx = √π` over the whole real line. Mathlib's
`integral_gaussian` proves `∫ e^{-b x²} dx = √(π/b)`, via the square of the integral and polar
coordinates, exactly the lesson's argument; we take `b = 1`. -/
theorem gaussian_integral : ∫ x : ℝ, exp (-x ^ 2) = √π := by
  have := integral_gaussian 1
  simpa using this
-- @endregion

-- @region multivariable_calculus.green_rectangle
-- @provenance library
/-- **Green's theorem on a rectangle**, in its flux (divergence) form: for `F = (f, g)` continuous
on the rectangle `R = [a₁, b₁] × [a₂, b₂]`, differentiable inside, with integrable divergence,
`∬_R (∂f/∂x + ∂g/∂y) = ∮_∂R F · n ds`, written out as four boundary integrals. This applies
Mathlib's `integral_divergence_prod_Icc_of_hasFDerivAt_of_le` (with values in `ℝ`). -/
theorem green_rectangle (f g : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ × ℝ)
    (hle : a ≤ b) (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :=
  integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g f' g' a b hle Hcf Hcg Hdf Hdg Hi
-- @endregion

end Lumenary.MultivariableCalculus
