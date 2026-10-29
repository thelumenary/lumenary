/-
The Lumenary — formal mathematics
Differential forms and Stokes' theorem: the wedge product of 1-forms, `d ∘ d = 0`, the
fundamental theorem of calculus and Green's theorem as cases of Stokes, and the angle form
`dθ = (x dy - y dx)/(x² + y²)` on the punctured plane, which is closed but not exact.

What is proved here and what Mathlib provides. Mathlib has the exterior algebra
(`ExteriorAlgebra`), differential forms on normed spaces as maps into continuous alternating
maps, the exterior derivative `extDeriv` with the theorem `extDeriv_extDeriv` (`d ∘ d = 0`),
symmetry of second derivatives, the fundamental theorem of calculus, and the divergence theorem
on rectangles. It does not yet have integration of forms over manifolds or the general Stokes
theorem. The *library* declarations cite these results. The *independent* declarations prove:
the algebra of the wedge product of two 1-forms (antisymmetry, `α ∧ α = 0`, and `dx ∧ dy` as
signed area), that `dθ` is closed, that its integral around the unit circle is `2π`, and — the
main theorem — that `dθ` is **not exact** on the punctured plane: no function `f` has
`df = dθ` there.
-/
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

namespace Lumenary.DifferentialForms

open Real

/-! ### The wedge product of 1-forms -/

-- @region differential_forms.wedge
-- @provenance definition
/-- The **wedge product** of two 1-forms (linear functionals) `α, β` on a real vector space: the
alternating bilinear form `(α ∧ β)(u, v) = α(u) β(v) - α(v) β(u)`. -/
def wedge {E : Type*} [AddCommGroup E] [Module ℝ E] (α β : E →ₗ[ℝ] ℝ) (u v : E) : ℝ :=
  α u * β v - α v * β u
-- @endregion

-- @region differential_forms.wedge_antisymm
-- @provenance independent
/-- **The wedge product of 1-forms is anticommutative**: `α ∧ β = -(β ∧ α)`. (For a `k`-form and an
`l`-form the rule is `α ∧ β = (-1)^(kl) β ∧ α`.) -/
theorem wedge_antisymm {E : Type*} [AddCommGroup E] [Module ℝ E] (α β : E →ₗ[ℝ] ℝ) (u v : E) :
    wedge α β u v = -wedge β α u v := by
  unfold wedge
  ring
-- @endregion

-- @region differential_forms.wedge_self
-- @provenance independent
/-- Consequently `α ∧ α = 0` for every 1-form `α`. -/
theorem wedge_self {E : Type*} [AddCommGroup E] [Module ℝ E] (α : E →ₗ[ℝ] ℝ) (u v : E) :
    wedge α α u v = 0 := by
  unfold wedge
  ring
-- @endregion

-- @region differential_forms.wedge_alternating
-- @provenance independent
/-- `α ∧ β` is **alternating**: it vanishes when both arguments are equal. -/
theorem wedge_alternating {E : Type*} [AddCommGroup E] [Module ℝ E] (α β : E →ₗ[ℝ] ℝ) (u : E) :
    wedge α β u u = 0 := by
  unfold wedge
  ring
-- @endregion

-- @region differential_forms.dx_wedge_dy
-- @provenance independent
/-- On `ℝ²`, `dx ∧ dy` evaluated on two vectors is the determinant `u₁ v₂ - u₂ v₁`: the **signed
area** of the parallelogram they span. Here `dx` and `dy` are the coordinate projections. -/
theorem dx_wedge_dy (u v : ℝ × ℝ) :
    wedge (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ) u v = u.1 * v.2 - u.2 * v.1 := by
  simp only [wedge, LinearMap.fst_apply, LinearMap.snd_apply]
  ring
-- @endregion

-- @region differential_forms.exterior_anticomm
-- @provenance library
/-- In Mathlib's **exterior algebra** of a module `M`, vectors anticommute: `x ∧ y + y ∧ x = 0`.
This applies Mathlib's `ExteriorAlgebra.ι_add_mul_swap`. -/
theorem exterior_anticomm {M : Type*} [AddCommGroup M] [Module ℝ M] (x y : M) :
    ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y + ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ x
      = 0 :=
  ExteriorAlgebra.ι_add_mul_swap x y
-- @endregion

/-! ### `d ∘ d = 0` -/

-- @region differential_forms.mixed_partials_commute
-- @provenance library
/-- **Mixed partial derivatives commute** for a `C²` function on `ℝ²` (Schwarz–Clairaut). In
coordinates `d(df) = (∂²f/∂x∂y - ∂²f/∂y∂x) dx ∧ dy`, so this is `d(df) = 0` for functions. This
applies Mathlib's `ContDiffAt.isSymmSndFDerivAt`. -/
theorem mixed_partials_commute (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hf : ContDiffAt ℝ 2 f p) :
    fderiv ℝ (fderiv ℝ f) p (1, 0) (0, 1) = fderiv ℝ (fderiv ℝ f) p (0, 1) (1, 0) :=
  hf.isSymmSndFDerivAt (by simp) _ _
-- @endregion

-- @region differential_forms.d_squared_zero
-- @provenance library
/-- **`d ∘ d = 0`** for every `C²` differential `n`-form `ω` on a normed space (with values in a
normed space). Mathlib represents an `n`-form as a map `E → E [⋀^Fin n]→L[ℝ] F` to continuous
alternating `n`-linear maps. This applies Mathlib's `extDeriv_extDeriv`. -/
theorem d_squared_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (hω : ContDiff ℝ 2 ω) : extDeriv (extDeriv ω) = 0 :=
  extDeriv_extDeriv hω (by simp)
-- @endregion

/-! ### Stokes' theorem in dimensions one and two -/

-- @region differential_forms.stokes_interval
-- @provenance library
/-- **Stokes' theorem on an interval is the fundamental theorem of calculus**: `∫_[a,b] df =
f(b) - f(a)`, the integral of `df` over `[a, b]` equals the "integral" of `f` over the oriented
boundary `{b} - {a}`. This applies Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem stokes_interval (f f' : ℝ → ℝ) (a b : ℝ)
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
    ∫ x in a..b, f' x = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
-- @endregion

-- @region differential_forms.stokes_rectangle
-- @provenance library
/-- **Stokes' theorem on a rectangle** (Green's theorem in divergence form): for the 1-form
`ω = f dy - g dx`, `dω = (∂f/∂x + ∂g/∂y) dx ∧ dy`, and `∬_R dω = ∮_∂R ω` becomes the identity
below — the integral of `f' (1, 0) + g' (0, 1)` over the rectangle equals the boundary terms. This
applies Mathlib's `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`. -/
theorem stokes_rectangle (f g : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (a₁ a₂ b₁ b₂ : ℝ)
    (Hcf : ContinuousOn f (Set.uIcc a₁ b₁ ×ˢ Set.uIcc a₂ b₂))
    (Hcg : ContinuousOn g (Set.uIcc a₁ b₁ ×ˢ Set.uIcc a₂ b₂))
    (Hdf : ∀ x ∈ Set.Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Set.Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Set.Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Set.Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt g (g' x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1))
      (Set.uIcc a₁ b₁ ×ˢ Set.uIcc a₂ b₂)) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) :=
  MeasureTheory.integral2_divergence_prod_of_hasFDerivAt f g f' g' a₁ a₂ b₁ b₂ Hcf Hcg Hdf Hdg Hi
-- @endregion

/-! ### The angle form `dθ` on the punctured plane -/

-- @region differential_forms.d_theta
-- @provenance definition
/-- The **angle form** `dθ = (x dy - y dx) / (x² + y²)` on `ℝ² ∖ {0}`: at each point `p = (x, y)`,
a linear functional on vectors. (It is not the differential of a global function `θ` — that is
the point of `dTheta_not_exact`.) -/
noncomputable def dTheta (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (p.1 / (p.1 ^ 2 + p.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ -
    (p.2 / (p.1 ^ 2 + p.2 ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ
-- @endregion

-- @region differential_forms.d_theta_closed
-- @provenance independent
/-- **`dθ` is closed.** Writing `dθ = P dx + Q dy` with `P = -y/(x² + y²)` and `Q = x/(x² + y²)`,
we have `dθ' = (∂Q/∂x - ∂P/∂y) dx ∧ dy`, and both partial derivatives equal
`(y² - x²)/(x² + y²)²` away from the origin. -/
theorem dTheta_closed (x y : ℝ) (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun x => x / (x ^ 2 + y ^ 2)) ((y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2) x ∧
      HasDerivAt (fun y => -y / (x ^ 2 + y ^ 2)) ((y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2) y := by
  constructor
  · have hd : HasDerivAt (fun x => x ^ 2 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
    convert (hasDerivAt_id' x).div hd h using 1
    field_simp
    ring
  · have hd : HasDerivAt (fun y => x ^ 2 + y ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (x ^ 2)
    convert (hasDerivAt_neg y).div hd h using 1
    field_simp
    ring
-- @endregion

-- @region differential_forms.circle_path
-- @provenance independent
/-- The unit circle `γ(t) = (cos t, sin t)` has velocity `γ'(t) = (-sin t, cos t)`. -/
theorem circle_path (t : ℝ) : HasDerivAt (fun t => (cos t, sin t)) (-sin t, cos t) t :=
  (hasDerivAt_cos t).prodMk (hasDerivAt_sin t)
-- @endregion

-- @region differential_forms.d_theta_on_circle
-- @provenance independent
/-- **The pullback of `dθ` to the circle is `dt`**: `dθ_{γ(t)}(γ'(t)) = cos t · cos t - sin t · (-sin t)
= 1`, using `cos² t + sin² t = 1`. -/
theorem dTheta_on_circle (t : ℝ) : dTheta (cos t, sin t) (-sin t, cos t) = 1 := by
  have h := cos_sq_add_sin_sq t
  simp only [dTheta, h, div_one]
  simp
  linear_combination h
-- @endregion

-- @region differential_forms.d_theta_circle_integral
-- @provenance independent
/-- **`∮ dθ = 2π` around the unit circle**: pull back along `γ(t) = (cos t, sin t)` and integrate
the constant `1` over `[0, 2π]`. -/
theorem dTheta_circle_integral :
    ∫ t in (0 : ℝ)..2 * π, dTheta (cos t, sin t) (-sin t, cos t) = 2 * π := by
  simp only [dTheta_on_circle, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
-- @endregion

-- @region differential_forms.d_theta_not_exact
-- @provenance independent
/-- **`dθ` is closed but not exact.** There is no differentiable function `f` on the punctured plane
with `df = dθ`. If there were, `g(t) = f(cos t, sin t)` would satisfy `g'(t) = dθ(γ'(t)) = 1` by
the chain rule, so `g(t) - t` would be constant; but `g(2π) = g(0)` because the circle closes up,
which would force `2π = 0`. -/
theorem dTheta_not_exact :
    ¬ ∃ f : ℝ × ℝ → ℝ, ∀ p : ℝ × ℝ, p ≠ 0 → HasFDerivAt f (dTheta p) p := by
  rintro ⟨f, hf⟩
  have hne : ∀ t : ℝ, ((cos t, sin t) : ℝ × ℝ) ≠ 0 := by
    intro t h0
    have h1 : cos t = 0 := congrArg Prod.fst h0
    have h2 : sin t = 0 := congrArg Prod.snd h0
    have := cos_sq_add_sin_sq t
    rw [h1, h2] at this
    norm_num at this
  -- `g(t) - t` has derivative `0` everywhere.
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t => f (cos t, sin t) - t) 0 t := by
    intro t
    have hg := (hf _ (hne t)).comp_hasDerivAt t (circle_path t)
    rw [dTheta_on_circle] at hg
    have h2 := hg.sub (hasDerivAt_id' t)
    rw [sub_self] at h2
    exact h2
  have hconst := is_const_of_deriv_eq_zero
    (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) (2 * π) 0
  simp only [cos_two_pi, sin_two_pi, cos_zero, sin_zero, sub_zero] at hconst
  have : (2 : ℝ) * π = 0 := by linarith
  exact (mul_ne_zero two_ne_zero pi_ne_zero) this
-- @endregion

end Lumenary.DifferentialForms
