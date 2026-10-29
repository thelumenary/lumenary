/-
The Lumenary — formal mathematics
Smooth manifolds: stereographic charts on spheres and their smooth transition map, the regular
value computation that makes the orthogonal group a manifold, the chain rule as functoriality of
the tangent map, and the first de Rham cohomology of the circle, computed through periodic
functions.

What is proved here and what Mathlib provides. Mathlib builds manifolds exactly as the lesson
does: a `ChartedSpace H M` is an atlas, `IsManifold I n M` says the transition maps are `Cⁿ`
(with `ω` meaning analytic), `mfderiv` is the derivative of a map between manifolds and
`TangentBundle I M` its tangent bundle. Mathlib proves that the unit sphere in Euclidean space is
an analytic manifold, with stereographic charts; we cite that instance. The *independent*
declarations prove from first principles the facts the lesson's hand computations rest on: the
inverse stereographic projection lands on the sphere, the transition map between the two charts
is the inversion `u ↦ u / ‖u‖²`, which is smooth and is its own inverse; the derivative of
`A ↦ AᵀA` at an orthogonal matrix is onto the symmetric matrices; and a continuous periodic
function is the derivative of a periodic function exactly when its integral over a period
vanishes, which is the statement `H¹_dR(S¹) ≅ ℝ` written in the coordinate `θ`.

Not formalised here: the regular value theorem in general (it needs the implicit function theorem
on manifolds, which Mathlib has only in pieces), Stokes's theorem on manifolds (Mathlib has the
divergence theorem on boxes, not yet on manifolds with boundary), differential forms on manifolds,
and de Rham's theorem.
-/
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Lumenary.SmoothManifolds

open scoped Manifold Matrix ContDiff

/-! ### Stereographic charts on the sphere -/

section Stereographic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- @region smooth_manifolds.stereo_inv_north
-- @provenance definition
/-- **Inverse stereographic projection from the north pole.** The point `u` of the equatorial
space `E` is sent to the point `(x, t) ∈ E × ℝ` where the line from the north pole `(0, 1)`
through `(u, 0)` meets the unit sphere again:
`x = 2u / (‖u‖² + 1)`, `t = (‖u‖² - 1) / (‖u‖² + 1)`. -/
noncomputable def stereoInvNorth (u : E) : E × ℝ :=
  ((2 / (‖u‖ ^ 2 + 1)) • u, (‖u‖ ^ 2 - 1) / (‖u‖ ^ 2 + 1))
-- @endregion

-- @region smooth_manifolds.stereo_inv_north_mem_sphere
-- @provenance independent
/-- The inverse stereographic projection really lands on the unit sphere `‖x‖² + t² = 1`.
With `r = ‖u‖²` the claim is `4r + (r - 1)² = (r + 1)²`, an identity of polynomials. -/
theorem stereoInvNorth_mem_sphere (u : E) :
    ‖(stereoInvNorth u).1‖ ^ 2 + (stereoInvNorth u).2 ^ 2 = 1 := by
  have hpos : (0 : ℝ) < ‖u‖ ^ 2 + 1 := by positivity
  simp only [stereoInvNorth, norm_smul, Real.norm_eq_abs, abs_div, abs_two,
    abs_of_pos hpos, mul_pow, div_pow]
  field_simp
  ring
-- @endregion

-- @region smooth_manifolds.stereo_south
-- @provenance definition
/-- **Stereographic projection from the south pole** `(0, -1)`: the point `(x, t)` of the sphere
(with `t ≠ -1`) is sent to `x / (1 + t)`, where the line from the south pole through `(x, t)`
meets the equatorial space. -/
noncomputable def stereoSouth (p : E × ℝ) : E :=
  (1 / (1 + p.2)) • p.1
-- @endregion

-- @region smooth_manifolds.inversion
-- @provenance definition
/-- The **inversion** `u ↦ u / ‖u‖²` in the unit sphere of `E`, defined on `E ∖ {0}`. -/
noncomputable def inversion (u : E) : E :=
  (‖u‖ ^ 2)⁻¹ • u
-- @endregion

-- @region smooth_manifolds.transition_map
-- @provenance independent
/-- **The transition map between the two stereographic charts is the inversion.** For `u ≠ 0`,
going up to the sphere by the north chart and down again by the south chart gives
`u / ‖u‖²`. This is the computation in the lesson:
`(2u/(r+1)) / (1 + (r-1)/(r+1)) = (2u/(r+1)) / (2r/(r+1)) = u/r`, with `r = ‖u‖²`. -/
theorem transition_map {u : E} (hu : u ≠ 0) :
    stereoSouth (stereoInvNorth u) = inversion u := by
  have hr : ‖u‖ ^ 2 ≠ 0 := by positivity
  have hpos : ‖u‖ ^ 2 + 1 ≠ 0 := by positivity
  simp only [stereoSouth, stereoInvNorth, inversion, smul_smul]
  congr 1
  field_simp
  ring
-- @endregion

-- @region smooth_manifolds.inversion_inversion
-- @provenance independent
/-- The inversion is its own inverse on `E ∖ {0}`: `‖u / ‖u‖²‖ = 1/‖u‖`, so inverting again
multiplies by `‖u‖²` and returns `u`. So the transition map is a bijection of `E ∖ {0}`, as the
transition map between two charts must be. -/
theorem inversion_inversion {u : E} (hu : u ≠ 0) : inversion (inversion u) = u := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have key : ((‖(‖u‖ ^ 2)⁻¹ • u‖ ^ 2)⁻¹ * (‖u‖ ^ 2)⁻¹ : ℝ) = 1 := by
    rw [norm_smul, norm_inv, norm_pow, norm_norm]
    field_simp
  simp only [inversion, smul_smul, key, one_smul]
-- @endregion

-- @region smooth_manifolds.inversion_smooth
-- @provenance independent
/-- The transition map is **smooth** (`C^∞`) on `E ∖ {0}`: it is the product of the smooth
function `u ↦ (‖u‖²)⁻¹` (smooth where `‖u‖² ≠ 0`) and the identity. Together with
`transition_map` this is what makes the two stereographic charts a smooth atlas. -/
theorem inversion_smooth : ContDiffOn ℝ ∞ (inversion (E := E)) {u | u ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞ (fun u : E => (‖u‖ ^ 2)⁻¹) {u | u ≠ 0} :=
    (contDiff_norm_sq ℝ).contDiffOn.inv fun u hu => by
      have : u ≠ 0 := hu
      positivity
  exact h1.smul contDiffOn_id
-- @endregion

end Stereographic

-- @region smooth_manifolds.sphere_is_manifold
-- @provenance library
/-- **The `n`-sphere is a smooth manifold** (indeed analytic: `ω`), modelled on `ℝⁿ`, with the
stereographic charts. This is Mathlib's instance `EuclideanSpace.instIsManifoldSphere`. -/
theorem sphere_is_manifold (n : ℕ) :
    IsManifold (𝓡 n) ω (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  inferInstance
-- @endregion

/-! ### The orthogonal group as a regular level set -/

section Orthogonal

variable {n : Type*} [Fintype n]

-- @region smooth_manifolds.gram_expansion
-- @provenance independent
/-- Expanding `F(A) = AᵀA` along the line `A + tH`:
`(A + tH)ᵀ(A + tH) = AᵀA + t(AᵀH + HᵀA) + t²HᵀH`. The coefficient of `t` is the derivative
`dF_A(H) = AᵀH + HᵀA`. -/
theorem gram_expansion (A H : Matrix n n ℝ) (t : ℝ) :
    (A + t • H)ᵀ * (A + t • H) = Aᵀ * A + t • (Aᵀ * H + Hᵀ * A) + t ^ 2 • (Hᵀ * H) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, pow_two]
  abel
-- @endregion

-- @region smooth_manifolds.orthogonal_regular_value
-- @provenance independent
/-- **The identity is a regular value of `A ↦ AᵀA`.** At an orthogonal matrix `A`, the derivative
`H ↦ AᵀH + HᵀA` maps onto the symmetric matrices: for symmetric `S`, the matrix `H = ½ A S` is a
preimage, because `Aᵀ(½AS) + (½AS)ᵀA = ½S + ½SᵀAᵀA = S`. By the regular value theorem,
`O(n) = F⁻¹(I)` is a manifold of dimension `n² - n(n+1)/2 = n(n-1)/2`. -/
theorem orthogonal_regular_value [DecidableEq n] {A S : Matrix n n ℝ} (hA : Aᵀ * A = 1) (hS : Sᵀ = S) :
    Aᵀ * ((1 / 2 : ℝ) • (A * S)) + ((1 / 2 : ℝ) • (A * S))ᵀ * A = S := by
  rw [Matrix.transpose_smul, Matrix.transpose_mul, hS, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_assoc, hA, Matrix.mul_assoc, hA, Matrix.one_mul, Matrix.mul_one, ← add_smul]
  norm_num
-- @endregion

end Orthogonal

/-! ### The chain rule: the tangent map is a functor -/

-- @region smooth_manifolds.chain_rule
-- @provenance library
/-- **The chain rule on manifolds**: the tangent map of a composite is the composite of the
tangent maps, `T(g ∘ f) = Tg ∘ Tf`. In the language of categories, `T` is a functor. This is
Mathlib's `mfderiv_comp`. -/
theorem chain_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
    {f : M → M'} {g : M' → M''} (x : M)
    (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) :=
  mfderiv_comp x hg hf
-- @endregion

/-! ### de Rham cohomology of the circle, in the coordinate θ

A 1-form on the circle `ℝ/Tℤ` is `f(θ) dθ` with `f` continuous and `T`-periodic; it is exact
when `f = g'` for a `T`-periodic `g`. Every 1-form on a 1-manifold is closed. -/

section Circle

-- @region smooth_manifolds.exact_integral_zero
-- @provenance independent
/-- **Exact forms have zero period.** If `g` is `T`-periodic with continuous derivative `f`, then
`∫₀ᵀ f = g(T) - g(0) = 0`, by the fundamental theorem of calculus. -/
theorem exact_integral_zero {T : ℝ} {f g : ℝ → ℝ} (hg : Function.Periodic g T)
    (hderiv : ∀ x, HasDerivAt g (f x) x) (hf : Continuous f) :
    ∫ x in (0 : ℝ)..T, f x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hf.intervalIntegrable 0 T)]
  have := hg 0
  rw [zero_add] at this
  rw [this, sub_self]
-- @endregion

-- @region smooth_manifolds.dtheta_not_exact
-- @provenance independent
/-- **`dθ` is closed but not exact on the circle.** There is no `2π`-periodic function `g` with
`g' = 1`: its integral over a period would be `0`, but `∫₀^{2π} 1 dθ = 2π`. -/
theorem dtheta_not_exact :
    ¬ ∃ g : ℝ → ℝ, Function.Periodic g (2 * Real.pi) ∧ ∀ x, HasDerivAt g 1 x := by
  rintro ⟨g, hg, hderiv⟩
  have h := exact_integral_zero (f := fun _ => (1 : ℝ)) hg hderiv continuous_const
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h
  exact Real.pi_ne_zero (by linarith)
-- @endregion

-- @region smooth_manifolds.primitive_periodic
-- @provenance independent
/-- **Forms with zero period are exact.** If `f` is continuous and `T`-periodic with
`∫₀ᵀ f = 0`, then `G(x) = ∫₀ˣ f` is `T`-periodic (because `∫ₓ^{x+T} f` does not depend on `x`)
and `G' = f` (the fundamental theorem of calculus). -/
theorem primitive_periodic {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f T) (hzero : ∫ x in (0 : ℝ)..T, f x = 0) :
    Function.Periodic (fun x => ∫ t in (0 : ℝ)..x, f t) T ∧
      ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f x) x := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hsplit : ∫ t in (0 : ℝ)..x + T, f t = (∫ t in (0 : ℝ)..x, f t) + ∫ t in x..x + T, f t :=
      (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)).symm
    have hshift : ∫ t in x..x + T, f t = ∫ t in (0 : ℝ)..0 + T, f t :=
      hper.intervalIntegral_add_eq x 0
    simp only
    rw [hsplit, hshift, zero_add, hzero, add_zero]
  · exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
-- @endregion

-- @region smooth_manifolds.de_rham_circle
-- @provenance independent
/-- **`H¹_dR(S¹) ≅ ℝ`, via the period.** A continuous `T`-periodic `f` (a 1-form `f dθ` on the
circle) is the derivative of a `T`-periodic function (is exact) **if and only if** its period
`∫₀ᵀ f` vanishes. So the linear map "integrate over the circle" from closed 1-forms to `ℝ` has
kernel exactly the exact forms; it is onto (the constant `1` has period `T`), so for `T ≠ 0` it
induces an isomorphism `H¹_dR(S¹) ≅ ℝ`. -/
theorem de_rham_circle {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hper : Function.Periodic f T) :
    (∃ g : ℝ → ℝ, Function.Periodic g T ∧ ∀ x, HasDerivAt g (f x) x) ↔
      ∫ x in (0 : ℝ)..T, f x = 0 := by
  constructor
  · rintro ⟨g, hg, hderiv⟩
    exact exact_integral_zero hg hderiv hf
  · intro hzero
    exact ⟨_, primitive_periodic hf hper hzero⟩
-- @endregion

end Circle

end Lumenary.SmoothManifolds
