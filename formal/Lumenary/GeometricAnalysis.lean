/-
The Lumenary — formal mathematics
Geometric analysis: the catenoid and Scherk's surface are minimal, Ricci flow shrinks a round
sphere to a point in finite time, a discrete maximum principle, and the mean value property.

What is proved here. Minimal surfaces: the profile `y = a cosh(x/a)` of the catenoid solves the
Euler–Lagrange equation `y y'' = 1 + y'²` of area for surfaces of revolution, together with its
first integral `y / √(1 + y'²) = a` (`catenary_euler_lagrange`, `catenary_first_integral`);
Scherk's surface `z = log cos y − log cos x` satisfies the minimal surface equation
(`scherk_minimal`). Ricci flow: on a round sphere the flow reduces to an ODE for the squared
radius, which reaches zero at time `r₀²/(2(n−1))` (`round_sphere_ricci_flow`); the reduction
itself (the Ricci tensor of a round sphere) is not formalised. The maximum principle: the explicit
finite-difference heat scheme with ratio `λ ≤ 1/2` never exceeds its initial maximum
(`discrete_max_principle`). Mathlib provides harmonic functions and their mean value property
(`harmonic_mean_value`). Not in Mathlib (as far as we know): mean curvature, minimal surfaces,
the Plateau problem, harmonic maps between manifolds, Ricci curvature or Ricci flow.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Harmonic.MeanValue

namespace Lumenary.GeometricAnalysis

open Real

/-! ### The catenoid -/

-- @region geometric_analysis.catenary_euler_lagrange
-- @provenance independent
/-- **The catenoid is a minimal surface of revolution.** Rotating the graph of `y(x) > 0` about
the `x`-axis gives area `2π ∫ y √(1 + y'²) dx`, whose Euler–Lagrange equation is
`y y'' = 1 + y'²`. The catenary `y = a cosh(x/a)` solves it: `y' = sinh(x/a)`,
`y'' = cosh(x/a)/a`, and `y y'' = cosh²(x/a) = 1 + sinh²(x/a)`. -/
theorem catenary_euler_lagrange (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => a * cosh (x / a)) (sinh (x / a)) x ∧
      HasDerivAt (fun x => sinh (x / a)) (cosh (x / a) / a) x ∧
      a * cosh (x / a) * (cosh (x / a) / a) = 1 + sinh (x / a) ^ 2 := by
  have hdiv : HasDerivAt (fun x : ℝ => x / a) (1 / a) x := by
    simpa using (hasDerivAt_id x).div_const a
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_cosh (x / a)).comp x hdiv).const_mul a
    exact h.congr_deriv (by field_simp)
  · have h := (hasDerivAt_sinh (x / a)).comp x hdiv
    exact h.congr_deriv (by field_simp)
  · field_simp
    linarith [cosh_sq (x / a)]
-- @endregion

-- @region geometric_analysis.catenary_first_integral
-- @provenance independent
/-- **Beltrami's first integral.** The area integrand `L = y √(1 + y'²)` does not depend on `x`, so
`L − y' ∂L/∂y' = y / √(1 + y'²)` is constant along solutions. For the catenary
`y = a cosh(x/a)` it equals `a`, because `√(1 + sinh²) = cosh`. -/
theorem catenary_first_integral (a x : ℝ) :
    a * cosh (x / a) / √(1 + sinh (x / a) ^ 2) = a := by
  have hc : √(1 + sinh (x / a) ^ 2) = cosh (x / a) := by
    rw [← cosh_sq', sqrt_sq (cosh_pos _).le]
  rw [hc, mul_div_assoc, div_self (cosh_pos _).ne', mul_one]
-- @endregion

/-! ### The minimal surface equation and Scherk's surface -/

-- @region geometric_analysis.minimal_surface_eq
-- @provenance definition
/-- The **minimal surface equation** for a graph `z = u(x, y)`, written in terms of its first and
second partial derivatives at a point:
`(1 + u_y²) u_xx − 2 u_x u_y u_xy + (1 + u_x²) u_yy = 0`. It says the mean curvature of the graph
vanishes; it is the Euler–Lagrange equation of the area `∬ √(1 + u_x² + u_y²) dx dy`. -/
def MinimalSurfaceEq (ux uy uxx uxy uyy : ℝ) : Prop :=
  (1 + uy ^ 2) * uxx - 2 * ux * uy * uxy + (1 + ux ^ 2) * uyy = 0
-- @endregion

-- @region geometric_analysis.scherk
-- @provenance definition
/-- **Scherk's first surface** (1834), the graph of `u(x, y) = log cos y − log cos x` over the
square `|x|, |y| < π/2`. -/
noncomputable def scherk (x y : ℝ) : ℝ := log (cos y) - log (cos x)
-- @endregion

-- @region geometric_analysis.scherk_minimal
-- @provenance independent
/-- **Scherk's surface is minimal.** On the open square (where `cos x, cos y > 0`) the partial
derivatives are `u_x = tan x`, `u_y = −tan y`, `u_xx = 1/cos² x`, `u_yy = −1/cos² y` and
`u_xy = 0` (the `x`-derivative `tan x` does not depend on `y`); and with `1 + tan² = 1/cos²` the
minimal surface equation reads `(1/cos² y)(1/cos² x) − (1/cos² x)(1/cos² y) = 0`. The partial
derivatives are proved as one-variable derivatives in each coordinate. -/
theorem scherk_minimal (x y : ℝ) (hx : 0 < cos x) (hy : 0 < cos y) :
    HasDerivAt (fun s => scherk s y) (tan x) x ∧
      HasDerivAt (fun t => scherk x t) (-tan y) y ∧
      HasDerivAt tan (1 / cos x ^ 2) x ∧
      HasDerivAt (fun t => -tan t) (-(1 / cos y ^ 2)) y ∧
      HasDerivAt (fun _ : ℝ => tan x) 0 y ∧
      MinimalSurfaceEq (tan x) (-tan y) (1 / cos x ^ 2) 0 (-(1 / cos y ^ 2)) := by
  refine ⟨?_, ?_, hasDerivAt_tan hx.ne', (hasDerivAt_tan hy.ne').neg, hasDerivAt_const _ _, ?_⟩
  · have h := ((hasDerivAt_cos x).log hx.ne').const_sub (log (cos y))
    exact h.congr_deriv (by rw [tan_eq_sin_div_cos]; ring)
  · have h := ((hasDerivAt_cos y).log hy.ne').sub_const (log (cos x))
    exact h.congr_deriv (by rw [tan_eq_sin_div_cos]; ring)
  · unfold MinimalSurfaceEq
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    have hx2 : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    have hy2 : sin y ^ 2 + cos y ^ 2 = 1 := sin_sq_add_cos_sq y
    field_simp
    nlinarith [hx2, hy2]
-- @endregion

/-! ### Ricci flow on a round sphere -/

-- @region geometric_analysis.round_sphere_ricci_flow
-- @provenance independent
/-- **Ricci flow shrinks a round sphere to a point.** For the round metric `g = r² g_{Sⁿ}` one has
`Ric(g) = (n − 1) g_{Sⁿ}`, independent of `r`, so the Ricci flow `∂g/∂t = −2 Ric(g)` keeps the
metric round, `g(t) = ρ(t) g_{Sⁿ}`, with `ρ' = −2(n − 1)`. Hence
`ρ(t) = r₀² − 2(n − 1)t`: positive before `T = r₀²/(2(n − 1))` and zero at `T`, the extinction
time. Here we prove the ODE statements (the curvature computation is the human input). -/
theorem round_sphere_ricci_flow (n : ℕ) (hn : 2 ≤ n) (r₀ : ℝ) :
    let ρ : ℝ → ℝ := fun t => r₀ ^ 2 - 2 * (n - 1) * t
    let T : ℝ := r₀ ^ 2 / (2 * (n - 1))
    (∀ t, HasDerivAt ρ (-(2 * (n - 1))) t) ∧ ρ 0 = r₀ ^ 2 ∧ ρ T = 0 ∧
      (∀ t, t < T → 0 < ρ t) := by
  intro ρ T
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (by norm_num) hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 2 * ((n : ℝ) - 1) := by linarith
  refine ⟨fun t => ?_, by simp [ρ], ?_, fun t ht => ?_⟩
  · have h := ((hasDerivAt_id t).const_mul (2 * ((n : ℝ) - 1))).const_sub (r₀ ^ 2)
    simpa [ρ] using h
  · have hne : (n : ℝ) - 1 ≠ 0 := by linarith
    simp only [ρ, T]
    field_simp
    ring
  · simp only [ρ]
    have : t * (2 * ((n : ℝ) - 1)) < r₀ ^ 2 := by
      have := (lt_div_iff₀ hpos).mp ht
      linarith
    nlinarith
-- @endregion

/-! ### A discrete maximum principle -/

-- @region geometric_analysis.heat_step
-- @provenance definition
/-- One step of the explicit finite-difference scheme for the heat equation `u_t = u_xx` on a grid
`ℤ`, with ratio `λ = Δt/Δx²`: `u'(i) = λ u(i−1) + (1 − 2λ) u(i) + λ u(i+1)`. -/
def heatStep (lam : ℝ) (u : ℤ → ℝ) : ℤ → ℝ :=
  fun i => lam * u (i - 1) + (1 - 2 * lam) * u i + lam * u (i + 1)
-- @endregion

-- @region geometric_analysis.heat_step_const
-- @provenance independent
/-- Constant functions are steady states of the heat scheme: the three weights `λ, 1 − 2λ, λ`
sum to `1`. (For the heat equation itself, constants solve `u_t = u_xx`.) -/
theorem heatStep_const (lam c : ℝ) : heatStep lam (fun _ => c) = fun _ => c := by
  funext i
  simp only [heatStep]
  ring
-- @endregion

-- @region geometric_analysis.discrete_max_principle
-- @provenance independent
/-- **Discrete maximum principle.** If `0 ≤ λ ≤ 1/2` and `u ≤ M` everywhere, then after any number
of heat steps the solution is still `≤ M`: each new value is a convex combination (weights `λ`,
`1 − 2λ`, `λ`, all non-negative) of old values. This is the discrete shadow of the maximum
principle for parabolic equations, which Hamilton turned into his main tool for Ricci flow. For
`λ > 1/2` the weight `1 − 2λ` is negative and the scheme can overshoot (and is unstable). -/
theorem discrete_max_principle (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 2) (M : ℝ)
    (u : ℤ → ℝ) (hu : ∀ i, u i ≤ M) (k : ℕ) (i : ℤ) : (heatStep lam)^[k] u i ≤ M := by
  induction k generalizing u with
  | zero => exact hu i
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    intro j
    simp only [heatStep]
    have ha := hu (j - 1)
    have hb := hu j
    have hc := hu (j + 1)
    have hw : 0 ≤ 1 - 2 * lam := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ha h0, mul_le_mul_of_nonneg_left hb hw,
      mul_le_mul_of_nonneg_left hc h0]
-- @endregion

/-! ### Harmonic functions -/

-- @region geometric_analysis.harmonic_mean_value
-- @provenance library
/-- **Mean value property.** A function harmonic on a neighbourhood of a closed disc in `ℂ = ℝ²`
equals its average over the boundary circle. This is Mathlib's
`InnerProductSpace.HarmonicOnNhd.circleAverage_eq`. It implies the strong maximum principle, and
it is the reason the coordinate functions of a conformally parametrised minimal surface — which
are harmonic — cannot have interior maxima: a compact minimal surface in `ℝ³` must have boundary. -/
theorem harmonic_mean_value {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall c |R|)) :
    circleAverage f c R = f c :=
  hf.circleAverage_eq
-- @endregion

end Lumenary.GeometricAnalysis
