/-
The Lumenary — formal mathematics
Differential geometry of curves and surfaces: unit-speed parametrisation and curvature of a
circle, curvature and torsion of a helix, the first and second fundamental forms and Gaussian
curvature of the sphere, the torus and the cylinder, and Gauss–Bonnet checked on the sphere and
the torus.

What is proved here and what Mathlib provides. Mathlib has one-variable calculus (`HasDerivAt`,
the fundamental theorem of calculus, `integral_cos`) but, at this version, no differential
geometry of curves and surfaces in `ℝ³`: no Frenet frame, no fundamental forms, no Gaussian
curvature. So this module works with explicit parametrisations, writing vectors of `ℝ³` as
triples `ℝ × ℝ × ℝ`. The *independent* declarations compute derivatives with Mathlib's calculus
rules (`HasDerivAt.comp`, `HasDerivAt.prodMk`, …) and then verify the lesson's formulas: the
circle of radius `r` has unit speed and curvature `1/r`; the helix has curvature `a/c²` and
torsion `b/c²`; the sphere of radius `R` has `E = R² cos² φ`, `F = 0`, `G = R²`, `L = -R cos² φ`,
`M = 0`, `N = -R` and Gaussian curvature `1/R²`; the torus has `K = cos φ / (r (R + r cos φ))`;
the cylinder has `K = 0`; and the total curvature `∫∫ K dA` is `4π = 2π χ(S²)` for the sphere and
`0 = 2π χ(T²)` for the torus. The *library* declaration cites Mathlib's `integral_cos`.

Not formalised: the Theorema Egregium and the Gauss–Bonnet theorem in general (only the two
computations above), geodesics, and the definition of a regular surface.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace Lumenary.CurvesSurfaces

open Real

/-! ### Vectors in `ℝ³` -/

-- @region curves_surfaces.dot
-- @provenance definition
/-- The dot product of two vectors of `ℝ³`, written as triples. -/
def dot (u v : ℝ × ℝ × ℝ) : ℝ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
-- @endregion

-- @region curves_surfaces.cross
-- @provenance definition
/-- The cross product of two vectors of `ℝ³`. -/
def cross (u v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)
-- @endregion

/-! ### Curves: the circle -/

-- @region curves_surfaces.has_deriv_at_cos_div
-- @provenance independent
/-- `d/ds [c · cos(s / r)] = -(c / r) · sin(s / r)`, by the chain rule. -/
theorem hasDerivAt_cos_div (c r s : ℝ) :
    HasDerivAt (fun s => c * cos (s / r)) (-(c / r) * sin (s / r)) s := by
  have h := ((hasDerivAt_id' s).div_const r).cos.const_mul c
  convert h using 1
  ring
-- @endregion

-- @region curves_surfaces.has_deriv_at_sin_div
-- @provenance independent
/-- `d/ds [c · sin(s / r)] = (c / r) · cos(s / r)`, by the chain rule. -/
theorem hasDerivAt_sin_div (c r s : ℝ) :
    HasDerivAt (fun s => c * sin (s / r)) ((c / r) * cos (s / r)) s := by
  have h := ((hasDerivAt_id' s).div_const r).sin.const_mul c
  convert h using 1
  ring
-- @endregion

-- @region curves_surfaces.circle_velocity
-- @provenance independent
/-- The circle of radius `r ≠ 0` parametrised by arc length, `γ(s) = (r cos(s/r), r sin(s/r))`, has
velocity `γ'(s) = (-sin(s/r), cos(s/r))`. -/
theorem circle_velocity (r s : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => (r * cos (s / r), r * sin (s / r))) (-sin (s / r), cos (s / r)) s := by
  have h1 := hasDerivAt_cos_div r r s
  have h2 := hasDerivAt_sin_div r r s
  rw [div_self hr] at h1 h2
  simpa using h1.prodMk h2
-- @endregion

-- @region curves_surfaces.circle_unit_speed
-- @provenance independent
/-- The velocity `(-sin(s/r), cos(s/r))` has length `1`: the parametrisation has **unit speed**, so
`s` measures arc length. -/
theorem circle_unit_speed (r s : ℝ) : (-sin (s / r)) ^ 2 + (cos (s / r)) ^ 2 = 1 := by
  rw [neg_sq, sin_sq_add_cos_sq]
-- @endregion

-- @region curves_surfaces.circle_acceleration
-- @provenance independent
/-- Differentiating again, the acceleration of the unit-speed circle is
`γ''(s) = (-(1/r) cos(s/r), -(1/r) sin(s/r))`, pointing to the centre. -/
theorem circle_acceleration (r s : ℝ) :
    HasDerivAt (fun s => (-sin (s / r), cos (s / r)))
      (-(1 / r) * cos (s / r), -(1 / r) * sin (s / r)) s := by
  have h1 := (hasDerivAt_sin_div 1 r s).neg
  have h2 := hasDerivAt_cos_div 1 r s
  simp only [one_mul] at h1 h2
  convert h1.prodMk h2 using 1
  simp only [Prod.mk.injEq, and_true]
  ring
-- @endregion

-- @region curves_surfaces.circle_curvature
-- @provenance independent
/-- **The curvature of a circle of radius `r > 0` is `1/r`.** The curvature of a unit-speed curve
is `κ = |γ''|`, and here `|γ''|² = (1/r)² (cos² + sin²) = 1/r²`. -/
theorem circle_curvature (r s : ℝ) (hr : 0 < r) :
    √((-(1 / r) * cos (s / r)) ^ 2 + (-(1 / r) * sin (s / r)) ^ 2) = 1 / r := by
  have h : (-(1 / r) * cos (s / r)) ^ 2 + (-(1 / r) * sin (s / r)) ^ 2 = (1 / r) ^ 2 := by
    have := cos_sq_add_sin_sq (s / r)
    linear_combination (1 / r) ^ 2 * this
  rw [h, sqrt_sq (by positivity)]
-- @endregion

/-! ### Curves: the helix -/

-- @region curves_surfaces.helix_velocity
-- @provenance independent
/-- The helix `γ(s) = (a cos(s/c), a sin(s/c), b s / c)` has velocity
`T = ((-a/c) sin(s/c), (a/c) cos(s/c), b/c)`. -/
theorem helix_velocity (a b c s : ℝ) :
    HasDerivAt (fun s => (a * cos (s / c), a * sin (s / c), b * s / c))
      (-(a / c) * sin (s / c), (a / c) * cos (s / c), b / c) s := by
  have h3 : HasDerivAt (fun s => b * s / c) (b / c) s := by
    simpa using ((hasDerivAt_id s).const_mul b).div_const c
  exact (hasDerivAt_cos_div a c s).prodMk ((hasDerivAt_sin_div a c s).prodMk h3)
-- @endregion

-- @region curves_surfaces.helix_tangent_deriv
-- @provenance independent
/-- Differentiating the unit tangent `T(s) = ((-a/c) sin(s/c), (a/c) cos(s/c), b/c)` of the helix:
`T'(s) = ((-a/c²) cos(s/c), (-a/c²) sin(s/c), 0)`. -/
theorem helix_tangent_deriv (a b c s : ℝ) :
    HasDerivAt (fun s => (-(a / c) * sin (s / c), (a / c) * cos (s / c), b / c))
      (-(a / c ^ 2) * cos (s / c), -(a / c ^ 2) * sin (s / c), 0) s := by
  have h1 := hasDerivAt_sin_div (-(a / c)) c s
  have h2 := hasDerivAt_cos_div (a / c) c s
  have h3 := hasDerivAt_const s (b / c)
  convert h1.prodMk (h2.prodMk h3) using 1
  exact Prod.ext (by ring) (Prod.ext (by ring) rfl)
-- @endregion

-- @region curves_surfaces.helix_binormal_deriv
-- @provenance independent
/-- Differentiating the binormal `B(s) = ((b/c) sin(s/c), (-b/c) cos(s/c), a/c)` of the helix:
`B'(s) = ((b/c²) cos(s/c), (b/c²) sin(s/c), 0)`. -/
theorem helix_binormal_deriv (a b c s : ℝ) :
    HasDerivAt (fun s => ((b / c) * sin (s / c), -(b / c) * cos (s / c), a / c))
      ((b / c ^ 2) * cos (s / c), (b / c ^ 2) * sin (s / c), 0) s := by
  have h1 := hasDerivAt_sin_div (b / c) c s
  have h2 := hasDerivAt_cos_div (-(b / c)) c s
  have h3 := hasDerivAt_const s (a / c)
  convert h1.prodMk (h2.prodMk h3) using 1
  exact Prod.ext (by ring) (Prod.ext (by ring) rfl)
-- @endregion

-- @region curves_surfaces.helix_frenet
-- @provenance independent
/-- **Curvature and torsion of a helix.** Let `c = √(a² + b²) > 0` and `T` be the velocity above.
Then (1) `|T| = 1`, so `s` is arc length; (2) `T' = (a/c²)·N` with `N = (-cos, -sin, 0)` a unit
vector, so the curvature is `κ = a/c²`; (3) the binormal `B = T × N` satisfies `B' = -(b/c²)·N`,
so the torsion is `τ = b/c²`. Here `θ = s/c`, and `T'`, `B'` are the derivatives computed in
`helix_tangent_deriv` and `helix_binormal_deriv`. -/
theorem helix_frenet (a b c θ : ℝ) (hc : c ^ 2 = a ^ 2 + b ^ 2) (hc0 : c ≠ 0) :
    let T : ℝ × ℝ × ℝ := (-(a / c) * sin θ, (a / c) * cos θ, b / c)
    let N : ℝ × ℝ × ℝ := (-cos θ, -sin θ, 0)
    let B := cross T N
    dot T T = 1 ∧ dot N N = 1 ∧
      B = ((b / c) * sin θ, -(b / c) * cos θ, a / c) ∧
      ((-(a / c ^ 2)) * cos θ, (-(a / c ^ 2)) * sin θ, (0 : ℝ)) = (a / c ^ 2) • N ∧
      (((b / c ^ 2)) * cos θ, (b / c ^ 2) * sin θ, (0 : ℝ)) = (-(b / c ^ 2)) • N := by
  intro T N B
  have hs := sin_sq_add_cos_sq θ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [T, dot]
    field_simp
    linear_combination (a ^ 2) * hs - hc
  · simp only [N, dot]
    linear_combination hs
  · simp only [B, T, N, cross, Prod.mk.injEq]
    refine ⟨by ring, by ring, ?_⟩
    field_simp
    linear_combination a * hs
  · simp only [N, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  · simp only [N, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
-- @endregion

/-! ### Surfaces: fundamental forms and Gaussian curvature -/

-- @region curves_surfaces.gauss_curvature
-- @provenance definition
/-- The **Gaussian curvature** from the coefficients of the first fundamental form `E, F, G` and
the second fundamental form `L, M, N`: `K = (LN - M²) / (EG - F²)`. -/
noncomputable def gaussCurvature (E F G L M N : ℝ) : ℝ := (L * N - M ^ 2) / (E * G - F ^ 2)
-- @endregion

-- @region curves_surfaces.sphere
-- @provenance definition
/-- The sphere of radius `R` in longitude `θ` and latitude `φ`:
`X(θ, φ) = (R cos φ cos θ, R cos φ sin θ, R sin φ)`. -/
noncomputable def sphere (R θ φ : ℝ) : ℝ × ℝ × ℝ :=
  (R * cos φ * cos θ, R * cos φ * sin θ, R * sin φ)
-- @endregion

-- @region curves_surfaces.sphere_d_theta
-- @provenance independent
/-- The partial derivative in the longitude: `X_θ = (-R cos φ sin θ, R cos φ cos θ, 0)`. -/
theorem sphere_dTheta (R θ φ : ℝ) :
    HasDerivAt (fun θ => sphere R θ φ) (-(R * cos φ) * sin θ, R * cos φ * cos θ, 0) θ := by
  have h1 := (hasDerivAt_cos θ).const_mul (R * cos φ)
  have h2 := (hasDerivAt_sin θ).const_mul (R * cos φ)
  have h3 := hasDerivAt_const θ (R * sin φ)
  convert h1.prodMk (h2.prodMk h3) using 1
  · rfl
  · exact Prod.ext (by ring) rfl
-- @endregion

-- @region curves_surfaces.sphere_d_phi
-- @provenance independent
/-- The partial derivative in the latitude: `X_φ = (-R sin φ cos θ, -R sin φ sin θ, R cos φ)`. -/
theorem sphere_dPhi (R θ φ : ℝ) :
    HasDerivAt (fun φ => sphere R θ φ)
      (-(R * sin φ) * cos θ, -(R * sin φ) * sin θ, R * cos φ) φ := by
  have h1 := ((hasDerivAt_cos φ).const_mul R).mul_const (cos θ)
  have h2 := ((hasDerivAt_cos φ).const_mul R).mul_const (sin θ)
  have h3 := (hasDerivAt_sin φ).const_mul R
  convert h1.prodMk (h2.prodMk h3) using 1
  · rfl
  · exact Prod.ext (by ring) (Prod.ext (by ring) rfl)
-- @endregion

-- @region curves_surfaces.sphere_first_form
-- @provenance independent
/-- **First fundamental form of the sphere**: `E = X_θ · X_θ = R² cos² φ`, `F = X_θ · X_φ = 0`,
`G = X_φ · X_φ = R²`. -/
theorem sphere_first_form (R θ φ : ℝ) :
    let Xθ : ℝ × ℝ × ℝ := (-(R * cos φ) * sin θ, R * cos φ * cos θ, 0)
    let Xφ : ℝ × ℝ × ℝ := (-(R * sin φ) * cos θ, -(R * sin φ) * sin θ, R * cos φ)
    dot Xθ Xθ = R ^ 2 * cos φ ^ 2 ∧ dot Xθ Xφ = 0 ∧ dot Xφ Xφ = R ^ 2 := by
  intro Xθ Xφ
  have hθ := sin_sq_add_cos_sq θ
  have hφ := sin_sq_add_cos_sq φ
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Xθ, Xφ, dot]
  · linear_combination (R ^ 2 * cos φ ^ 2) * hθ
  · ring
  · linear_combination (R ^ 2 * sin φ ^ 2) * hθ + R ^ 2 * hφ
-- @endregion

-- @region curves_surfaces.sphere_second_form
-- @provenance independent
/-- **Second fundamental form of the sphere**, with the outward unit normal
`n = (cos φ cos θ, cos φ sin θ, sin φ)` and the second derivatives
`X_θθ = (-R cos φ cos θ, -R cos φ sin θ, 0)`, `X_θφ = (R sin φ sin θ, -R sin φ cos θ, 0)` and
`X_φφ = (-R cos φ cos θ, -R cos φ sin θ, -R sin φ)`: `L = -R cos² φ`, `M = 0`, `N = -R`, and `n` is
a unit vector. -/
theorem sphere_second_form (R θ φ : ℝ) :
    let n : ℝ × ℝ × ℝ := (cos φ * cos θ, cos φ * sin θ, sin φ)
    let Xθθ : ℝ × ℝ × ℝ := (-(R * cos φ) * cos θ, -(R * cos φ) * sin θ, 0)
    let Xθφ : ℝ × ℝ × ℝ := (R * sin φ * sin θ, -(R * sin φ) * cos θ, 0)
    let Xφφ : ℝ × ℝ × ℝ := (-(R * cos φ) * cos θ, -(R * cos φ) * sin θ, -(R * sin φ))
    dot n n = 1 ∧ dot Xθθ n = -R * cos φ ^ 2 ∧ dot Xθφ n = 0 ∧ dot Xφφ n = -R := by
  intro n Xθθ Xθφ Xφφ
  have hθ := sin_sq_add_cos_sq θ
  have hφ := sin_sq_add_cos_sq φ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [n, Xθθ, Xθφ, Xφφ, dot]
  · linear_combination (cos φ ^ 2) * hθ + hφ
  · linear_combination (-R * cos φ ^ 2) * hθ
  · ring
  · linear_combination (-R * cos φ ^ 2) * hθ - R * hφ
-- @endregion

-- @region curves_surfaces.sphere_gauss_curvature
-- @provenance independent
/-- **The sphere of radius `R` has constant Gaussian curvature `1/R²`** (away from the poles,
where `cos φ ≠ 0` and the coordinates are regular):
`K = (LN - M²)/(EG - F²) = (R² cos² φ)/(R⁴ cos² φ) = 1/R²`. -/
theorem sphere_gauss_curvature (R φ : ℝ) (hR : R ≠ 0) (hφ : cos φ ≠ 0) :
    gaussCurvature (R ^ 2 * cos φ ^ 2) 0 (R ^ 2) (-R * cos φ ^ 2) 0 (-R) = 1 / R ^ 2 := by
  unfold gaussCurvature
  field_simp
  ring
-- @endregion

-- @region curves_surfaces.torus_gauss_curvature
-- @provenance independent
/-- **The torus.** For `X(θ, φ) = ((R + r cos φ) cos θ, (R + r cos φ) sin θ, r sin φ)` with
`0 < r < R`, the fundamental forms are `E = (R + r cos φ)²`, `F = 0`, `G = r²`,
`L = -(R + r cos φ) cos φ`, `M = 0`, `N = -r`, so `K = cos φ / (r (R + r cos φ))`: positive on the
outside (`cos φ > 0`), negative on the inside, zero on the top and bottom circles. -/
theorem torus_gauss_curvature (R r φ : ℝ) (hr : 0 < r) (hRr : r < R) :
    gaussCurvature ((R + r * cos φ) ^ 2) 0 (r ^ 2) (-(R + r * cos φ) * cos φ) 0 (-r) =
      cos φ / (r * (R + r * cos φ)) := by
  have hpos : 0 < R + r * cos φ := by
    nlinarith [neg_one_le_cos φ, cos_le_one φ]
  unfold gaussCurvature
  field_simp
  ring
-- @endregion

-- @region curves_surfaces.cylinder_gauss_curvature
-- @provenance independent
/-- **The cylinder is flat.** For `X(θ, z) = (r cos θ, r sin θ, z)`: `E = r²`, `F = 0`, `G = 1`,
`L = -r`, `M = 0`, `N = 0`, so `K = 0`. One principal curvature is `1/r`, the other `0`; their
product vanishes — although the cylinder looks curved. -/
theorem cylinder_gauss_curvature (r : ℝ) : gaussCurvature (r ^ 2) 0 1 (-r) 0 0 = 0 := by
  simp [gaussCurvature]
-- @endregion

/-! ### Gauss–Bonnet on two examples -/

-- @region curves_surfaces.integral_cos_library
-- @provenance library
/-- `∫ₐᵇ cos x dx = sin b - sin a`. This applies Mathlib's `integral_cos` (the fundamental
theorem of calculus for `sin' = cos`). -/
theorem integral_cos_library (a b : ℝ) : ∫ x in a..b, cos x = sin b - sin a :=
  integral_cos
-- @endregion

-- @region curves_surfaces.gauss_bonnet_sphere
-- @provenance independent
/-- **Gauss–Bonnet for the sphere.** The area element is `dA = √(EG - F²) dθ dφ = R² cos φ dθ dφ`
(for `|φ| ≤ π/2`) and `K = 1/R²`, so `K dA = cos φ dθ dφ`. Integrating over longitude `[0, 2π]`
and latitude `[-π/2, π/2]` gives `2π · 2 = 4π = 2π χ(S²)`, for every radius `R`. -/
theorem gauss_bonnet_sphere (R : ℝ) (hR : R ≠ 0) :
    ∫ _θ in (0 : ℝ)..2 * π, ∫ φ in (-(π / 2))..(π / 2), (1 / R ^ 2) * (R ^ 2 * cos φ) =
      2 * π * 2 := by
  have hK : ∀ φ : ℝ, (1 / R ^ 2) * (R ^ 2 * cos φ) = cos φ := by
    intro φ
    field_simp
  simp only [hK, integral_cos, sin_neg, sin_pi_div_two, intervalIntegral.integral_const,
    smul_eq_mul]
  ring
-- @endregion

-- @region curves_surfaces.gauss_bonnet_torus
-- @provenance independent
/-- **Gauss–Bonnet for the torus.** Here `dA = r (R + r cos φ) dθ dφ`, so
`K dA = cos φ dθ dφ`, and `∫₀^{2π} ∫₀^{2π} cos φ dφ dθ = 0 = 2π χ(T²)`. The positive curvature
on the outside exactly cancels the negative curvature on the inside. -/
theorem gauss_bonnet_torus (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    ∫ _θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
      cos φ / (r * (R + r * cos φ)) * (r * (R + r * cos φ)) = 0 := by
  have hK : ∀ φ : ℝ, cos φ / (r * (R + r * cos φ)) * (r * (R + r * cos φ)) = cos φ := by
    intro φ
    have hpos : 0 < R + r * cos φ := by
      nlinarith [neg_one_le_cos φ, cos_le_one φ]
    exact div_mul_cancel₀ (cos φ) (mul_ne_zero hr.ne' hpos.ne')
  simp only [hK, integral_cos, sin_two_pi, sin_zero, sub_zero, intervalIntegral.integral_const,
    smul_eq_mul, mul_zero]
-- @endregion

end Lumenary.CurvesSurfaces
