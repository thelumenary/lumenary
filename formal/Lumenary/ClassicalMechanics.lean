/-
The Lumenary — formal mathematics
Classical mechanics: projectiles, conservation of energy for conservative forces (in any
dimension), conservation of angular momentum and planar motion under central forces, Kepler
orbits as conic sections, and the damped harmonic oscillator.

What is proved here and what Mathlib provides. Mathlib has no physics library, but it has the
calculus needed to state Newton's law `m r'' = F(r)` precisely: a trajectory is a pair of
functions `r, v : ℝ → E` with `r' = v` and `m v' = F(r)` (`HasDerivAt`). The *independent*
declarations prove the lesson's conservation laws exactly as on paper — by differentiating the
conserved quantity and getting zero — and verify the explicit solutions (projectile, conic orbit,
damped oscillator). The *library* declarations cite Mathlib's facts about the cross product
(`cross_self`, `dot_self_cross`) used in the angular-momentum argument. Not formalised: the
Euler–Lagrange equations (the calculus of variations), whose statement needs differentiation
under the integral sign.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct

namespace Lumenary.ClassicalMechanics

open Real Matrix

/-! ### Uniform gravity -/

-- @region classical_mechanics.projectile
-- @provenance independent
/-- A projectile in uniform gravity: the height `y(t) = y₀ + v₀ t - g t²/2` has velocity
`v(t) = v₀ - g t`, whose derivative is the constant acceleration `-g`. -/
theorem projectile (y₀ v₀ g t : ℝ) :
    HasDerivAt (fun s => y₀ + v₀ * s - g * s ^ 2 / 2) (v₀ - g * t) t ∧
      HasDerivAt (fun s => v₀ - g * s) (-g) t := by
  constructor
  · have h := (((hasDerivAt_id' t).const_mul v₀).const_add y₀).sub
      ((hasDerivAt_pow 2 t).const_mul g |>.div_const 2)
    convert h using 1
    push_cast
    ring
  · have h := ((hasDerivAt_id' t).const_mul g).const_sub v₀
    convert h using 1
    ring
-- @endregion

/-! ### Conservation of energy -/

-- @region classical_mechanics.energy_conservation
-- @provenance independent
/-- **Conservation of energy** for a conservative force, in any (real inner product) space.
Suppose the particle of mass `m ≠ 0` moves by Newton's law with force `F = -∇V`: `r' = v` and
`v' = -(1/m) ∇V(r)`. Then the total energy `E = ½ m ⟪v, v⟫ + V(r)` is constant. Proof: by the
product and chain rules, `E' = m ⟪v, v'⟫ + ⟪∇V(r), r'⟫ = -⟪v, ∇V(r)⟫ + ⟪∇V(r), v⟫ = 0`. -/
theorem energy_conservation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {m : ℝ} (hm : m ≠ 0) {V : E → ℝ} {gradV : E → E}
    (hV : ∀ x, HasGradientAt V (gradV x) x) {r v : ℝ → E}
    (hr : ∀ t, HasDerivAt r (v t) t) (hv : ∀ t, HasDerivAt v (-(1 / m) • gradV (r t)) t)
    (s t : ℝ) :
    m / 2 * inner ℝ (v s) (v s) + V (r s) = m / 2 * inner ℝ (v t) (v t) + V (r t) := by
  have hE : ∀ τ, HasDerivAt (fun τ => m / 2 * inner ℝ (v τ) (v τ) + V (r τ)) 0 τ := by
    intro τ
    have hkin := ((hv τ).inner ℝ (hv τ)).const_mul (m / 2)
    have hpot := (hasGradientAt_iff_hasFDerivAt.mp (hV (r τ))).comp_hasDerivAt τ (hr τ)
    have h := hkin.add hpot
    convert h using 1
    · rfl
    · simp only [InnerProductSpace.toDual_apply_apply, inner_smul_right, inner_smul_left,
        real_inner_comm (gradV (r τ)) (v τ), RCLike.conj_to_real]
      field_simp
      ring
  exact is_const_of_deriv_eq_zero (fun τ => (hE τ).differentiableAt) (fun τ => (hE τ).deriv) s t
-- @endregion

/-! ### Central forces and angular momentum -/

-- @region classical_mechanics.cross_self_zero
-- @provenance library
/-- The cross product of a vector with itself is zero (Mathlib's `cross_self`). It is why the
term `v × (m v)` drops out of `d/dt (r × m v) = v × m v + r × m v'`. -/
theorem cross_self_zero (v : Fin 3 → ℝ) : v ⨯₃ v = 0 :=
  cross_self v
-- @endregion

-- @region classical_mechanics.angular_momentum_conserved
-- @provenance independent
/-- **Conservation of angular momentum** under a central force. If `r' = v` and `v' = k(t) r`
(acceleration always parallel to the position vector, as for any central force), then
`L = r × v` has derivative `v × v + r × (k r) = 0`, so it is constant. We check the derivative
coordinate by coordinate (`hasDerivAt_pi`). -/
theorem angular_momentum_conserved {r v : ℝ → Fin 3 → ℝ} {k : ℝ → ℝ}
    (hr : ∀ t, HasDerivAt r (v t) t) (hv : ∀ t, HasDerivAt v (k t • r t) t) (s t : ℝ) :
    r s ⨯₃ v s = r t ⨯₃ v t := by
  have hL : ∀ τ, HasDerivAt (fun τ => r τ ⨯₃ v τ) 0 τ := by
    intro τ
    rw [hasDerivAt_pi]
    have hri : ∀ i, HasDerivAt (fun τ => r τ i) (v τ i) τ := hasDerivAt_pi.mp (hr τ)
    have hvi : ∀ i, HasDerivAt (fun τ => v τ i) (k τ * r τ i) τ := by
      intro i
      simpa using hasDerivAt_pi.mp (hv τ) i
    intro i
    fin_cases i
    · have h := ((hri 1).mul (hvi 2)).sub ((hri 2).mul (hvi 1))
      convert h using 1
      · funext τ; simp [cross_apply]
      · simp; ring
    · have h := ((hri 2).mul (hvi 0)).sub ((hri 0).mul (hvi 2))
      convert h using 1
      · funext τ; simp [cross_apply]
      · simp; ring
    · have h := ((hri 0).mul (hvi 1)).sub ((hri 1).mul (hvi 0))
      convert h using 1
      · funext τ; simp [cross_apply]
      · simp; ring
  exact is_const_of_deriv_eq_zero (fun τ => (hL τ).differentiableAt) (fun τ => (hL τ).deriv) s t
-- @endregion

-- @region classical_mechanics.dot_self_cross_zero
-- @provenance library
/-- A vector is perpendicular to its cross product with any other vector:
`r · (r × v) = 0` (Mathlib's `dot_self_cross`). -/
theorem dot_self_cross_zero (r v : Fin 3 → ℝ) : r ⬝ᵥ (r ⨯₃ v) = 0 :=
  dot_self_cross r v
-- @endregion

-- @region classical_mechanics.motion_in_plane
-- @provenance independent
/-- **Central-force motion is planar.** Under the hypotheses of `angular_momentum_conserved`,
the position `r(t)` is perpendicular to the constant vector `L = r(0) × v(0)` at every time,
so (when `L ≠ 0`) the particle stays in the plane through the origin perpendicular to `L`. -/
theorem motion_in_plane {r v : ℝ → Fin 3 → ℝ} {k : ℝ → ℝ}
    (hr : ∀ t, HasDerivAt r (v t) t) (hv : ∀ t, HasDerivAt v (k t • r t) t) (t : ℝ) :
    r t ⬝ᵥ (r 0 ⨯₃ v 0) = 0 := by
  rw [angular_momentum_conserved hr hv 0 t]
  exact dot_self_cross_zero (r t) (v t)
-- @endregion

/-! ### Kepler orbits are conic sections -/

-- @region classical_mechanics.binet_conic
-- @provenance independent
/-- The orbit equation. With `u = 1/r` as a function of the polar angle `θ`, the inverse-square
law gives Binet's equation `u'' + u = 1/p`. Its solutions `u(θ) = (1 + e cos θ)/p` (for constants
`e`, `p` with `p ≠ 0`) indeed satisfy it: `u' = -(e/p) sin θ`, `u'' = -(e/p) cos θ`. -/
theorem binet_conic (e p θ : ℝ) :
    HasDerivAt (fun φ => (1 + e * cos φ) / p) (-(e / p) * sin θ) θ ∧
      HasDerivAt (fun φ => -(e / p) * sin φ) (1 / p - (1 + e * cos θ) / p) θ := by
  constructor
  · have h := (((hasDerivAt_cos θ).const_mul e).const_add 1).div_const p
    convert h using 1
    ring
  · have h := (hasDerivAt_sin θ).const_mul (-(e / p))
    convert h using 1
    ring
-- @endregion

-- @region classical_mechanics.orbit_is_conic
-- @provenance independent
/-- **Kepler's first law, the geometric step.** If a point at distance `r ≥ 0` from the origin and
polar angle `θ` lies on the orbit `r (1 + e cos θ) = p`, then its Cartesian coordinates
`x = r cos θ`, `y = r sin θ` satisfy `(1 - e²) x² + 2 p e x + y² = p²`: a conic with a focus at
the origin — an ellipse if `0 ≤ e < 1` (a circle if `e = 0`), a parabola if `e = 1`, a hyperbola
branch if `e > 1`. Proof: `r = p - e x`, and `x² + y² = r²`. -/
theorem orbit_is_conic {r θ e p : ℝ} (horbit : r * (1 + e * cos θ) = p) :
    (1 - e ^ 2) * (r * cos θ) ^ 2 + 2 * p * e * (r * cos θ) + (r * sin θ) ^ 2 = p ^ 2 := by
  have hr : r = p - e * (r * cos θ) := by linarith
  have hpyth : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
    have := sin_sq_add_cos_sq θ
    calc (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 * (sin θ ^ 2 + cos θ ^ 2) := by ring
      _ = r ^ 2 := by rw [this, mul_one]
  calc (1 - e ^ 2) * (r * cos θ) ^ 2 + 2 * p * e * (r * cos θ) + (r * sin θ) ^ 2
      = ((r * cos θ) ^ 2 + (r * sin θ) ^ 2) - (e * (r * cos θ)) ^ 2
          + 2 * p * (e * (r * cos θ)) := by ring
    _ = r ^ 2 - (e * (r * cos θ)) ^ 2 + 2 * p * (e * (r * cos θ)) := by rw [hpyth]
    _ = (p - e * (r * cos θ)) ^ 2 - (e * (r * cos θ)) ^ 2 + 2 * p * (e * (r * cos θ)) := by
        rw [← hr]
    _ = p ^ 2 := by ring
-- @endregion

-- @region classical_mechanics.eccentricity_energy
-- @provenance independent
/-- **Energy determines the shape.** At perihelion the radial velocity is `0` and
`r = p/(1 + e)`, so the energy is `E = L²/(2 m r²) - k/r`. With `p = L²/(m k)` this equals
`k (e² - 1)/(2p)`: hence `e < 1` (an ellipse) exactly when `E < 0`. -/
theorem eccentricity_energy {m k L e : ℝ} (hm : 0 < m) (hk : 0 < k) (hL : L ≠ 0)
    (he : 0 ≤ e) :
    let p := L ^ 2 / (m * k)
    let r := p / (1 + e)
    L ^ 2 / (2 * m * r ^ 2) - k / r = k * (e ^ 2 - 1) / (2 * p) := by
  intro p r
  have hp : p ≠ 0 := by positivity
  have h1e : 1 + e ≠ 0 := by positivity
  have hr : r ≠ 0 := div_ne_zero hp h1e
  have hpL : L ^ 2 = p * (m * k) := by
    simp only [p]; field_simp
  simp only [r]
  rw [hpL]
  field_simp
  ring
-- @endregion

-- @region classical_mechanics.kepler_third_law
-- @provenance independent
/-- **Kepler's third law, the algebraic step.** An ellipse with semi-latus rectum
`p = L²/(m k)` and semi-major axis `a` has semi-minor axis `b` with `b² = p a` (since
`a = p/(1 - e²)` and `b = a √(1 - e²)`). Its area `πab` is swept at the constant rate `L/(2m)`,
so the period is `T = πab / (L/(2m))`. Then `T² = 4π² m a³ / k`. -/
theorem kepler_third_law {m k L a b T : ℝ} (hm : 0 < m) (hk : 0 < k) (hL : L ≠ 0)
    (hb : b ^ 2 = L ^ 2 / (m * k) * a) (hT : T = π * a * b / (L / (2 * m))) :
    T ^ 2 = 4 * π ^ 2 * m * a ^ 3 / k := by
  have hm0 : m ≠ 0 := hm.ne'
  have hk0 : k ≠ 0 := hk.ne'
  rw [hT]
  calc (π * a * b / (L / (2 * m))) ^ 2 = 4 * π ^ 2 * m ^ 2 * a ^ 2 * b ^ 2 / L ^ 2 := by
        field_simp
        ring
    _ = 4 * π ^ 2 * m * a ^ 3 / k := by
        rw [hb]
        field_simp
-- @endregion

/-! ### Oscillators -/

-- @region classical_mechanics.damped_oscillator
-- @provenance independent
/-- The underdamped oscillator `x'' + 2γ x' + ω₀² x = 0` with `ω₀² = γ² + ω²` is solved by
`x(t) = e^{-γt} cos(ωt)`: we compute its velocity `v` and check `v' = -2γ v - ω₀² x`. -/
theorem damped_oscillator (γ ω t : ℝ) :
    HasDerivAt (fun s => exp (-γ * s) * cos (ω * s))
        (exp (-γ * t) * (-γ * cos (ω * t) - ω * sin (ω * t))) t ∧
      HasDerivAt (fun s => exp (-γ * s) * (-γ * cos (ω * s) - ω * sin (ω * s)))
        (-2 * γ * (exp (-γ * t) * (-γ * cos (ω * t) - ω * sin (ω * t)))
          - (γ ^ 2 + ω ^ 2) * (exp (-γ * t) * cos (ω * t))) t := by
  have hl : ∀ c : ℝ, HasDerivAt (fun s => c * s) c t := fun c => by
    simpa using (hasDerivAt_id' t).const_mul c
  have he := (hl (-γ)).exp
  constructor
  · have h := he.mul (hl ω).cos
    convert h using 1
    ring
  · have h := he.mul ((((hl ω).cos).const_mul (-γ)).sub (((hl ω).sin).const_mul ω))
    convert h using 1
    simp only [Pi.sub_apply]
    ring
-- @endregion

end Lumenary.ClassicalMechanics
