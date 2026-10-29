/-
The Lumenary — formal mathematics
The geometry of spacetime: Lorentz boosts, the twin paradox as a reverse triangle inequality, and
circular orbits around a Schwarzschild black hole.

Mathlib has no Minkowski space or Lorentzian geometry yet (the Physlib project builds them on top
of Mathlib), so here we work directly with Mathlib's real numbers, matrices, inner product spaces
and derivatives, in units with `c = 1` and `G = 1`. Proved here: boosts preserve the Minkowski
metric (`Λᵀ η Λ = η`) and compose by adding rapidities; relativistic velocity addition never
exceeds the speed of light; the reversed Cauchy–Schwarz inequality and the reverse triangle
inequality for future-pointing timelike vectors (the twin paradox), in any number of space
dimensions; and, for the Schwarzschild effective potential, the derivative formula, the bound
`L² ≥ 12 M²` for circular orbits and the innermost stable circular orbit at `r = 6M`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped RealInnerProductSpace

namespace Lumenary.Relativity

/-! ### Special relativity in 1 + 1 dimensions: the Lorentz group -/

-- @region relativity.eta
-- @provenance definition
/-- The Minkowski metric in one time and one space dimension, signature `(−, +)`:
`η((t, x), (t, x)) = −t² + x²`. -/
def eta : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]
-- @endregion

-- @region relativity.boost
-- @provenance definition
/-- The Lorentz boost with rapidity `φ`, acting on column vectors `(t, x)`:
`t′ = t cosh φ + x sinh φ`, `x′ = t sinh φ + x cosh φ`. Its velocity is `v = tanh φ` and its
Lorentz factor is `γ = cosh φ = 1/√(1 − v²)`. -/
noncomputable def boost (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh φ, Real.sinh φ; Real.sinh φ, Real.cosh φ]
-- @endregion

-- @region relativity.boost_preserves_eta
-- @provenance independent
/-- **Boosts are Lorentz transformations:** `Λᵀ η Λ = η`, i.e. every boost preserves the interval
`−t² + x²`. Proof: multiply out; the entries reduce to `cosh² φ − sinh² φ = 1`. -/
theorem boost_preserves_eta (φ : ℝ) : (boost φ).transpose * eta * boost φ = eta := by
  have h := Real.cosh_sq φ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, eta, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]
-- @endregion

-- @region relativity.boost_mul
-- @provenance independent
/-- **Rapidities add:** `Λ(φ) Λ(ψ) = Λ(φ + ψ)`. The boosts form a one-parameter group isomorphic
to `(ℝ, +)` — the hyperbolic analogue of rotations composing by adding angles. Proof: the
addition formulas for `cosh` and `sinh`. -/
theorem boost_mul (φ ψ : ℝ) : boost φ * boost ψ = boost (φ + ψ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_add, Real.sinh_add] <;> ring
-- @endregion

-- @region relativity.velocity_addition
-- @provenance independent
/-- **Relativistic velocity addition stays below the speed of light.** If `|u| < 1` and `|v| < 1`
then `|(u + v)/(1 + uv)| < 1`. (This is `tanh(φ + ψ)` for `u = tanh φ`, `v = tanh ψ`.) Proof:
`1 + uv > 0`, and `(1 + uv) − (u + v) = (1 − u)(1 − v) > 0`,
`(1 + uv) + (u + v) = (1 + u)(1 + v) > 0`. -/
theorem velocity_addition {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    |(u + v) / (1 + u * v)| < 1 := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  have hpos : 0 < 1 + u * v := by nlinarith
  rw [abs_div, abs_of_pos hpos, div_lt_one hpos, abs_lt]
  constructor <;> nlinarith
-- @endregion

-- @region relativity.lorentz_factor_three_fifths
-- @provenance independent
/-- A traveller at `v = 3/5` of the speed of light has Lorentz factor
`γ = 1/√(1 − 9/25) = 5/4`: every `5` years of Earth time are `4` years of proper time. -/
theorem lorentz_factor_three_fifths : 1 / Real.sqrt (1 - (3 / 5 : ℝ) ^ 2) = 5 / 4 := by
  have h : (1 - (3 / 5 : ℝ) ^ 2) = (4 / 5) ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num
-- @endregion

/-! ### Proper time and the twin paradox, in any dimension -/

-- @region relativity.reverse_cauchy_schwarz
-- @provenance independent
/-- **The reversed Cauchy–Schwarz inequality.** For future-pointing causal vectors `(t₁, x)` and
`(t₂, y)` (time component `t`, space component in any real inner product space, `‖x‖ ≤ t₁`,
`‖y‖ ≤ t₂`): `√(t₁² − ‖x‖²) · √(t₂² − ‖y‖²) ≤ t₁ t₂ − ⟪x, y⟫`. In Minkowski terms,
`τ(v) τ(w) ≤ −η(v, w)`. Proof: `⟪x, y⟫ ≤ ‖x‖ ‖y‖` (Cauchy–Schwarz), and
`(t₁ t₂ − ‖x‖‖y‖)² − (t₁² − ‖x‖²)(t₂² − ‖y‖²) = (t₁‖y‖ − t₂‖x‖)² ≥ 0`. -/
theorem reverse_cauchy_schwarz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {t₁ t₂ : ℝ} {x y : E} (h₁ : ‖x‖ ≤ t₁) (h₂ : ‖y‖ ≤ t₂) :
    Real.sqrt (t₁ ^ 2 - ‖x‖ ^ 2) * Real.sqrt (t₂ ^ 2 - ‖y‖ ^ 2) ≤ t₁ * t₂ - ⟪x, y⟫ := by
  have hcs : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have ha : 0 ≤ t₁ ^ 2 - ‖x‖ ^ 2 := by nlinarith
  rw [← Real.sqrt_mul ha]
  calc Real.sqrt ((t₁ ^ 2 - ‖x‖ ^ 2) * (t₂ ^ 2 - ‖y‖ ^ 2)) ≤ t₁ * t₂ - ‖x‖ * ‖y‖ := by
        rw [Real.sqrt_le_iff]
        constructor
        · nlinarith [mul_le_mul h₁ h₂ hy (hx.trans h₁)]
        · nlinarith [sq_nonneg (t₁ * ‖y‖ - t₂ * ‖x‖)]
    _ ≤ t₁ * t₂ - ⟪x, y⟫ := by linarith
-- @endregion

-- @region relativity.twin_paradox
-- @provenance independent
/-- **The reverse triangle inequality (the twin paradox).** For future-pointing causal vectors
`v = (t₁, x)` and `w = (t₂, y)`, with proper time `τ(t, x) = √(t² − ‖x‖²)`:
`τ(v) + τ(w) ≤ τ(v + w)`. The stay-at-home twin's straight worldline from `0` to `v + w` has
*more* proper time than the traveller's broken path `0 → v → v + w`: in Minkowski geometry the
straight line is the *longest* timelike path. Proof: square both sides; using
`‖x + y‖² = ‖x‖² + 2⟪x, y⟫ + ‖y‖²`, the inequality reduces to the reversed Cauchy–Schwarz
inequality. -/
theorem twin_paradox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {t₁ t₂ : ℝ} {x y : E} (h₁ : ‖x‖ ≤ t₁) (h₂ : ‖y‖ ≤ t₂) :
    Real.sqrt (t₁ ^ 2 - ‖x‖ ^ 2) + Real.sqrt (t₂ ^ 2 - ‖y‖ ^ 2) ≤
      Real.sqrt ((t₁ + t₂) ^ 2 - ‖x + y‖ ^ 2) := by
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have ha : 0 ≤ t₁ ^ 2 - ‖x‖ ^ 2 := by nlinarith
  have hb : 0 ≤ t₂ ^ 2 - ‖y‖ ^ 2 := by nlinarith
  have hrcs := reverse_cauchy_schwarz h₁ h₂
  have hnorm : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_add_sq_real x y
  have hxy : ‖x + y‖ ≤ t₁ + t₂ := (norm_add_le x y).trans (add_le_add h₁ h₂)
  have hc : 0 ≤ (t₁ + t₂) ^ 2 - ‖x + y‖ ^ 2 := by nlinarith [norm_nonneg (x + y)]
  rw [Real.le_sqrt (by positivity) hc, add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, hnorm]
  nlinarith
-- @endregion

/-! ### Orbits around a Schwarzschild black hole -/

-- @region relativity.effective_potential
-- @provenance definition
/-- The effective potential for timelike geodesics in the Schwarzschild metric of mass `M`, for a
particle with angular momentum per unit mass `L` (units `G = c = 1`):
`V(r) = (1 − 2M/r)(1 + L²/r²)`. Radial motion obeys `ṙ² = E² − V(r)`. -/
noncomputable def effectivePotential (M L r : ℝ) : ℝ :=
  (1 - 2 * M / r) * (1 + L ^ 2 / r ^ 2)
-- @endregion

-- @region relativity.effective_potential_deriv
-- @provenance independent
/-- **Where circular orbits live.** For `r ≠ 0`,
`V′(r) = 2 (M r² − L² r + 3 M L²) / r⁴`. Circular orbits sit at critical points of `V`, i.e. at
the roots of `M r² − L² r + 3 M L² = 0`. The term `3 M L²` has no Newtonian counterpart. -/
theorem effective_potential_deriv (M L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (effectivePotential M L)
      (2 * (M * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2) / r ^ 4) r := by
  have h1 : HasDerivAt (fun s => 1 - 2 * M / s) (2 * M / r ^ 2) r := by
    have := ((hasDerivAt_inv hr).const_mul (2 * M)).const_sub 1
    convert this using 1
    · funext s
      simp [div_eq_mul_inv]
    · field_simp
  have h2 : HasDerivAt (fun s => 1 + L ^ 2 / s ^ 2) (-2 * L ^ 2 / r ^ 3) r := by
    have hsq : HasDerivAt (fun s => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have := ((hsq.inv (pow_ne_zero 2 hr)).const_mul (L ^ 2)).const_add 1
    convert this using 1
    · funext s
      simp [div_eq_mul_inv]
    · field_simp
  show HasDerivAt (fun s => (1 - 2 * M / s) * (1 + L ^ 2 / s ^ 2)) _ r
  convert h1.mul h2 using 1
  field_simp
  ring
-- @endregion

-- @region relativity.circular_orbit_bound
-- @provenance independent
/-- **No circular orbits with too little angular momentum.** If `M > 0`, `r > 0` and
`M r² − L² r + 3 M L² = 0` (a circular orbit of radius `r`), then `L² ≥ 12 M²`. Proof: completing
the square, `(2 M r − L²)² = L⁴ − 12 M² L²`, so `L² (L² − 12 M²) ≥ 0`, and `L ≠ 0` because
`L = 0` would force `M r² = 0`. -/
theorem circular_orbit_bound {M L r : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hcirc : M * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2 = 0) : 12 * M ^ 2 ≤ L ^ 2 := by
  have hsq : (2 * M * r - L ^ 2) ^ 2 = L ^ 2 * (L ^ 2 - 12 * M ^ 2) := by
    have : (2 * M * r - L ^ 2) ^ 2 = 4 * M * (M * r ^ 2 - L ^ 2 * r) + L ^ 4 := by ring
    rw [this, show M * r ^ 2 - L ^ 2 * r = -(3 * M * L ^ 2) by linarith]
    ring
  have hL : 0 < L ^ 2 := by
    rcases (sq_nonneg L).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hcirc
      have : M * r ^ 2 = 0 := by linarith
      have : 0 < M * r ^ 2 := by positivity
      linarith
  have hprod : 0 ≤ L ^ 2 * (L ^ 2 - 12 * M ^ 2) := hsq ▸ sq_nonneg _
  by_contra hlt
  have : L ^ 2 * (L ^ 2 - 12 * M ^ 2) < 0 := mul_neg_of_pos_of_neg hL (by linarith [not_le.mp hlt])
  linarith
-- @endregion

-- @region relativity.isco
-- @provenance independent
/-- **The innermost stable circular orbit is at `r = 6M`.** At the critical angular momentum
`L² = 12 M²` the two circular orbits (stable and unstable) merge, and the circular-orbit
equation forces `r = 6M`, three times the Schwarzschild radius. Inside it there are no stable
circular orbits: matter in an accretion disc spirals in. -/
theorem isco {M L r : ℝ} (hM : 0 < M) (hL : L ^ 2 = 12 * M ^ 2)
    (hcirc : M * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2 = 0) : r = 6 * M := by
  rw [hL] at hcirc
  have h : M * (r - 6 * M) ^ 2 = 0 := by nlinarith
  have h' : (r - 6 * M) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h0 | h0
    · linarith
    · exact h0
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  linarith
-- @endregion

end Lumenary.Relativity
