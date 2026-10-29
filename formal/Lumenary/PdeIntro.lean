/-
The Lumenary — formal mathematics
Partial differential equations and Fourier series: separated solutions of the heat, wave and
Laplace equations, d'Alembert's travelling waves, orthogonality of sines, a discrete maximum
principle for the explicit heat scheme, and Mathlib's Fourier theory on the circle.

What is proved here and what Mathlib provides. The *independent* declarations verify, by explicit
derivative computations, that the lesson's separated solutions really solve their equations
(`e^{-k n² t} sin(n x)` for the heat equation, `e^{n y} sin(n x)` for Laplace's equation) and that
`f(x - c t) + g(x + c t)` solves the wave equation; they prove the orthogonality relation
`∫₀^π sin(m x) sin(n x) dx = 0` (m ≠ n) from an antiderivative; and they prove the discrete
maximum principle for the explicit finite-difference heat scheme when `r = k Δt/Δx² ≤ 1/2`,
together with the growth of a sawtooth mode when `r = 1`. The *library* declarations cite
Mathlib's Fourier analysis on `AddCircle T`: orthonormality of `e^{2π i n x/T}` in `L²`,
convergence of Fourier series in `L²`, Parseval's identity, uniform convergence when the
coefficients are summable, and the Basel sum `∑ 1/n² = π²/6`. Not formalised: Dirichlet's
pointwise convergence theorem, the Gibbs phenomenon, the continuous maximum principle and the
energy method (Mathlib has no PDE library at this version).
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues

namespace Lumenary.PdeIntro

open Real MeasureTheory

/-! ### Separated solutions -/

-- @region pde_intro.heat_mode
-- @provenance independent
/-- **A separated solution of the heat equation.** `u(t, x) = e^{-k n² t} sin(n x)` satisfies
`u_t = k u_xx`: differentiating in `t` brings down `-k n²`, and differentiating twice in `x`
brings down `-n²`. Both sides equal `-k n² e^{-k n² t} sin(n x)`. -/
theorem heat_mode (k n t x : ℝ) :
    deriv (fun s => exp (-k * n ^ 2 * s) * sin (n * x)) t =
      k * deriv (fun y => deriv (fun z => exp (-k * n ^ 2 * t) * sin (n * z)) y) x := by
  -- First and second derivatives in `x`.
  have hx1 : ∀ y, HasDerivAt (fun z => exp (-k * n ^ 2 * t) * sin (n * z))
      (exp (-k * n ^ 2 * t) * (cos (n * y) * n)) y := fun y =>
    (((hasDerivAt_id' y).const_mul n).sin.congr_deriv (by simp)).const_mul _
  have hfun : deriv (fun z => exp (-k * n ^ 2 * t) * sin (n * z)) =
      fun y => exp (-k * n ^ 2 * t) * (cos (n * y) * n) := funext fun y => (hx1 y).deriv
  have hx2 : HasDerivAt (fun y => exp (-k * n ^ 2 * t) * (cos (n * y) * n))
      (exp (-k * n ^ 2 * t) * (-sin (n * x) * n * n)) x := by
    have := ((((hasDerivAt_id' x).const_mul n).cos).mul_const n).const_mul (exp (-k * n ^ 2 * t))
    convert this using 1; ring
  -- The derivative in `t`.
  have ht : HasDerivAt (fun s => exp (-k * n ^ 2 * s) * sin (n * x))
      (exp (-k * n ^ 2 * t) * (-k * n ^ 2) * sin (n * x)) t := by
    have := (((hasDerivAt_id' t).const_mul (-k * n ^ 2)).exp).mul_const (sin (n * x))
    convert this using 1; ring
  rw [ht.deriv, hfun, hx2.deriv]
  ring
-- @endregion

-- @region pde_intro.heat_mode_boundary
-- @provenance independent
/-- The heat mode `e^{-k n² t} sin(n x)` with `n` a natural number vanishes at both ends of
`[0, π]`, so it satisfies the Dirichlet boundary conditions `u(t, 0) = u(t, π) = 0` for all `t`.
(This is why the separation constants are `n²` with `n = 1, 2, 3, …`.) -/
theorem heat_mode_boundary (k t : ℝ) (n : ℕ) :
    exp (-k * (n : ℝ) ^ 2 * t) * sin (n * 0) = 0 ∧
      exp (-k * (n : ℝ) ^ 2 * t) * sin (n * π) = 0 := by
  constructor
  · simp
  · rw [sin_nat_mul_pi, mul_zero]
-- @endregion

-- @region pde_intro.laplace_mode
-- @provenance independent
/-- **A separated solution of Laplace's equation.** `u(x, y) = e^{n y} sin(n x)` is harmonic:
`u_xx = -n² u` and `u_yy = n² u`, so `u_xx + u_yy = 0`. -/
theorem laplace_mode (n x y : ℝ) :
    deriv (fun a => deriv (fun b => exp (n * y) * sin (n * b)) a) x +
      deriv (fun a => deriv (fun b => exp (n * b) * sin (n * x)) a) y = 0 := by
  have h1 : deriv (fun b => exp (n * y) * sin (n * b)) = fun a => exp (n * y) * (cos (n * a) * n) :=
    funext fun a => ((((hasDerivAt_id' a).const_mul n).sin.congr_deriv (by simp)).const_mul _).deriv
  have h2 : deriv (fun b => exp (n * b) * sin (n * x)) = fun a => exp (n * a) * n * sin (n * x) := by
    funext a
    have := (((hasDerivAt_id' a).const_mul n).exp).mul_const (sin (n * x))
    rw [this.deriv]; ring
  have h3 : HasDerivAt (fun a => exp (n * y) * (cos (n * a) * n))
      (exp (n * y) * (-sin (n * x) * n * n)) x := by
    have := ((((hasDerivAt_id' x).const_mul n).cos).mul_const n).const_mul (exp (n * y))
    convert this using 1; ring
  have h4 : HasDerivAt (fun a => exp (n * a) * n * sin (n * x))
      (exp (n * y) * n * n * sin (n * x)) y := by
    have := ((((hasDerivAt_id' y).const_mul n).exp).mul_const n).mul_const (sin (n * x))
    convert this using 1; ring
  rw [h1, h2, h3.deriv, h4.deriv]
  ring
-- @endregion

-- @region pde_intro.dalembert_solves
-- @provenance independent
/-- **d'Alembert's travelling waves solve the wave equation.** If `f` and `g` are twice
differentiable, then `u(t, x) = f(x - c t) + g(x + c t)` satisfies `u_tt = c² u_xx`. By the chain
rule `u_t = -c f'(x - c t) + c g'(x + c t)` and `u_tt = c² f''(x - c t) + c² g''(x + c t)`, while
`u_xx = f''(x - c t) + g''(x + c t)`. (The converse — every C² solution has this form — is proved
in the lesson by changing to the characteristic coordinates `x ± c t`.) -/
theorem dalembert_solves {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g)) (c t x : ℝ) :
    deriv (fun s => deriv (fun r => f (x - c * r) + g (x + c * r)) s) t =
      c ^ 2 * deriv (fun y => deriv (fun z => f (z - c * t) + g (z + c * t)) y) x := by
  -- Inner derivatives.
  have hin : ∀ s : ℝ, HasDerivAt (fun r => x - c * r) (-c) s := fun s => by
    simpa using ((hasDerivAt_id' s).const_mul c).const_sub x
  have hin' : ∀ s : ℝ, HasDerivAt (fun r => x + c * r) c s := fun s => by
    simpa using ((hasDerivAt_id' s).const_mul c).const_add x
  have ht1 : deriv (fun r => f (x - c * r) + g (x + c * r)) =
      fun s => deriv f (x - c * s) * (-c) + deriv g (x + c * s) * c := by
    funext s
    exact (((hf _).hasDerivAt.comp s (hin s)).add ((hg _).hasDerivAt.comp s (hin' s))).deriv
  have ht2 : HasDerivAt (fun s => deriv f (x - c * s) * (-c) + deriv g (x + c * s) * c)
      (deriv (deriv f) (x - c * t) * (-c) * (-c) + deriv (deriv g) (x + c * t) * c * c) t :=
    (((hf' _).hasDerivAt.comp t (hin t)).mul_const (-c)).add
      (((hg' _).hasDerivAt.comp t (hin' t)).mul_const c)
  have hsh : ∀ y : ℝ, HasDerivAt (fun z => z - c * t) 1 y := fun y => (hasDerivAt_id' y).sub_const _
  have hsh' : ∀ y : ℝ, HasDerivAt (fun z => z + c * t) 1 y := fun y => (hasDerivAt_id' y).add_const _
  have hx1 : deriv (fun z => f (z - c * t) + g (z + c * t)) =
      fun y => deriv f (y - c * t) + deriv g (y + c * t) := by
    funext y
    have := ((hf _).hasDerivAt.comp y (hsh y)).add ((hg _).hasDerivAt.comp y (hsh' y))
    rw [mul_one, mul_one] at this
    exact this.deriv
  have hx2 : HasDerivAt (fun y => deriv f (y - c * t) + deriv g (y + c * t))
      (deriv (deriv f) (x - c * t) + deriv (deriv g) (x + c * t)) x := by
    have := ((hf' _).hasDerivAt.comp x (hsh x)).add ((hg' _).hasDerivAt.comp x (hsh' x))
    rw [mul_one, mul_one] at this
    exact this
  rw [ht1, ht2.deriv, hx1, hx2.deriv]
  ring
-- @endregion

/-! ### Orthogonality of the sine modes -/

-- @region pde_intro.sin_orthogonal
-- @provenance independent
/-- **Orthogonality of sines on `[0, π]`.** For distinct natural numbers `m ≠ n`,
`∫₀^π sin(m x) sin(n x) dx = 0`. Proof: `sin a sin b = (cos(a - b) - cos(a + b))/2`, which has the
antiderivative `sin((m - n)x)/(2(m - n)) - sin((m + n)x)/(2(m + n))`; this vanishes at `0` and at
`π` because `sin(k π) = 0` for every integer `k`. This is what lets us read off Fourier sine
coefficients by integrating against `sin(n x)`. -/
theorem sin_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..π, sin (m * x) * sin (n * x) = 0 := by
  have hd : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hs : (m : ℝ) + n ≠ 0 := by
    have : (0 : ℝ) < m + n := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; have : 0 < n := Nat.pos_of_ne_zero (Ne.symm hmn); simp; exact_mod_cast this
      · have : (0 : ℝ) < m := by exact_mod_cast h
        positivity
    exact this.ne'
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) π, HasDerivAt
      (fun x => sin ((m - n) * x) / (2 * (m - n)) - sin ((m + n) * x) / (2 * (m + n)))
      (sin (m * x) * sin (n * x)) x := by
    intro x _
    have h1 := (((hasDerivAt_id' x).const_mul ((m : ℝ) - n)).sin).div_const (2 * ((m : ℝ) - n))
    have h2 := (((hasDerivAt_id' x).const_mul ((m : ℝ) + n)).sin).div_const (2 * ((m : ℝ) + n))
    refine (h1.sub h2).congr_deriv ?_
    rw [show ((m : ℝ) - n) * x = (m * x) - (n * x) by ring,
      show ((m : ℝ) + n) * x = (m * x) + (n * x) by ring, cos_sub, cos_add]
    field_simp
    ring
  have hcont : Continuous fun x : ℝ => sin (m * x) * sin (n * x) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have hk1 : sin (((m : ℝ) - n) * π) = 0 := by
    have := sin_int_mul_pi ((m : ℤ) - n); push_cast at this; exact this
  have hk2 : sin (((m : ℝ) + n) * π) = 0 := by
    have := sin_nat_mul_pi (m + n); push_cast at this; exact this
  simp [hk1, hk2]
-- @endregion

/-! ### The explicit finite-difference scheme and its maximum principle -/

-- @region pde_intro.heat_step
-- @provenance definition
/-- One step of the explicit scheme for `u_t = k u_xx` on a grid of spacing `Δx` with time step
`Δt`: the new value at site `j` is `r u_{j-1} + (1 - 2r) u_j + r u_{j+1}`, where
`r = k Δt / Δx²`. (Sites are indexed by `ℤ`, an unbounded rod; boundary conditions are treated in
the lesson.) -/
def heatStep (r : ℝ) (u : ℤ → ℝ) : ℤ → ℝ :=
  fun j => r * u (j - 1) + (1 - 2 * r) * u j + r * u (j + 1)
-- @endregion

-- @region pde_intro.heat_step_bounded
-- @provenance independent
/-- **Discrete maximum principle, one step.** If `0 ≤ r ≤ 1/2`, the new value is a *convex
combination* of three old values (the weights `r, 1 - 2r, r` are non-negative and sum to `1`), so
if all old values lie in `[m, M]`, so do all new ones. -/
theorem heatStep_bounded {r m M : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) {u : ℤ → ℝ}
    (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (j : ℤ) : m ≤ heatStep r u j ∧ heatStep r u j ≤ M := by
  have hw : 0 ≤ 1 - 2 * r := by linarith
  obtain ⟨a1, a2⟩ := hu (j - 1)
  obtain ⟨b1, b2⟩ := hu j
  obtain ⟨c1, c2⟩ := hu (j + 1)
  simp only [heatStep]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left a1 hr0, mul_le_mul_of_nonneg_left b1 hw,
      mul_le_mul_of_nonneg_left c1 hr0]
  · nlinarith [mul_le_mul_of_nonneg_left a2 hr0, mul_le_mul_of_nonneg_left b2 hw,
      mul_le_mul_of_nonneg_left c2 hr0]
-- @endregion

-- @region pde_intro.heat_iterate_bounded
-- @provenance independent
/-- **Discrete maximum principle, all time.** With `0 ≤ r ≤ 1/2`, after any number of steps the
solution stays between the minimum and maximum of the initial data. In particular the scheme is
*stable* in the maximum norm: errors in the data are never amplified. Induction on the number of
steps, using `heatStep_bounded`. -/
theorem heat_iterate_bounded {r m M : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) {u : ℤ → ℝ}
    (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (steps : ℕ) (j : ℤ) :
    m ≤ (heatStep r)^[steps] u j ∧ (heatStep r)^[steps] u j ≤ M := by
  induction steps generalizing j with
  | zero => exact hu j
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact heatStep_bounded hr0 hr1 ih j
-- @endregion

-- @region pde_intro.heat_step_unstable
-- @provenance independent
/-- **Instability when `r > 1/2`.** With `r = 1`, the sawtooth `u_j = (-1)^j` is multiplied by
`1 - 4r = -3` at every step, so after `N` steps it has grown by `3^N`: rounding errors of this
shape explode. In general this mode is multiplied by `1 - 4r`, which has absolute value at most
`1` exactly when `0 ≤ r ≤ 1/2` (von Neumann's stability condition). -/
theorem heat_step_unstable (j : ℤ) :
    heatStep 1 (fun i => (-1 : ℝ) ^ i) j = -3 * (-1 : ℝ) ^ j := by
  simp only [heatStep]
  rw [zpow_sub_one₀ (by norm_num), zpow_add_one₀ (by norm_num)]
  ring
-- @endregion

/-! ### Fourier series on the circle (Mathlib) -/

-- @region pde_intro.fourier_orthonormal
-- @provenance library
/-- **The exponentials `e_n(x) = e^{2π i n x / T}` are orthonormal in `L²` of the circle
`ℝ/Tℤ`** (with normalised Haar measure). This applies Mathlib's `orthonormal_fourier`. -/
theorem fourier_orthonormal (T : ℝ) [Fact (0 < T)] :
    Orthonormal ℂ (@fourierLp T _ 2 _) :=
  orthonormal_fourier
-- @endregion

-- @region pde_intro.fourier_series_l2
-- @provenance library
/-- **Fourier series converge in `L²`.** For every square-integrable `f` on the circle,
`∑ₙ f̂(n) eₙ = f` with convergence in the `L²` norm: the exponentials form a Hilbert basis.
This applies Mathlib's `hasSum_fourier_series_L2`. -/
theorem fourier_series_l2 (T : ℝ) [Fact (0 < T)] (f : Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f :=
  hasSum_fourier_series_L2 f
-- @endregion

-- @region pde_intro.parseval
-- @provenance library
/-- **Parseval's identity**: `∑ₙ |f̂(n)|² = ∫ |f|²` (normalised measure on the circle). This
applies Mathlib's `tsum_sq_fourierCoeff`. -/
theorem parseval (T : ℝ) [Fact (0 < T)] (f : Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle :=
  tsum_sq_fourierCoeff f
-- @endregion

-- @region pde_intro.fourier_uniform
-- @provenance library
/-- **Absolutely summable coefficients give uniform convergence.** If `f` is continuous on the
circle and `∑ |f̂(n)| < ∞` (summability in `ℂ`), then the Fourier series converges to `f` in the
sup norm of `C(ℝ/Tℤ, ℂ)`, hence uniformly and at every point. This applies Mathlib's
`hasSum_fourier_series_of_summable`. -/
theorem fourier_uniform (T : ℝ) [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (h : Summable (fourierCoeff f)) :
    HasSum (fun i => fourierCoeff f i • fourier i) f :=
  hasSum_fourier_series_of_summable h
-- @endregion

-- @region pde_intro.basel
-- @provenance library
/-- **Basel problem**: `∑_{n ≥ 1} 1/n² = π²/6`. The lesson derives it from Parseval's identity for
the sawtooth `f(x) = x` on `(-π, π)`; Mathlib proves it (`hasSum_zeta_two`) via Bernoulli
polynomials and Fourier series. (The `n = 0` term is `1/0 = 0` in Lean's conventions.) -/
theorem basel : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two
-- @endregion

end Lumenary.PdeIntro
