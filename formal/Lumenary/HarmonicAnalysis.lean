/-
The Lumenary — formal mathematics
Fourier and harmonic analysis: orthogonality of characters, Parseval, the Riemann–Lebesgue
lemma, Plancherel, the self-dual Gaussian, Poisson summation and the theta functional equation.

Mathlib's Fourier analysis is extensive: the exponentials `fourier n` on `AddCircle T` form a
Hilbert basis of `L²` (`orthonormal_fourier`, `fourierBasis`), with Parseval's identity
(`hasSum_sq_fourierCoeff`); the Fourier transform `𝓕` on `ℝⁿ` with the Riemann–Lebesgue lemma,
Fourier inversion and Plancherel on `L²` (`MeasureTheory.Lp.norm_fourier_eq`); the Gaussian
(`fourier_gaussian_pi`); Poisson summation (`SchwartzMap.tsum_eq_tsum_fourier`); and Jacobi's
theta functional equation and `ζ(2) = π²/6`, both proved with Fourier analysis. Proved here from
more basic facts: orthogonality of the characters of `ℤ/N` (a geometric series), the decay of
Fourier coefficients of `L²` functions (from Parseval), and the self-duality of `e^{-πx²}`.
Not in Mathlib (or here): Fejér's theorem, Carleson's theorem and the uncertainty principle.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

open MeasureTheory Filter Topology Complex
open scoped Real FourierTransform

namespace Lumenary.HarmonicAnalysis

/-! ### Orthogonality -/

-- @region harmonic_analysis.roots_of_unity_sum
-- @provenance independent
/-- **Orthogonality of characters on `ℤ/N`.** If `z^N = 1` and `z ≠ 1`, then
`1 + z + ⋯ + z^{N-1} = 0`. Proof: `(∑ zᵏ)(z − 1) = z^N − 1 = 0` and `z − 1 ≠ 0`. With
`z = e^{2πi(m−n)/N}` this says the discrete exponentials are orthogonal — the finite model of
Fourier series and the basis of the fast Fourier transform. -/
theorem roots_of_unity_sum {z : ℂ} {N : ℕ} (hz : z ^ N = 1) (hz1 : z ≠ 1) :
    ∑ k ∈ Finset.range N, z ^ k = 0 := by
  have h : (∑ k ∈ Finset.range N, z ^ k) * (z - 1) = 0 := by
    rw [geom_sum_mul, hz, sub_self]
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz1)
-- @endregion

-- @region harmonic_analysis.orthonormal_exponentials
-- @provenance library
/-- **The exponentials are orthonormal** in `L²` of the circle `ℝ/Tℤ` with normalised Haar
measure: `⟪eₘ, eₙ⟫ = δₘₙ` for `eₙ(x) = e^{2πinx/T}`. This is Mathlib's `orthonormal_fourier`;
`span_fourierLp_closure_eq_top` adds that their span is dense, so they form a Hilbert basis. -/
theorem orthonormal_exponentials (T : ℝ) [Fact (0 < T)] :
    Orthonormal ℂ (fun n : ℤ => fourierLp (T := T) 2 n) :=
  orthonormal_fourier
-- @endregion

/-! ### Parseval and the decay of Fourier coefficients -/

-- @region harmonic_analysis.parseval
-- @provenance library
/-- **Parseval's identity.** For `f ∈ L²(ℝ/Tℤ)`, `∑ₙ |f̂(n)|² = ∫ |f|²` (normalised measure).
This is Mathlib's `hasSum_sq_fourierCoeff`, a consequence of the exponentials forming a Hilbert
basis. -/
theorem parseval (T : ℝ) [Fact (0 < T)] (f : Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
      (∫ t : AddCircle T, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle) :=
  hasSum_sq_fourierCoeff f
-- @endregion

-- @region harmonic_analysis.fourier_coeff_tendsto_zero
-- @provenance independent
/-- **Riemann–Lebesgue lemma for `L²` functions on the circle**, from Parseval: the series
`∑ |f̂(n)|²` converges, so its terms tend to `0` (along the cofinite filter, i.e. as `|n| → ∞`),
and hence so do the coefficients `f̂(n) = √(|f̂(n)|²)`. -/
theorem fourier_coeff_tendsto_zero (T : ℝ) [Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  have hsq : Tendsto (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) cofinite (𝓝 0) :=
    (parseval T f).summable.tendsto_cofinite_zero
  have hnorm : Tendsto (fun n : ℤ => ‖fourierCoeff f n‖) cofinite (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
-- @endregion

-- @region harmonic_analysis.riemann_lebesgue
-- @provenance library
/-- **Riemann–Lebesgue lemma** on `ℝ`: for integrable `f`, `f̂(ξ) = ∫ e^{−2πixξ} f(x) dx → 0`
as `|ξ| → ∞`. This applies Mathlib's `tendsto_integral_exp_inner_smul_cocompact` (stated on any
finite-dimensional real inner product space; for `ℝ` the cocompact filter is `|ξ| → ∞`). -/
theorem riemann_lebesgue (f : ℝ → ℂ) :
    Tendsto (fun ξ : ℝ => ∫ x : ℝ, 𝐞 (-(ξ * x)) • f x) (cocompact ℝ) (𝓝 0) := by
  simpa using tendsto_integral_exp_inner_smul_cocompact f
-- @endregion

/-! ### The Fourier transform on `ℝ` -/

-- @region harmonic_analysis.fourier_bound
-- @provenance independent
/-- **The Fourier transform is bounded from `L¹` to `L^∞`:** `|f̂(ξ)| ≤ ∫ |f|` for every `ξ`,
because `|∫ g| ≤ ∫ |g|` and the character `e^{−2πixξ}` has modulus `1`. (For non-integrable `f`
both sides are `0` under Lean's convention for the Bochner integral.) -/
theorem fourier_bound (f : ℝ → ℂ) (ξ : ℝ) :
    ‖∫ x : ℝ, 𝐞 (-(ξ * x)) • f x‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  calc ‖∫ x : ℝ, 𝐞 (-(ξ * x)) • f x‖ ≤ ∫ x : ℝ, ‖𝐞 (-(ξ * x)) • f x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f x‖ := by
        congr 1
        ext x
        simp
-- @endregion

-- @region harmonic_analysis.plancherel
-- @provenance library
/-- **Plancherel's theorem.** The Fourier transform, defined on `L¹ ∩ L²` and extended by
continuity, is an isometry of `L²(ℝ)`: `‖𝓕 f‖₂ = ‖f‖₂` (indeed a unitary map, with inverse the
conjugate transform). This is Mathlib's `MeasureTheory.Lp.norm_fourier_eq`. -/
theorem plancherel (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  Lp.norm_fourier_eq f
-- @endregion

-- @region harmonic_analysis.gaussian_self_dual
-- @provenance library
/-- **The Gaussian `e^{−πx²}` is its own Fourier transform**, with the normalisation
`f̂(ξ) = ∫ f(x) e^{−2πixξ} dx`. Obtained from Mathlib's `fourier_gaussian_pi`, which computes the
transform of `e^{−πbx²}` for `Re b > 0`, by setting `b = 1` and simplifying `1/1^{1/2} = 1`. -/
theorem gaussian_self_dual :
    (𝓕 fun x : ℝ => cexp (-π * x ^ 2)) = fun ξ : ℝ => cexp (-π * ξ ^ 2) := by
  have h := fourier_gaussian_pi (b := 1) (by simp)
  simpa using h
-- @endregion

-- @region harmonic_analysis.poisson_summation
-- @provenance library
/-- **Poisson summation formula.** For a Schwartz function `f` on `ℝ`,
`∑ₙ f(x + n) = ∑ₖ f̂(k) e^{2πikx}`; at `x = 0`, `∑ f(n) = ∑ f̂(k)`. The left side is a
`1`-periodic function whose Fourier coefficients are the `f̂(k)`. This is Mathlib's
`SchwartzMap.tsum_eq_tsum_fourier`. -/
theorem poisson_summation (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' k : ℤ, 𝓕 f k * fourier k (x : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f x
-- @endregion

-- @region harmonic_analysis.theta_functional_equation
-- @provenance library
/-- **Jacobi's theta functional equation** `θ(−1/τ) = (−iτ)^{1/2} θ(τ)` for
`θ(τ) = ∑ₙ e^{πin²τ}` on the upper half-plane — Poisson summation applied to a Gaussian. Riemann
derived the functional equation of `ζ(s)` from it. This is Mathlib's `jacobiTheta_S_smul`. -/
theorem theta_functional_equation (τ : UpperHalfPlane) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ :=
  jacobiTheta_S_smul τ
-- @endregion

-- @region harmonic_analysis.basel
-- @provenance library
/-- **`∑ 1/n² = π²/6`**, which Mathlib proves with Fourier series (Parseval applied to Bernoulli
polynomials). The `n = 0` term is `1/0 = 0` in Lean's conventions. This is Mathlib's
`hasSum_zeta_two`. -/
theorem basel : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two
-- @endregion

end Lumenary.HarmonicAnalysis
