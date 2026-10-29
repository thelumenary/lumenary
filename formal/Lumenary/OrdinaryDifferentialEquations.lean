/-
The Lumenary — formal mathematics
Ordinary differential equations: exponential growth and its uniqueness, the integrating factor,
the logistic equation, finite-time blow-up, non-uniqueness for `x' = √|x|`, the harmonic
oscillator and its energy, matrix exponentials, and the Picard–Lindelöf theorem.

What is proved here and what Mathlib provides. Mathlib's `HasDerivAt x v t` says the curve `x`
has velocity `v` at time `t`, so "x solves x' = f(t, x)" is `∀ t, HasDerivAt x (f t (x t)) t`.
The *independent* declarations verify explicit solutions and prove uniqueness results the way
the lesson does — by showing that a cleverly chosen quantity (`x e^{-at}`, or the energy
`x² + x'²`) has zero derivative. They also show *why* the hypotheses of Picard–Lindelöf matter:
`x' = √|x|` has two different solutions with `x(0) = 0` (and `√|x|` is not Lipschitz at `0`),
and `x' = x²` has a solution that escapes to infinity at `t = 1`. The *library* declarations
cite Mathlib's Picard–Lindelöf existence theorem, its Grönwall-based uniqueness theorem, and the
derivative of the exponential of a matrix.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.ExistUnique

namespace Lumenary.OrdinaryDifferentialEquations

open Set Filter Topology Real

/-! ### Exponential growth -/

-- @region ordinary_differential_equations.exp_solves
-- @provenance independent
/-- `x(t) = x₀ e^{a t}` solves `x' = a x` with `x(0) = x₀`. -/
theorem exp_solves (a x₀ t : ℝ) :
    HasDerivAt (fun s => x₀ * exp (a * s)) (a * (x₀ * exp (a * t))) t := by
  have h := ((hasDerivAt_id' t).const_mul a).exp.const_mul x₀
  convert h using 1
  ring
-- @endregion

-- @region ordinary_differential_equations.exp_unique
-- @provenance independent
/-- **Uniqueness for `x' = a x`.** If `y' = a y` everywhere, then `y(t) = y(0) e^{a t}`.
Proof (the integrating factor): `g(t) = y(t) e^{-a t}` has `g' = y' e^{-at} - a y e^{-at} = 0`,
so `g` is constant (Mathlib's `is_const_of_deriv_eq_zero`), and `g(0) = y(0)`. -/
theorem exp_unique {a : ℝ} {y : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (a * y t) t) (t : ℝ) :
    y t = y 0 * exp (a * t) := by
  let g : ℝ → ℝ := fun s => y s * exp (-a * s)
  have hg : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := (hy s).mul (((hasDerivAt_id' s).const_mul (-a)).exp)
    convert h using 1
    ring
  have hconst : g t = g 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simp only [g, mul_zero, exp_zero, mul_one] at hconst
  calc y t = y t * exp (-a * t) * exp (a * t) := by
          rw [mul_assoc, ← exp_add]; ring_nf; simp
    _ = y 0 * exp (a * t) := by rw [hconst]
-- @endregion

-- @region ordinary_differential_equations.integrating_factor
-- @provenance independent
/-- **The integrating factor.** If `P' = p`, then `(y e^{P})' = (y' + p y) e^{P}`. So the linear
equation `y' + p(t) y = q(t)` becomes `(y e^{P})' = q e^{P}`, which is solved by integrating. -/
theorem integrating_factor {y P : ℝ → ℝ} {y' p t : ℝ} (hy : HasDerivAt y y' t)
    (hP : HasDerivAt P p t) :
    HasDerivAt (fun s => y s * exp (P s)) ((y' + p * y t) * exp (P t)) t := by
  have h := hy.mul hP.exp
  convert h using 1
  ring
-- @endregion

-- @region ordinary_differential_equations.logistic_solves
-- @provenance independent
/-- The logistic equation `x' = x (1 - x)` is solved by `x(t) = 1 / (1 + C e^{-t})` for every
`C ≥ 0` (found by separating variables and partial fractions; here we verify it). -/
theorem logistic_solves {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    HasDerivAt (fun s => 1 / (1 + C * exp (-s)))
      ((1 / (1 + C * exp (-t))) * (1 - 1 / (1 + C * exp (-t)))) t := by
  have hpos : 0 < 1 + C * exp (-t) := by positivity
  have hd : HasDerivAt (fun s => 1 + C * exp (-s)) (C * (exp (-t) * (-1))) t :=
    (((hasDerivAt_neg' t).exp).const_mul C).const_add 1
  have h := (hasDerivAt_const t (1 : ℝ)).div hd hpos.ne'
  convert h using 1
  field_simp
  ring
-- @endregion

/-! ### When the hypotheses fail: blow-up and non-uniqueness -/

-- @region ordinary_differential_equations.blowup_solves
-- @provenance independent
/-- `x(t) = 1/(1 - t)` solves `x' = x²` with `x(0) = 1` for `t ≠ 1`… -/
theorem blowup_solves {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt (fun s => 1 / (1 - s)) ((1 / (1 - t)) ^ 2) t := by
  have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hd : HasDerivAt (fun s => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id' t).const_sub 1
  have h := (hasDerivAt_const t (1 : ℝ)).div hd h1
  convert h using 1
  field_simp
  ring
-- @endregion

-- @region ordinary_differential_equations.blowup_tendsto
-- @provenance independent
/-- …and it escapes to `+∞` as `t → 1⁻`: the solution exists only on `(-∞, 1)`, although the
right-hand side `x²` is smooth on all of `ℝ`. -/
theorem blowup_tendsto : Tendsto (fun s : ℝ => 1 / (1 - s)) (𝓝[<] 1) atTop := by
  have hc : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))
    simpa using this
  have h : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mem_Ioi.mpr (sub_pos.mpr (show s < 1 from hs))
  refine h.inv_tendsto_nhdsGT_zero.congr ?_
  intro s
  simp [one_div]
-- @endregion

-- @region ordinary_differential_equations.half_sq
-- @provenance definition
/-- The second solution of `x' = √|x|`, `x(0) = 0`: it stays at `0` until time `0`, then rises
as `t²/4`. Written as `(max t 0)² / 4`. -/
noncomputable def halfSq (t : ℝ) : ℝ := (max t 0) ^ 2 / 4
-- @endregion

-- @region ordinary_differential_equations.half_sq_solves
-- @provenance independent
/-- `halfSq` solves `x' = √|x|` at every time. For `t > 0` it is `t²/4` near `t`, with derivative
`t/2 = √(t²/4)`; for `t < 0` it is `0` near `t`; at `t = 0` it is squeezed: `|x(h)| ≤ h²/4`,
which is `o(h)`, so the derivative is `0 = √0`. -/
theorem halfSq_solves (t : ℝ) : HasDerivAt halfSq (√|halfSq t|) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · -- Left of zero: locally the zero function.
    have hval : halfSq t = 0 := by simp [halfSq, max_eq_right ht.le]
    rw [hval, abs_zero, sqrt_zero]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds ht] with s hs
    simp [halfSq, max_eq_right hs.le]
  · -- At zero: the bound `|x(h)| ≤ h²/4`.
    have hval : halfSq 0 = 0 := by simp [halfSq]
    rw [hval, abs_zero, sqrt_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : ℝ => halfSq (0 + h) - halfSq 0 - h • (0 : ℝ)) =O[𝓝 0]
        fun h : ℝ => h ^ 2 := by
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      simp only [zero_add, hval, sub_zero, smul_zero, norm_pow, Real.norm_eq_abs, one_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ halfSq h by unfold halfSq; positivity)]
      unfold halfSq
      rcases le_total h 0 with hh | hh
      · rw [max_eq_right hh]; nlinarith [sq_nonneg |h|]
      · rw [max_eq_left hh, sq_abs]; linarith [sq_nonneg h]
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)
  · -- Right of zero: locally `s²/4`.
    have hval : halfSq t = t ^ 2 / 4 := by simp [halfSq, max_eq_left ht.le]
    have hsq : √|halfSq t| = t / 2 := by
      rw [hval, abs_of_nonneg (by positivity)]
      rw [show t ^ 2 / 4 = (t / 2) ^ 2 by ring]
      exact sqrt_sq (by linarith)
    rw [hsq]
    have h := (hasDerivAt_pow 2 t).div_const 4
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [lt_mem_nhds ht] with s hs
      simp [halfSq, max_eq_left hs.le]
    · push_cast; ring
-- @endregion

-- @region ordinary_differential_equations.nonunique
-- @provenance independent
/-- **Non-uniqueness.** Both `x ≡ 0` and `halfSq` solve `x' = √|x|` with `x(0) = 0`, and they
are different functions (at `t = 2`, `halfSq 2 = 1`). Picard–Lindelöf does not apply. -/
theorem nonunique :
    (∀ t, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (√|(0 : ℝ)|) t) ∧
      (∀ t, HasDerivAt halfSq (√|halfSq t|) t) ∧ halfSq 0 = 0 ∧ halfSq 2 ≠ 0 := by
  refine ⟨fun t => by simpa using hasDerivAt_const t (0 : ℝ), halfSq_solves, ?_, ?_⟩
  · simp [halfSq]
  · norm_num [halfSq]
-- @endregion

-- @region ordinary_differential_equations.sqrt_abs_not_lipschitz
-- @provenance independent
/-- The reason: `x ↦ √|x|` is not Lipschitz on `[-1, 1]` (Mathlib's `LipschitzOnWith`). A
Lipschitz constant `K` would give `√x ≤ K x` for `0 < x ≤ 1` (compare with the value `0` at `0`),
but `x = 1/(K+1)²` has `√x = 1/(K+1) > K/(K+1)² = K x`. -/
theorem sqrt_abs_not_lipschitz :
    ¬ ∃ K : NNReal, LipschitzOnWith K (fun x : ℝ => √|x|) (Icc (-1) 1) := by
  rintro ⟨K, hK⟩
  set k : ℝ := (K : ℝ) with hk
  have hk0 : 0 ≤ k := K.2
  set x : ℝ := 1 / (k + 1) ^ 2 with hx
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]
    nlinarith
  have hsqrt : √x = 1 / (k + 1) := by
    rw [hx, one_div, one_div, sqrt_inv, sqrt_sq (by linarith)]
  -- The Lipschitz bound between `x` and `0`.
  have hb := hK.dist_le_mul x ⟨by linarith, hxle⟩ 0 ⟨by norm_num, by norm_num⟩
  simp only [Real.dist_eq, abs_zero, sqrt_zero, sub_zero, abs_of_pos hxpos,
    abs_of_nonneg (sqrt_nonneg _)] at hb
  rw [hsqrt] at hb
  -- But `k x = k/(k+1)² < 1/(k+1)`.
  have hlt : k * x < 1 / (k + 1) := by
    have hk1 : 0 < k + 1 := by linarith
    rw [hx, mul_one_div, div_lt_div_iff₀ (by positivity) hk1]
    nlinarith
  linarith
-- @endregion

/-! ### Existence and uniqueness: Picard–Lindelöf -/

-- @region ordinary_differential_equations.picard_lindelof
-- @provenance library
/-- **Picard–Lindelöf, existence.** If on the time interval `[tmin, tmax] ∋ t₀` the vector field
`f t x` is continuous in `t`, `K`-Lipschitz in `x` on the ball of radius `a` about `x₀`, bounded
by `L` there, and `L · (length of time on either side of t₀) ≤ a`, then there is a solution with
`α(t₀) = x₀` on the whole interval. This applies Mathlib's
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`, proved by showing that an iterate
of the Picard map `α ↦ x₀ + ∫_{t₀}^t f(τ, α τ) dτ` is a contraction. -/
theorem picard_lindelof {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a L K : NNReal}
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
  hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
-- @endregion

-- @region ordinary_differential_equations.unique_of_lipschitz
-- @provenance library
/-- **Uniqueness.** If `v t` is `K`-Lipschitz for every `t`, two solutions of `x' = v(t, x)`
defined for all time that agree at one time `t₀` agree everywhere. This applies Mathlib's
`ODE_solution_unique_univ`, whose proof uses Grönwall's inequality, as in the lesson. -/
theorem unique_of_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {K : NNReal} {f g : ℝ → E} {t₀ : ℝ}
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ∀ t, HasDerivAt f (v t (f t)) t) (hg : ∀ t, HasDerivAt g (v t (g t)) t)
    (heq : f t₀ = g t₀) : f = g :=
  ODE_solution_unique_univ (s := fun _ => univ) (fun t => (hv t).lipschitzOnWith)
    (fun t => ⟨hf t, mem_univ _⟩) (fun t => ⟨hg t, mem_univ _⟩) heq
-- @endregion

/-! ### Second-order linear equations: the harmonic oscillator -/

-- @region ordinary_differential_equations.harmonic_solves
-- @provenance independent
/-- `x(t) = A cos ωt + B sin ωt` solves `x'' = -ω² x`: its velocity is
`v(t) = -Aω sin ωt + Bω cos ωt`, and the derivative of `v` is `-ω² x(t)`. -/
theorem harmonic_solves (A B ω t : ℝ) :
    HasDerivAt (fun s => A * cos (ω * s) + B * sin (ω * s))
        (-A * ω * sin (ω * t) + B * ω * cos (ω * t)) t ∧
      HasDerivAt (fun s => -A * ω * sin (ω * s) + B * ω * cos (ω * s))
        (-ω ^ 2 * (A * cos (ω * t) + B * sin (ω * t))) t := by
  have hl : HasDerivAt (fun s => ω * s) ω t := by
    simpa using (hasDerivAt_id' t).const_mul ω
  constructor
  · have h := ((hl.cos).const_mul A).add ((hl.sin).const_mul B)
    convert h using 1
    ring
  · have h := ((hl.sin).const_mul (-A * ω)).add ((hl.cos).const_mul (B * ω))
    convert h using 1
    ring
-- @endregion

-- @region ordinary_differential_equations.oscillator_unique
-- @provenance independent
/-- **Uniqueness via energy.** If `x' = v` and `v' = -x` (so `x'' + x = 0`) with
`x(0) = v(0) = 0`, then `x ≡ 0`. Proof: the energy `E = x² + v²` has
`E' = 2x v + 2v(-x) = 0`, so `E` is constant, equal to `E(0) = 0`; hence `x(t)² ≤ E(t) = 0`. -/
theorem oscillator_unique {x v : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (-x t) t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (t : ℝ) : x t = 0 := by
  let E : ℝ → ℝ := fun s => x s ^ 2 + v s ^ 2
  have hE : ∀ s, HasDerivAt E 0 s := by
    intro s
    have h := ((hx s).pow 2).add ((hv s).pow 2)
    convert h using 1
    push_cast
    ring
  have hconst : E t = E 0 :=
    is_const_of_deriv_eq_zero (fun s => (hE s).differentiableAt) (fun s => (hE s).deriv) t 0
  have hE0 : E 0 = 0 := by simp [E, hx0, hv0]
  have hsq : x t ^ 2 + v t ^ 2 = 0 := by
    have := hconst.trans hE0
    simpa [E] using this
  nlinarith [sq_nonneg (x t), sq_nonneg (v t)]
-- @endregion

/-! ### Linear systems: the matrix exponential -/

section MatrixExp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- @region ordinary_differential_equations.matrix_exp_solves
-- @provenance library
/-- For a square matrix `A`, the fundamental matrix `X(t) = e^{tA}` solves `X' = A X` (and
`X(0) = I`), so `x(t) = e^{tA} x₀` solves `x' = A x`, `x(0) = x₀`. This applies Mathlib's
`hasDerivAt_exp_smul_const'`, valid in any complete normed algebra; matrices become one by
choosing an operator norm (here the `L^∞` operator norm, as local instances). -/
theorem matrix_exp_solves {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (A * NormedSpace.exp (t • A)) t :=
  hasDerivAt_exp_smul_const' A t
-- @endregion

end MatrixExp

end Lumenary.OrdinaryDifferentialEquations
