/-
The Lumenary — formal mathematics
Mathematical biology: the logistic equation and the logistic map (fixed points, stability, the
period-2 cycle), the Lotka–Volterra conserved quantity and cycle averages, the SIR epidemic
model (conservation, the threshold `R₀ S/N > 1`, the invariant behind the final-size
relation, herd immunity), and the trace–determinant test for stability.

Mathlib's `HasDerivAt f f' t` expresses "the derivative of `f` at `t` is `f'`", so "`(x, y)`
solves the system" is a family of `HasDerivAt` hypotheses. Proved here
(`@provenance independent`): every algebraic and differential identity listed above — each a
computation that mirrors the lesson. Cited from Mathlib (`@provenance library`): the Banach
fixed-point theorem, which explains why iterating a contracting map converges. Not
formalised: existence of solutions, the linearisation theorem (Hartman–Grobman is not in
Mathlib), Poincaré–Bendixson, chaos for the logistic map and Feigenbaum's constant.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Complex.Basic

open Real Filter Topology

namespace Lumenary.MathematicalBiology

/-! ### Logistic growth -/

-- @region mathematical_biology.logistic_ode_solves
-- @provenance independent
/-- **The logistic equation** `N' = r N (1 − N/K)` is solved by
`N(t) = K / (1 + C e^{−rt})` (found by separation of variables; here verified by
differentiation). With `C = K/N₀ − 1` this is the solution with `N(0) = N₀`. -/
theorem logistic_ode_solves {r K C : ℝ} (hK : K ≠ 0) (hC : 0 ≤ C) (t : ℝ) :
    HasDerivAt (fun s => K / (1 + C * exp (-(r * s))))
      (r * (K / (1 + C * exp (-(r * t)))) * (1 - K / (1 + C * exp (-(r * t))) / K)) t := by
  have hpos : 0 < 1 + C * exp (-(r * t)) := by positivity
  have h0 := (hasDerivAt_id t).const_mul (-r)
  have hinner : HasDerivAt (fun s => -(r * s)) (-r) t := by
    convert h0 using 1
    · funext s
      simp only [id]
      ring
    · ring
  have hd : HasDerivAt (fun s => 1 + C * exp (-(r * s))) (C * (exp (-(r * t)) * (-r))) t :=
    ((hinner.exp).const_mul C).const_add 1
  have h := (hasDerivAt_const t K).div hd hpos.ne'
  convert h using 1
  field_simp
  ring
-- @endregion

-- @region mathematical_biology.logistic_ode_limit
-- @provenance independent
/-- Every positive logistic solution approaches the **carrying capacity**: if `r > 0` then
`K / (1 + C e^{−rt}) → K` as `t → ∞`, because `e^{−rt} → 0`. -/
theorem logistic_ode_limit {r K C : ℝ} (hr : 0 < r) :
    Tendsto (fun t => K / (1 + C * exp (-(r * t)))) atTop (𝓝 K) := by
  have hexp : Tendsto (fun t => exp (-(r * t))) atTop (𝓝 0) := by
    have : Tendsto (fun t => r * t) atTop atTop := tendsto_id.const_mul_atTop hr
    exact tendsto_exp_neg_atTop_nhds_zero.comp this |>.congr fun t => rfl
  have hden : Tendsto (fun t => 1 + C * exp (-(r * t))) atTop (𝓝 1) := by
    simpa using (hexp.const_mul C).const_add 1
  have h := (tendsto_const_nhds (x := K)).div hden one_ne_zero
  rw [div_one] at h
  exact h
-- @endregion

/-! ### The logistic map -/

-- @region mathematical_biology.logistic_map
-- @provenance definition
/-- The **logistic map** `f_r(x) = r x (1 − x)`, a discrete-time model of a population
(as a fraction of its maximum) in non-overlapping generations. -/
def logisticMap (r x : ℝ) : ℝ := r * x * (1 - x)
-- @endregion

-- @region mathematical_biology.logistic_fixed_points
-- @provenance independent
/-- **Fixed points of the logistic map.** For `r ≠ 0`, `f_r(x) = x` exactly when `x = 0`
(extinction) or `x = 1 − 1/r` (the non-trivial equilibrium, in `(0, 1)` when `r > 1`).
Proof: `r x (1 − x) − x = x (r − 1 − r x)`. -/
theorem logistic_fixed_points {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    logisticMap r x = x ↔ x = 0 ∨ x = 1 - 1 / r := by
  unfold logisticMap
  constructor
  · intro h
    have hfac : x * (r - 1 - r * x) = 0 := by linarith [h]
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · right
      field_simp
      linarith
  · rintro (rfl | rfl)
    · ring
    · field_simp
      ring
-- @endregion

-- @region mathematical_biology.logistic_map_deriv
-- @provenance independent
/-- The derivative of the logistic map is `f_r'(x) = r (1 − 2x)`; at the non-trivial fixed
point `x* = 1 − 1/r` it equals `2 − r`. -/
theorem logistic_map_deriv {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (logisticMap r) (2 - r) (1 - 1 / r) := by
  have h : HasDerivAt (fun x => r * x * (1 - x)) (r * 1 * (1 - (1 - 1 / r)) + r * (1 - 1 / r) * (-1))
      (1 - 1 / r) :=
    ((hasDerivAt_id' _).const_mul r).mul ((hasDerivAt_id' _).const_sub 1 |>.congr_deriv (by simp))
  have hv : r * 1 * (1 - (1 - 1 / r)) + r * (1 - 1 / r) * (-1) = 2 - r := by
    field_simp
    ring
  rw [hv] at h
  exact h
-- @endregion

-- @region mathematical_biology.logistic_stable_iff
-- @provenance independent
/-- **Stability of the non-trivial equilibrium.** A fixed point of a smooth map is
asymptotically stable when `|f'(x*)| < 1`; here `|2 − r| < 1` exactly when `1 < r < 3`.
At `r = 3` the multiplier passes through `−1` and the period-doubling cascade begins. -/
theorem logistic_stable_iff (r : ℝ) : |2 - r| < 1 ↔ 1 < r ∧ r < 3 := by
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
-- @endregion

-- @region mathematical_biology.logistic_period_two
-- @provenance independent
/-- **The period-2 cycle.** For `r ≥ 3`, with `s = √((r − 3)(r + 1))`, the points
`x± = (r + 1 ± s)/(2r)` are swapped by the logistic map: `f_r(x₊) = x₋` and `f_r(x₋) = x₊`.
(They coincide with the fixed point `1 − 1/r` at `r = 3` and separate for `r > 3`.)
Proof: expand, using `s² = r² − 2r − 3`. -/
theorem logistic_period_two {r : ℝ} (hr : 3 ≤ r) :
    let s := Real.sqrt ((r - 3) * (r + 1))
    logisticMap r ((r + 1 + s) / (2 * r)) = (r + 1 - s) / (2 * r) ∧
      logisticMap r ((r + 1 - s) / (2 * r)) = (r + 1 + s) / (2 * r) := by
  intro s
  have hr0 : r ≠ 0 := by linarith
  have hs : s ^ 2 = (r - 3) * (r + 1) := Real.sq_sqrt (by nlinarith)
  unfold logisticMap
  constructor
  · field_simp
    linear_combination -hs
  · field_simp
    linear_combination -hs
-- @endregion

-- @region mathematical_biology.period_two_multiplier
-- @provenance independent
/-- **Stability of the 2-cycle.** The multiplier of the cycle — the derivative of `f_r ∘ f_r`
along it, `f_r'(x₊) f_r'(x₋) = r²(1 − 2x₊)(1 − 2x₋)` — equals `−r² + 2r + 4`. It lies in
`(−1, 1)` exactly for `3 < r < 1 + √6 ≈ 3.449`, where the 2-cycle is stable and the next
doubling begins. -/
theorem period_two_multiplier {r : ℝ} (hr : 3 ≤ r) :
    let s := Real.sqrt ((r - 3) * (r + 1))
    (r * (1 - 2 * ((r + 1 + s) / (2 * r)))) * (r * (1 - 2 * ((r + 1 - s) / (2 * r)))) =
      -r ^ 2 + 2 * r + 4 := by
  intro s
  have hr0 : r ≠ 0 := by linarith
  have hs : s ^ 2 = (r - 3) * (r + 1) := Real.sq_sqrt (by nlinarith)
  field_simp
  linear_combination -hs
-- @endregion

-- @region mathematical_biology.contraction_converges
-- @provenance library
/-- **Why stable fixed points attract: the Banach fixed-point theorem.** If a map of a complete
metric space is a contraction (`dist (f x) (f y) ≤ K dist x y` with `K < 1`), its iterates
from any starting point converge to its unique fixed point. Near a fixed point with
`|f'(x*)| < 1` a smooth map is a contraction of a small interval, which is the proof of the
stability criterion. This is Mathlib's `ContractingWith.tendsto_iterate_fixedPoint`. -/
theorem contraction_converges {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f) (x : α) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 (ContractingWith.fixedPoint f hf)) :=
  hf.tendsto_iterate_fixedPoint x
-- @endregion

/-! ### Predator and prey -/

-- @region mathematical_biology.lotka_volterra_conserved
-- @provenance independent
/-- **The Lotka–Volterra conserved quantity.** Along any positive solution of
`x' = αx − βxy` (prey), `y' = δxy − γy` (predators), the function
`V(x, y) = δx − γ log x + βy − α log y` has zero derivative, so it is constant and orbits lie
on its level curves (which are closed curves around the equilibrium `(γ/δ, α/β)`).
Proof: `V' = (δ − γ/x) x' + (β − α/y) y' = (δx − γ)(α − βy) + (βy − α)(δx − γ) = 0`. -/
theorem lotka_volterra_conserved {α β γ δ : ℝ} {x y : ℝ → ℝ} {t : ℝ} (hx : 0 < x t)
    (hy : 0 < y t) (hx' : HasDerivAt x (α * x t - β * x t * y t) t)
    (hy' : HasDerivAt y (δ * x t * y t - γ * y t) t) :
    HasDerivAt (fun s => δ * x s - γ * log (x s) + β * y s - α * log (y s)) 0 t := by
  have h1 := hx'.const_mul δ
  have h2 := (hx'.log hx.ne').const_mul γ
  have h3 := hy'.const_mul β
  have h4 := (hy'.log hy.ne').const_mul α
  have h := ((h1.sub h2).add h3).sub h4
  convert h using 1
  field_simp
  ring
-- @endregion

-- @region mathematical_biology.lotka_volterra_average
-- @provenance independent
/-- **Averages over a cycle equal the equilibrium.** If a positive solution is periodic with
period `T > 0` (`y(T) = y(0)`), then the average prey population over a period is
`(1/T) ∫₀ᵀ x = γ/δ`. Proof: `(log y)' = y'/y = δx − γ`; integrate over a period, where
`log y` returns to its initial value. (This is Volterra's explanation of D'Ancona's
observation that reduced fishing during the First World War raised the share of predators.) -/
theorem lotka_volterra_average {α β γ δ T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T) {x y : ℝ → ℝ}
    (hy : ∀ t, 0 < y t) (hx' : ∀ t, HasDerivAt x (α * x t - β * x t * y t) t)
    (hy' : ∀ t, HasDerivAt y (δ * x t * y t - γ * y t) t) (hper : y T = y 0) :
    (∫ t in (0 : ℝ)..T, x t) / T = γ / δ := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx' t).continuousAt
  -- `(log y)' = δ x − γ`.
  have hlog : ∀ t, HasDerivAt (fun s => log (y s)) (δ * x t - γ) t := by
    intro t
    have := (hy' t).log (hy t).ne'
    convert this using 1
    field_simp [(hy t).ne']
  have hint : IntervalIntegrable (fun t => δ * x t - γ) MeasureTheory.volume 0 T :=
    ((hxc.const_mul δ).sub continuous_const).intervalIntegrable 0 T
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hlog t) hint
  rw [hper, sub_self, intervalIntegral.integral_sub
    ((hxc.const_mul δ).intervalIntegrable 0 T) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero] at hftc
  field_simp
  linarith
-- @endregion

/-! ### Epidemics: the SIR model -/

-- @region mathematical_biology.sir_total_constant
-- @provenance independent
/-- **The SIR model conserves the population.** If `S' = −βSI/N`, `I' = βSI/N − γI` and
`R' = γI`, then `(S + I + R)' = 0`: everyone is always susceptible, infected or removed. -/
theorem sir_total_constant {β γ N : ℝ} {S I R : ℝ → ℝ} {t : ℝ}
    (hS : HasDerivAt S (-(β * S t * I t / N)) t)
    (hI : HasDerivAt I (β * S t * I t / N - γ * I t) t) (hR : HasDerivAt R (γ * I t) t) :
    HasDerivAt (fun s => S s + I s + R s) 0 t := by
  convert (hS.add hI).add hR using 1
  ring
-- @endregion

-- @region mathematical_biology.sir_threshold
-- @provenance independent
/-- **The epidemic threshold.** When infection is present (`I > 0`), the number infected is
increasing (`I' > 0`) exactly when `R₀ · S/N > 1`, where `R₀ = β/γ` (`β, γ, N > 0`). -/
theorem sir_threshold {β γ N S I : ℝ} (hγ : 0 < γ) (hN : 0 < N) (hI : 0 < I) :
    0 < β * S * I / N - γ * I ↔ 1 < β / γ * (S / N) := by
  have key : β * S * I / N - γ * I = γ * I * (β / γ * (S / N) - 1) := by
    field_simp
  rw [key]
  constructor
  · intro h
    have := (mul_pos_iff_of_pos_left (mul_pos hγ hI)).mp h
    linarith
  · intro h
    exact mul_pos (mul_pos hγ hI) (by linarith)
-- @endregion

-- @region mathematical_biology.sir_invariant
-- @provenance independent
/-- **The invariant behind the final-size relation.** Along a solution of the SIR model with
`S > 0`, the quantity `S + I − (N/R₀) log S` (with `R₀ = β/γ`, written `γN/β`) is constant.
Proof: its derivative is `S' + I' − (γN/β) S'/S = −γI + γI = 0`. Comparing its values at the
start (`I ≈ 0`, `S ≈ N`) and the end (`I = 0`) of an epidemic gives the final-size relation
`log(S∞/S₀) = R₀ (S∞ − S₀)/N`. -/
theorem sir_invariant {β γ N : ℝ} (hβ : β ≠ 0) (hN : N ≠ 0) {S I : ℝ → ℝ} {t : ℝ}
    (hpos : 0 < S t) (hS : HasDerivAt S (-(β * S t * I t / N)) t)
    (hI : HasDerivAt I (β * S t * I t / N - γ * I t) t) :
    HasDerivAt (fun s => S s + I s - γ * N / β * log (S s)) 0 t := by
  convert (hS.add hI).sub ((hS.log hpos.ne').const_mul (γ * N / β)) using 1
  field_simp
  ring
-- @endregion

-- @region mathematical_biology.herd_immunity
-- @provenance independent
/-- **Herd immunity threshold.** If a fraction `p` of the population is immune, an
introduced infection grows only if `R₀ (1 − p) > 1`. So it cannot grow exactly when
`p ≥ 1 − 1/R₀` (for `R₀ > 0`): about `92–94%` for measles (`R₀ ≈ 12–18`). -/
theorem herd_immunity {R₀ p : ℝ} (hR : 0 < R₀) : R₀ * (1 - p) ≤ 1 ↔ 1 - 1 / R₀ ≤ p := by
  constructor
  · intro h
    have : 1 - p ≤ 1 / R₀ := by
      rw [le_div_iff₀ hR]
      linarith
    linarith
  · intro h
    have : 1 - p ≤ 1 / R₀ := by linarith
    rw [le_div_iff₀ hR] at this
    linarith
-- @endregion

/-! ### Linear stability -/

-- @region mathematical_biology.trace_det_stable
-- @provenance independent
/-- **The trace–determinant test.** If a real `2 × 2` Jacobian has trace `τ < 0` and
determinant `Δ > 0`, every root `λ` of its characteristic polynomial `λ² − τλ + Δ` has
negative real part, so the equilibrium is locally asymptotically stable (by the linearisation
theorem). Proof: write `λ = a + bi`. The imaginary part of the equation is `b(2a − τ) = 0`;
if `b ≠ 0` then `a = τ/2 < 0`, and if `b = 0` then `a² − τa + Δ = 0` forces `a < 0`. -/
theorem trace_det_stable {τ Δ : ℝ} (hτ : τ < 0) (hΔ : 0 < Δ) {z : ℂ}
    (hz : z ^ 2 - τ * z + Δ = 0) : z.re < 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two] at hre him
  by_cases hb : z.im = 0
  · rw [hb] at hre
    by_contra hnn
    push Not at hnn
    nlinarith
  · have h2 : 2 * z.re - τ = 0 := by
      have : z.im * (2 * z.re - τ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hb
      · exact h
    linarith
-- @endregion

end Lumenary.MathematicalBiology
