/-
The Lumenary — formal mathematics
Optimisation: weak duality, optimality certificates and complementary slackness for linear
programs; local minima of convex functions are global; a least-norm problem solved by the
Lagrange condition; and the O(1/k) convergence rate of gradient descent.

Mathlib has convex sets and functions (`Convex`, `ConvexOn`), local and global minima
(`IsLocalMin`, `IsMinOn`), dot products of vectors (`⬝ᵥ`) with the order lemmas needed for linear
programming, and real inner product spaces. Proved here from more basic facts
(`@provenance independent`), mirroring the lesson: weak duality and its two corollaries, the
local-to-global principle for convex functions, the least-norm solution of `⟪a, x⟫ = b`, the
convergence-rate argument for gradient descent (from the descent inequality and the convexity
inequality, which are taken as hypotheses), and a check that these hypotheses hold for convex
quadratics. Applied from Mathlib (`@provenance library`): its own local-to-global theorem and
convexity of sublevel sets. Not formalised: strong duality and the simplex method, the KKT
theorem in general, and the derivation of the descent inequality from an `L`-Lipschitz gradient.
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Lumenary.Optimisation

open Matrix

/-! ### Linear programming duality -/

-- @region optimisation.weak_duality
-- @provenance independent
/-- **Weak duality.** For the primal problem *maximise `c · x` subject to `A x ≤ b`, `x ≥ 0`*
and its dual *minimise `b · y` subject to `Aᵀ y ≥ c`, `y ≥ 0`*, every feasible `x` and `y` satisfy
`c · x ≤ b · y`. The proof is one line of inequalities:
`c · x ≤ (Aᵀ y) · x = y · (A x) ≤ y · b`, using `x ≥ 0` and then `y ≥ 0`. -/
theorem weak_duality {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ)
    (c : n → ℝ) (x : n → ℝ) (y : m → ℝ) (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ b) (hy : 0 ≤ y)
    (hAy : c ≤ y ᵥ* A) : c ⬝ᵥ x ≤ b ⬝ᵥ y :=
  calc c ⬝ᵥ x ≤ (y ᵥ* A) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hAy hx
    _ = y ⬝ᵥ (A *ᵥ x) := (dotProduct_mulVec y A x).symm
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hAx hy
    _ = b ⬝ᵥ y := dotProduct_comm _ _
-- @endregion

-- @region optimisation.optimality_certificate
-- @provenance independent
/-- **A dual solution certifies optimality.** If a primal-feasible `x` and a dual-feasible `y`
have equal objective values, then `x` is optimal: no feasible `x'` does better, because
`c · x' ≤ b · y = c · x` by weak duality. -/
theorem optimality_certificate {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ) (hy : 0 ≤ y) (hAy : c ≤ y ᵥ* A)
    (heq : c ⬝ᵥ x = b ⬝ᵥ y) (x' : n → ℝ) (hx' : 0 ≤ x') (hAx' : A *ᵥ x' ≤ b) :
    c ⬝ᵥ x' ≤ c ⬝ᵥ x := by
  rw [heq]
  exact weak_duality A b c x' y hx' hAx' hy hAy
-- @endregion

-- @region optimisation.complementary_slackness
-- @provenance independent
/-- **Complementary slackness.** If feasible `x` and `y` have equal objective values, then both
inequalities in the weak-duality chain are equalities: `y · (b − A x) = 0` (a dual variable is
zero unless its constraint is tight) and `(Aᵀ y − c) · x = 0` (a primal variable is zero unless
its dual constraint is tight). -/
theorem complementary_slackness {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) (y : m → ℝ) (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ b)
    (hy : 0 ≤ y) (hAy : c ≤ y ᵥ* A) (heq : c ⬝ᵥ x = b ⬝ᵥ y) :
    y ⬝ᵥ (b - A *ᵥ x) = 0 ∧ (y ᵥ* A - c) ⬝ᵥ x = 0 := by
  have h1 : c ⬝ᵥ x ≤ (y ᵥ* A) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hAy hx
  have h2 : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hAx hy
  have h3 : y ⬝ᵥ (A *ᵥ x) = (y ᵥ* A) ⬝ᵥ x := dotProduct_mulVec y A x
  have h4 : b ⬝ᵥ y = y ⬝ᵥ b := dotProduct_comm _ _
  constructor
  · rw [dotProduct_sub]
    linarith
  · rw [sub_dotProduct]
    linarith
-- @endregion

/-! ### Convexity -/

-- @region optimisation.local_min_convex_global
-- @provenance independent
/-- **For a convex function, every local minimum is global.** Suppose `x` is a local minimum
and `y` is any point. For small `t > 0` the point `x + t (y − x) = (1 − t) x + t y` is near `x`,
so `f x ≤ f ((1 − t) x + t y) ≤ (1 − t) f x + t f y` by convexity; subtracting `(1 − t) f x`
and dividing by `t` gives `f x ≤ f y`. -/
theorem local_min_convex_global {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E} (hx : IsLocalMin f x) (y : E) :
    f x ≤ f y := by
  have hcont : Filter.Tendsto (fun t : ℝ => x + t • (y - x)) (nhds 0) (nhds x) := by
    have hc : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
    simpa using hc.tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually hx)
  set t : ℝ := min (ε / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (half_pos hε) (by norm_num)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hloc : f x ≤ f (x + t • (y - x)) := hball htε
  have hseg : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  have hconv : f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y :=
    hf.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith) ht0.le (by ring)
  rw [hseg] at hloc
  simp only [smul_eq_mul] at hconv
  nlinarith
-- @endregion

-- @region optimisation.local_min_convex_global_library
-- @provenance library
/-- The same principle from Mathlib: `IsMinOn.of_isLocalMin_of_convex_univ` (whose proof also
restricts `f` to the segment from `x` to `y`). -/
theorem local_min_convex_global_library {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E} (hx : IsLocalMin f x) :
    ∀ y, f x ≤ f y :=
  IsMinOn.of_isLocalMin_of_convex_univ hx hf
-- @endregion

-- @region optimisation.convex_sublevel
-- @provenance library
/-- **Sublevel sets of a convex function are convex** (Mathlib's `ConvexOn.convex_le`): the set
of points where `f ≤ r` is convex. In particular the set of minimisers of a convex function is
convex, so it is empty, a single point, or infinite. -/
theorem convex_sublevel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (r : ℝ) : Convex ℝ {x ∈ Set.univ | f x ≤ r} :=
  hf.convex_le r
-- @endregion

/-! ### A Lagrange-multiplier problem -/

-- @region optimisation.least_norm
-- @provenance independent
/-- **The least-norm solution of a linear equation.** Among all `x` with `⟪a, x⟫ = b`, the
smallest is `x* = (b / ‖a‖²) a` — the point the Lagrange condition `∇‖x‖² = λ ∇⟪a, x⟫`, i.e.
`2 x = λ a`, predicts. The proof is Pythagoras: `x − x*` is orthogonal to `x*`, so
`‖x‖² = ‖x − x*‖² + ‖x*‖² ≥ ‖x*‖²`. -/
theorem least_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : E) (b : ℝ)
    (ha : a ≠ 0) (x : E) (hx : inner ℝ a x = b) :
    ‖(b / ‖a‖ ^ 2) • a‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  set xs : E := (b / ‖a‖ ^ 2) • a with hxs
  have ha2 : ‖a‖ ^ 2 ≠ 0 := by positivity
  have horth : inner ℝ (x - xs) xs = 0 := by
    rw [hxs, inner_smul_right, inner_sub_left, inner_smul_left, real_inner_comm, hx,
      real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  have hpy : ‖x‖ ^ 2 = ‖x - xs‖ ^ 2 + ‖xs‖ ^ 2 := by
    have h := norm_add_sq_real (x - xs) xs
    rw [sub_add_cancel] at h
    rw [h, horth]
    ring
  rw [hpy]
  nlinarith [sq_nonneg ‖x - xs‖]
-- @endregion

/-! ### Gradient descent -/

-- @region optimisation.gradient_descent_rate
-- @provenance independent
/-- **Gradient descent converges at rate `O(1/k)`.** Let `x (k + 1) = x k − (1/L) g k`, where
`g k` is the gradient at `x k`, and assume the two standard inequalities for a convex function
with `L`-Lipschitz gradient: the *descent inequality* `f (x (k+1)) ≤ f (x k) − ‖g k‖² / (2L)` and
the *convexity inequality* `f (x k) − f x* ≤ ⟪g k, x k − x*⟫`. Then
`k · (f (x k) − f x*) ≤ (L/2) ‖x 0 − x*‖²`. Proof (the lesson's): each step satisfies
`f (x (k+1)) − f x* ≤ (L/2)(‖x k − x*‖² − ‖x (k+1) − x*‖²)`; these telescope, and the values
`f (x k)` decrease. -/
theorem gradient_descent_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : ℕ → E) (xs : E) (L : ℝ) (hL : 0 < L)
    (hstep : ∀ k, x (k + 1) = x k - (1 / L) • g k)
    (hdesc : ∀ k, f (x (k + 1)) ≤ f (x k) - 1 / (2 * L) * ‖g k‖ ^ 2)
    (hconv : ∀ k, f (x k) - f xs ≤ inner ℝ (g k) (x k - xs)) (n : ℕ) :
    (n : ℝ) * (f (x n) - f xs) ≤ L / 2 * ‖x 0 - xs‖ ^ 2 := by
  -- One step: the gap is bounded by the decrease of the squared distance to `x*`.
  have step : ∀ k, f (x (k + 1)) - f xs ≤
      L / 2 * (‖x k - xs‖ ^ 2 - ‖x (k + 1) - xs‖ ^ 2) := by
    intro k
    have hx1 : x (k + 1) - xs = (x k - xs) - (1 / L) • g k := by
      rw [hstep]
      abel
    have hn : ‖x (k + 1) - xs‖ ^ 2 = ‖x k - xs‖ ^ 2 - 2 * (1 / L) * inner ℝ (g k) (x k - xs)
        + (1 / L) ^ 2 * ‖g k‖ ^ 2 := by
      rw [hx1, norm_sub_sq_real, inner_smul_right, norm_smul, real_inner_comm, mul_pow,
        Real.norm_eq_abs, sq_abs]
      ring
    have h1 := hdesc k
    have h2 := hconv k
    have h3 : L / 2 * (‖x k - xs‖ ^ 2 - (‖x k - xs‖ ^ 2 - 2 * (1 / L) * inner ℝ (g k) (x k - xs)
        + (1 / L) ^ 2 * ‖g k‖ ^ 2)) = inner ℝ (g k) (x k - xs) - 1 / (2 * L) * ‖g k‖ ^ 2 := by
      field_simp
      ring
    rw [hn, h3]
    linarith
  -- Telescoping the steps.
  have tele : ∀ n : ℕ, (∑ k ∈ Finset.range n, (f (x (k + 1)) - f xs)) ≤
      L / 2 * (‖x 0 - xs‖ ^ 2 - ‖x n - xs‖ ^ 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := step n
      nlinarith
  -- The values decrease along the iteration.
  have mono : ∀ k n, k ≤ n → f (x n) ≤ f (x k) := by
    intro k n hkn
    induction hkn with
    | refl => exact le_refl _
    | @step m _ ih =>
      have h1 := hdesc m
      have h2 : 0 ≤ 1 / (2 * L) * ‖g m‖ ^ 2 := by positivity
      linarith
  have hsum : (n : ℝ) * (f (x n) - f xs) ≤ ∑ k ∈ Finset.range n, (f (x (k + 1)) - f xs) := by
    have hle : ∀ k ∈ Finset.range n, f (x n) - f xs ≤ f (x (k + 1)) - f xs := by
      intro k hk
      have := mono (k + 1) n (Finset.mem_range.mp hk)
      linarith
    have := Finset.card_nsmul_le_sum (Finset.range n) _ _ hle
    simpa using this
  have := tele n
  have : 0 ≤ L / 2 * ‖x n - xs‖ ^ 2 := by positivity
  linarith
-- @endregion

-- @region optimisation.gradient_descent_quadratic
-- @provenance independent
/-- **The hypotheses are not vacuous: convex quadratics satisfy them.** For `f(x) = (a/2) x²` on
`ℝ` with `0 < a ≤ L`, gradient descent with step `1/L` is `x (k+1) = (1 − a/L) x k`, and the
rate theorem gives `k · (a/2) x_k² ≤ (L/2) x_0²`. We check the descent inequality (it reduces to
`(1 − a/L)² ≤ 1 − a/L`) and the convexity inequality (`(a/2) x² ≤ a x²`), then apply
`gradient_descent_rate` with minimiser `0`. -/
theorem gradient_descent_quadratic (a L : ℝ) (ha : 0 < a) (haL : a ≤ L) (x : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = x k - (1 / L) * (a * x k)) (n : ℕ) :
    (n : ℝ) * (a / 2 * x n ^ 2) ≤ L / 2 * x 0 ^ 2 := by
  have hL : 0 < L := lt_of_lt_of_le ha haL
  have h1 : 0 ≤ 1 - a / L := by
    rw [sub_nonneg, div_le_one hL]
    exact haL
  have h2 : 1 - a / L ≤ 1 := by
    have : 0 ≤ a / L := by positivity
    linarith
  have key := gradient_descent_rate (fun y : ℝ => a / 2 * y ^ 2) x (fun k => a * x k) 0 L hL
    (fun k => by rw [hstep k]; simp [smul_eq_mul])
    (fun k => by
      show a / 2 * x (k + 1) ^ 2 ≤ a / 2 * x k ^ 2 - 1 / (2 * L) * ‖a * x k‖ ^ 2
      rw [hstep k, Real.norm_eq_abs, sq_abs]
      have e1 : x k - 1 / L * (a * x k) = (1 - a / L) * x k := by field_simp
      have e2 : a / 2 * x k ^ 2 - 1 / (2 * L) * (a * x k) ^ 2
          = a / 2 * x k ^ 2 * (1 - a / L) := by
        field_simp
      rw [e1, e2, show a / 2 * ((1 - a / L) * x k) ^ 2 = a / 2 * x k ^ 2 * (1 - a / L) ^ 2 by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith)
    (fun k => by
      simp only [Real.inner_apply, sub_zero]
      nlinarith [sq_nonneg (x k)]) n
  simpa using key
-- @endregion

end Lumenary.Optimisation
