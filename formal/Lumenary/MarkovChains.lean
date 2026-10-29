/-
The Lumenary — formal mathematics
Markov chains on finite state spaces: stochastic matrices and n-step transitions, detailed
balance, the two-state chain, gambler's ruin, Doeblin's contraction (the engine of the
convergence theorem), and the divergence of return probabilities of simple random walk in one
and two dimensions (the analytic half of Pólya's theorem).

A finite chain is described by its transition matrix `P : Matrix S S ℝ`; a distribution is a
row vector `μ : S → ℝ`, and one step of the chain sends it to `μ ᵥ* P`. Mathlib provides the
submonoid `Matrix.rowStochastic ℝ S` of row-stochastic matrices and its basic lemmas; general
Markov kernels on measurable spaces are `ProbabilityTheory.Kernel`. Proved here
(`@provenance independent`): products of stochastic matrices are stochastic, detailed balance
implies stationarity, the closed form of `Pⁿ` for two states and its convergence, the
gambler's-ruin formulas and the uniqueness of the fair solution, Doeblin's contraction and its
iteration, and the lower bounds on return probabilities that make random walk on `ℤ` and `ℤ²`
recurrent. Cited from Mathlib (`@provenance library`): powers of stochastic matrices are
stochastic, one step preserves probability vectors, and `4ⁿ ≤ (2n + 1)·C(2n, n)`.
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Central

open Finset Matrix Filter Topology

namespace Lumenary.MarkovChains

variable {S : Type*} [Fintype S]

/-! ### Stochastic matrices and n-step transitions -/

-- @region markov_chains.stochastic_mul
-- @provenance independent
/-- **The product of two transition matrices is a transition matrix.** If `P` and `Q` have
non-negative entries and rows summing to `1`, so does `PQ`: its entries `∑ₖ Pᵢₖ Qₖⱼ` are sums
of non-negative terms, and its row sums are
`∑ⱼ ∑ₖ Pᵢₖ Qₖⱼ = ∑ₖ Pᵢₖ ∑ⱼ Qₖⱼ = ∑ₖ Pᵢₖ = 1`. By Chapman–Kolmogorov, `PQ` is "first a step of
`P`, then a step of `Q`". -/
theorem stochastic_mul {P Q : Matrix S S ℝ}
    (hP : (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1)
    (hQ : (∀ i j, 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j = 1) :
    (∀ i j, 0 ≤ (P * Q) i j) ∧ ∀ i, ∑ j, (P * Q) i j = 1 := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [mul_apply]
    exact sum_nonneg fun k _ => mul_nonneg (hP.1 i k) (hQ.1 k j)
  · simp only [mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.2, mul_one]
    exact hP.2 i
-- @endregion

-- @region markov_chains.stochastic_pow
-- @provenance library
/-- **n-step transition matrices are stochastic.** Mathlib's `Matrix.rowStochastic ℝ S` is a
submonoid of the matrix monoid, so it contains every power `Pⁿ` of its elements
(`Submonoid.pow_mem`). The entry `(Pⁿ)ᵢⱼ` is the probability of being at `j` after `n` steps
from `i`. -/
theorem stochastic_pow [DecidableEq S] {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (n : ℕ) :
    P ^ n ∈ rowStochastic ℝ S :=
  Submonoid.pow_mem _ hP n
-- @endregion

-- @region markov_chains.distribution_step
-- @provenance library
/-- **One step of the chain maps distributions to distributions.** If `μ ≥ 0` sums to `1`, so
does `μ P`. These are Mathlib's `nonneg_vecMul_of_mem_rowStochastic` and
`vecMul_dotProduct_one_eq_one_rowStochastic` (`x ⬝ᵥ 1` is the sum of the entries of `x`). -/
theorem distribution_step [DecidableEq S] {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : μ ⬝ᵥ 1 = 1) :
    (∀ j, 0 ≤ (μ ᵥ* P) j) ∧ (μ ᵥ* P) ⬝ᵥ 1 = 1 :=
  ⟨nonneg_vecMul_of_mem_rowStochastic hP hμ0, vecMul_dotProduct_one_eq_one_rowStochastic hP hμ1⟩
-- @endregion

/-! ### Stationary distributions and detailed balance -/

-- @region markov_chains.detailed_balance_stationary
-- @provenance independent
/-- **Detailed balance implies stationarity.** If `πᵢ Pᵢⱼ = πⱼ Pⱼᵢ` for all states (the flow
of probability from `i` to `j` equals the flow back), and the rows of `P` sum to `1`, then
`π P = π`. Proof: `(πP)ⱼ = ∑ᵢ πᵢ Pᵢⱼ = ∑ᵢ πⱼ Pⱼᵢ = πⱼ ∑ᵢ Pⱼᵢ = πⱼ`. -/
theorem detailed_balance_stationary {P : Matrix S S ℝ} (hrow : ∀ i, ∑ j, P i j = 1)
    {π : S → ℝ} (hdb : ∀ i j, π i * P i j = π j * P j i) : π ᵥ* P = π := by
  funext j
  simp only [vecMul, dotProduct]
  simp_rw [hdb _ j]
  rw [← mul_sum, hrow j, mul_one]
-- @endregion

/-! ### The two-state chain -/

-- @region markov_chains.two_state
-- @provenance definition
/-- The general **two-state chain**: from state `0` jump with probability `a`, from state `1`
jump back with probability `b`. -/
def twoState (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - a, a; b, 1 - b]
-- @endregion

-- @region markov_chains.two_state_stationary
-- @provenance independent
/-- The two-state chain (with `a + b ≠ 0`) has stationary distribution
`π = (b/(a + b), a/(a + b))`: a direct computation of `π P`. -/
theorem two_state_stationary {a b : ℝ} (hab : a + b ≠ 0) :
    ![b / (a + b), a / (a + b)] ᵥ* twoState a b = ![b / (a + b), a / (a + b)] := by
  funext j
  fin_cases j <;>
  · simp [twoState, vecMul, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
-- @endregion

-- @region markov_chains.two_state_pow
-- @provenance independent
/-- **The n-step matrix of the two-state chain.** With `λ = 1 − a − b` (the second eigenvalue),
`(a + b) Pⁿ = [[b + a λⁿ, a − a λⁿ], [b − b λⁿ, a + b λⁿ]]`. Each row is the stationary
distribution plus a correction that decays like `λⁿ`. Proof: induction on `n`, using
`Pⁿ⁺¹ = Pⁿ P`. -/
theorem two_state_pow (a b : ℝ) (n : ℕ) :
    (a + b) • twoState a b ^ n =
      !![b + a * (1 - a - b) ^ n, a - a * (1 - a - b) ^ n;
         b - b * (1 - a - b) ^ n, a + b * (1 - a - b) ^ n] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  | succ n ih =>
    rw [pow_succ, ← smul_mul_assoc, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
    · simp [twoState, mul_apply, Fin.sum_univ_two]
      ring
-- @endregion

-- @region markov_chains.two_state_converges
-- @provenance independent
/-- **Convergence to equilibrium for two states.** If `|1 − a − b| < 1` (true whenever
`0 < a, b` and `a + b < 2`, i.e. the chain is irreducible and aperiodic), then the probability
of being in state `0` after `n` steps from state `0` tends to `π₀ = b/(a + b)`. Proof: by
`two_state_pow`, `(Pⁿ)₀₀ = (b + a λⁿ)/(a + b)` and `λⁿ → 0`. -/
theorem two_state_converges {a b : ℝ} (hab : a + b ≠ 0) (hlam : |1 - a - b| < 1) :
    Tendsto (fun n : ℕ => (twoState a b ^ n) 0 0) atTop (𝓝 (b / (a + b))) := by
  have hentry : ∀ n : ℕ, (twoState a b ^ n) 0 0 = (b + a * (1 - a - b) ^ n) / (a + b) := by
    intro n
    have h := congrFun (congrFun (two_state_pow a b n) 0) 0
    have h' : (a + b) * (twoState a b ^ n) 0 0 = b + a * (1 - a - b) ^ n := by
      simpa [Matrix.smul_apply] using h
    rw [eq_div_iff hab, mul_comm]
    exact h'
  simp_rw [hentry]
  have hpow : Tendsto (fun n : ℕ => (1 - a - b) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hlam
  have := ((hpow.const_mul a).const_add b).div_const (a + b)
  simpa using this
-- @endregion

/-! ### Gambler's ruin: first-step analysis -/

-- @region markov_chains.gambler_fair_solves
-- @provenance independent
/-- **Fair gambler's ruin.** Starting with `i` coins and betting one coin on fair coin flips
until reaching `0` or `N`, the probability `h(i)` of reaching `N` satisfies the first-step
equations `h(i) = ½ h(i − 1) + ½ h(i + 1)` with `h(0) = 0`, `h(N) = 1`. The function
`h(i) = i/N` is a solution. -/
theorem gambler_fair_solves {N : ℕ} (hN : 0 < N) (i : ℕ) :
    ((i + 1 : ℕ) : ℝ) / N = 1 / 2 * ((i : ℝ) / N) + 1 / 2 * (((i + 2 : ℕ) : ℝ) / N) := by
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  push_cast
  field_simp
  ring
-- @endregion

-- @region markov_chains.gambler_fair_unique
-- @provenance independent
/-- **…and it is the only solution.** If `h(0) = 0`, `h(N) = 1` and
`h(i + 1) = 2h(i) − h(i − 1)` for `0 < i < N` (the first-step equation rearranged), then
`h(i) = i/N` for all `i ≤ N`. Proof: the increments `h(i + 1) − h(i)` are all equal, so
`h(i) = i·h(1)` by induction, and `h(N) = 1` forces `h(1) = 1/N`. -/
theorem gambler_fair_unique {N : ℕ} (hN : 0 < N) (h : ℕ → ℝ) (h0 : h 0 = 0) (hNv : h N = 1)
    (hrec : ∀ i, 0 < i → i < N → h (i + 1) = 2 * h i - h (i - 1)) :
    ∀ i ≤ N, h i = i / N := by
  -- First, `h i = i * h 1` for `i ≤ N`, proved together with the next value.
  have key : ∀ i, i + 1 ≤ N → h i = i * h 1 ∧ h (i + 1) = (i + 1) * h 1 := by
    intro i
    induction i with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨by push_cast; exact h2, ?_⟩
      have := hrec (k + 1) (by omega) (by omega)
      rw [this, show k + 1 - 1 = k by omega, h1, h2]
      push_cast
      ring
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hN1 : h 1 = 1 / N := by
    obtain ⟨_, hlast⟩ := key (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega, hNv] at hlast
    have : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this] at hlast
    field_simp
    linarith
  intro i hi
  rcases Nat.lt_or_ge i N with hlt | hge
  · rw [(key i (by omega)).1, hN1]
    ring
  · rw [show i = N by omega, hNv]
    field_simp
-- @endregion

-- @region markov_chains.gambler_biased_solves
-- @provenance independent
/-- **Biased gambler's ruin.** If each bet is won with probability `p` and lost with
probability `q = 1 − p`, with `r = q/p ≠ 1`, the probability of reaching `N` from `i` is
`h(i) = (1 − rⁱ)/(1 − rᴺ)`: it satisfies `h(i + 1) = p h(i + 2) + q h(i)` (first-step
analysis from `i + 1`), together with `h(0) = 0` and `h(N) = 1`. -/
theorem gambler_biased_solves {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : (1 - p) / p ≠ 1) {N : ℕ}
    (hN : 0 < N) (i : ℕ) :
    let r := (1 - p) / p
    let h : ℕ → ℝ := fun k => (1 - r ^ k) / (1 - r ^ N)
    h 0 = 0 ∧ h N = 1 ∧ h (i + 1) = p * h (i + 2) + (1 - p) * h i := by
  intro r h
  have hrpos : 0 ≤ r := div_nonneg (by linarith) hp0.le
  have hrN : 1 - r ^ N ≠ 0 := by
    intro h0
    have hr1 : r ^ N = 1 := by linarith
    exact hr ((pow_eq_one_iff_of_nonneg hrpos hN.ne').mp hr1)
  refine ⟨by simp [h], by simp [h, div_self hrN], ?_⟩
  have hq : 1 - p = r * p := by
    simp only [r]
    field_simp
  have key : p * (1 - r ^ (i + 2)) + (1 - p) * (1 - r ^ i) = 1 - r ^ (i + 1) := by
    linear_combination (r ^ i * (r - 1)) * hq
  simp only [h]
  rw [show p * ((1 - r ^ (i + 2)) / (1 - r ^ N)) + (1 - p) * ((1 - r ^ i) / (1 - r ^ N)) =
      (p * (1 - r ^ (i + 2)) + (1 - p) * (1 - r ^ i)) / (1 - r ^ N) by ring, key]
-- @endregion

-- @region markov_chains.duration_fair_solves
-- @provenance independent
/-- **Expected duration of the fair game.** The expected number of bets `m(i)` until the
fair game ends satisfies `m(i) = 1 + ½ m(i − 1) + ½ m(i + 1)` with `m(0) = m(N) = 0`, and
`m(i) = i (N − i)` is a solution (shown here at `i + 1` for all `i`). Starting with `10`
coins and stopping at `0` or `20` takes `100` bets on average. -/
theorem duration_fair_solves (N i : ℝ) :
    (i + 1) * (N - (i + 1)) = 1 + 1 / 2 * (i * (N - i)) + 1 / 2 * ((i + 2) * (N - (i + 2))) := by
  ring
-- @endregion

/-! ### Doeblin's contraction: why chains forget their start -/

-- @region markov_chains.zero_sum_vec_mul
-- @provenance independent
/-- A step of a stochastic matrix preserves zero-sum vectors (such as the difference `μ − ν`
of two distributions): `∑ⱼ (xP)ⱼ = ∑ᵢ xᵢ ∑ⱼ Pᵢⱼ = ∑ᵢ xᵢ`. -/
theorem zero_sum_vecMul {P : Matrix S S ℝ} (hrow : ∀ i, ∑ j, P i j = 1) {x : S → ℝ}
    (hx : ∑ i, x i = 0) : ∑ j, (x ᵥ* P) j = 0 := by
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  simp only [← mul_sum, hrow, mul_one]
  exact hx
-- @endregion

-- @region markov_chains.doeblin_contraction
-- @provenance independent
/-- **Doeblin's contraction.** Let `P` be stochastic with every entry at least `δ`, on a state
space with `k` states. Then for every zero-sum vector `x`, `‖xP‖₁ ≤ (1 − kδ)‖x‖₁`.
Proof: since `∑ᵢ xᵢ = 0`, `(xP)ⱼ = ∑ᵢ xᵢ (Pᵢⱼ − δ)` with `Pᵢⱼ − δ ≥ 0`, so
`∑ⱼ |(xP)ⱼ| ≤ ∑ᵢ |xᵢ| ∑ⱼ (Pᵢⱼ − δ) = (1 − kδ) ∑ᵢ |xᵢ|`. Applied to `x = μ − ν`, two
distributions are pulled together by a factor `1 − kδ < 1` at every step. -/
theorem doeblin_contraction {P : Matrix S S ℝ} (hrow : ∀ i, ∑ j, P i j = 1) {δ : ℝ}
    (hδ : ∀ i j, δ ≤ P i j) {x : S → ℝ} (hx : ∑ i, x i = 0) :
    ∑ j, |(x ᵥ* P) j| ≤ (1 - Fintype.card S * δ) * ∑ i, |x i| := by
  have hshift : ∀ j, (x ᵥ* P) j = ∑ i, x i * (P i j - δ) := by
    intro j
    simp only [vecMul, dotProduct, mul_sub, sum_sub_distrib, ← sum_mul, hx, zero_mul, sub_zero]
  calc ∑ j, |(x ᵥ* P) j| = ∑ j, |∑ i, x i * (P i j - δ)| := by simp_rw [hshift]
    _ ≤ ∑ j, ∑ i, |x i| * (P i j - δ) := by
        apply sum_le_sum
        intro j _
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hδ i j))]
    _ = ∑ i, |x i| * ∑ j, (P i j - δ) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = (1 - Fintype.card S * δ) * ∑ i, |x i| := by
        simp only [sum_sub_distrib, hrow, sum_const, card_univ, nsmul_eq_mul]
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by ring
-- @endregion

-- @region markov_chains.doeblin_iterate
-- @provenance independent
/-- **Geometric convergence.** Iterating Doeblin's contraction (zero-sum vectors stay
zero-sum): `‖x Pⁿ‖₁ ≤ (1 − kδ)ⁿ ‖x‖₁`. With `x = μ − π` for a stationary `π`, the distribution
at time `n` approaches `π` exponentially fast. For a general irreducible aperiodic chain, apply
this to a power `Pᴺ` whose entries are all positive. -/
theorem doeblin_iterate [DecidableEq S] {P : Matrix S S ℝ} (hrow : ∀ i, ∑ j, P i j = 1) {δ : ℝ}
    (hδ : ∀ i j, δ ≤ P i j) (hkδ : Fintype.card S * δ ≤ 1) {x : S → ℝ} (hx : ∑ i, x i = 0)
    (n : ℕ) : ∑ j, |(x ᵥ* P ^ n) j| ≤ (1 - Fintype.card S * δ) ^ n * ∑ i, |x i| := by
  have hz : ∀ m : ℕ, ∑ i, (x ᵥ* P ^ m) i = 0 := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ihm =>
      rw [pow_succ, ← vecMul_vecMul]
      exact zero_sum_vecMul hrow ihm
  induction n with
  | zero => simp
  | succ n ih =>
    have hzero := hz n
    rw [pow_succ, ← vecMul_vecMul]
    calc ∑ j, |((x ᵥ* P ^ n) ᵥ* P) j| ≤ (1 - Fintype.card S * δ) * ∑ i, |(x ᵥ* P ^ n) i| :=
          doeblin_contraction hrow hδ hzero
      _ ≤ (1 - Fintype.card S * δ) * ((1 - Fintype.card S * δ) ^ n * ∑ i, |x i|) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - Fintype.card S * δ) ^ (n + 1) * ∑ i, |x i| := by ring
-- @endregion

/-! ### Random walks: returns to the origin -/

-- @region markov_chains.central_binom_lower
-- @provenance library
/-- `4ⁿ ≤ (2n + 1) C(2n, n)`: the middle binomial coefficient is the largest of the `2n + 1`
coefficients `C(2n, k)`, which add up to `4ⁿ`. This is Mathlib's
`Nat.four_pow_le_two_mul_add_one_mul_centralBinom`. Since simple random walk on `ℤ` is back at
`0` at time `2n` with probability `C(2n, n)/4ⁿ`, that probability is at least `1/(2n + 1)`. -/
theorem central_binom_lower (n : ℕ) : 4 ^ n ≤ (2 * n + 1) * n.centralBinom :=
  Nat.four_pow_le_two_mul_add_one_mul_centralBinom n
-- @endregion

-- @region markov_chains.walk_1d_returns_diverge
-- @provenance independent
/-- **Simple random walk on `ℤ` is recurrent.** The expected number of returns to `0` is
`∑ₙ P(S₂ₙ = 0) = ∑ₙ C(2n, n)/4ⁿ`, and this series diverges: each term is at least
`1/(2n + 1) ≥ 1/(2(n + 1))`, and the harmonic series diverges. By the recurrence criterion
(infinitely many expected returns ⇔ recurrent), the walk returns with probability `1`. -/
theorem walk_1d_returns_diverge :
    ¬ Summable (fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n) := by
  intro hsum
  -- Compare with `1/(2(n + 1))`.
  have hle : ∀ n : ℕ, 1 / (2 * ((n : ℝ) + 1)) ≤ (n.centralBinom : ℝ) / 4 ^ n := by
    intro n
    have h := central_binom_lower n
    have h' : (4 : ℝ) ^ n ≤ (2 * n + 1) * n.centralBinom := by exact_mod_cast h
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n,
      (Nat.cast_nonneg n.centralBinom : (0 : ℝ) ≤ _)]
  have h2 : Summable (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hsum
  have h3 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    have := h2.mul_left 2
    refine this.congr fun n => ?_
    push_cast
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h3)
-- @endregion

-- @region markov_chains.central_binom_sq_lower
-- @provenance independent
/-- `(C(2n, n)/4ⁿ)² ≥ 1/(4n)` for `n ≥ 1`. Proof by induction: `aₙ = C(2n, n)/4ⁿ` satisfies
`aₙ₊₁ = aₙ (2n + 1)/(2n + 2)` (Mathlib's `Nat.succ_mul_centralBinom_succ`), and
`(2n + 1)² ≥ 4n(n + 1)`. This sharper bound is what dimension two needs. -/
theorem central_binom_sq_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ 4 * (n : ℝ) * ((n.centralBinom : ℝ) / 4 ^ n) ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
    set a := (k.centralBinom : ℝ) / 4 ^ k
    have hrec : ((k + 1).centralBinom : ℝ) / 4 ^ (k + 1) = a * (2 * k + 1) / (2 * k + 2) := by
      have h := Nat.succ_mul_centralBinom_succ k
      have h' : ((k : ℝ) + 1) * (k + 1).centralBinom = 2 * (2 * k + 1) * k.centralBinom := by
        exact_mod_cast h
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      simp only [a]
      rw [pow_succ]
      field_simp
      have : ((k + 1).centralBinom : ℝ) = 2 * (2 * k + 1) * k.centralBinom / (k + 1) := by
        field_simp
        linarith
      rw [this]
      field_simp
      ring
    rw [hrec]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsq : 4 * (k : ℝ) * (k + 1) ≤ (2 * k + 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < 2 * k + 2 := by positivity
    push_cast
    have hsimp : 4 * ((k : ℝ) + 1) * (a * (2 * k + 1) / (2 * k + 2)) ^ 2 =
        a ^ 2 * (2 * k + 1) ^ 2 / (k + 1) := by
      field_simp
      ring
    rw [hsimp, le_div_iff₀ (by positivity)]
    have hchain : (2 * (k : ℝ) + 1) ^ 2 ≤ (2 * k + 1) ^ 2 * (4 * k * a ^ 2) := by
      nlinarith [sq_nonneg (2 * (k : ℝ) + 1)]
    nlinarith [hchain, hsq, hkR]
-- @endregion

-- @region markov_chains.walk_2d_returns_diverge
-- @provenance independent
/-- **Simple random walk on `ℤ²` is recurrent.** Rotating the lattice by 45° turns the planar
walk into two independent walks on `ℤ` (the coordinates `x + y` and `x − y`), so
`P(S₂ₙ = 0) = (C(2n, n)/4ⁿ)²`. These probabilities are not summable: from `n = 1` on they are
at least `1/(4n)`. (The rotation argument itself is in the lesson, not formalised.) -/
theorem walk_2d_returns_diverge :
    ¬ Summable (fun n : ℕ => ((n.centralBinom : ℝ) / 4 ^ n) ^ 2) := by
  intro hsum
  have hshift := (summable_nat_add_iff 1).mpr hsum
  have hle : ∀ n : ℕ, 1 / 4 * (1 / ((n + 1 : ℕ) : ℝ)) ≤
      (((n + 1).centralBinom : ℝ) / 4 ^ (n + 1)) ^ 2 := by
    intro n
    have h := central_binom_sq_lower (n + 1) (by omega)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [show 1 / 4 * (1 / ((n + 1 : ℕ) : ℝ)) = 1 / (4 * ((n + 1 : ℕ) : ℝ)) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h2 : Summable (fun n : ℕ => 1 / 4 * (1 / ((n + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hshift
  have h3 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (1 / 4 : ℝ) ≠ 0)).mp h2
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h3)
-- @endregion

end Lumenary.MarkovChains
