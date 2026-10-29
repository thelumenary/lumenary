/-
The Lumenary — formal mathematics
Random structures: the analytic heart of Pólya's recurrence theorem in dimensions 1 and 2, the
45° rotation that turns the planar walk into two independent walks, the Nash-Williams bound
behind recurrence of ℤ², Peierls' counting argument for percolation, and the absence of a giant
component in subcritical random graphs.

What is proved here and what Mathlib provides. Mathlib has central binomial coefficients, p-series
and geometric series, but no random walks on lattices, percolation or random graphs, so the
probabilistic modelling is done in the lesson and the *formal* content is the exact mathematics
the proofs reduce to. The *independent* declarations prove the two-sided bound
`16ⁿ / (4n) ≤ C(2n, n)² ≤ 16ⁿ / (2n + 1)` by induction; deduce that the return probabilities
`p₂ₙ = C(2n, n)/4ⁿ` of the walk on ℤ (and their squares, the return probabilities on ℤ²) have
divergent sums, while `p₂ₙ → 0`; prove that the rotation `(x, y) ↦ (x + y, x − y)` maps the four
unit steps of ℤ² onto the four diagonal steps `(±1, ±1)` and that a planar path is closed iff both
rotated coordinates return to zero; show that the Nash-Williams series `∑ 1/(8k + 4)` diverges;
prove Peierls' estimate `cₙ pⁿ → 0` for `p < 1/3` when `cₙ ≤ 4 · 3ⁿ`; and show that for `c ≤ 1`
the survival equation `β = 1 − e^{−cβ}` has only the solution `β = 0`. The *library* declarations
cite Mathlib's bound `4ⁿ ≤ (2n + 1) C(2n, n)`, the convergence of `∑ 1/n²` and of `∑ n rⁿ`. Not
formalised: probability spaces of walks, the strong Markov property and the equivalence
"recurrent ⟺ expected number of returns infinite", electrical networks, the counting bound for
self-avoiding paths, Kesten's theorem, random graphs, Brownian motion and SLE.
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Lumenary.RandomGeometry

open Nat Filter Topology

/-! ### Return probabilities of simple random walk: exact bounds -/

-- @region random_geometry.four_pow_le_central_binom
-- @provenance library
/-- `4ⁿ ≤ (2n + 1) · C(2n, n)`: the central binomial coefficient is the largest of the `2n + 1`
coefficients `C(2n, k)`, which sum to `4ⁿ`. This applies Mathlib's
`Nat.four_pow_le_two_mul_add_one_mul_centralBinom`. -/
theorem four_pow_le_central_binom (n : ℕ) : 4 ^ n ≤ (2 * n + 1) * centralBinom n :=
  Nat.four_pow_le_two_mul_add_one_mul_centralBinom n
-- @endregion

-- @region random_geometry.central_binom_sq_lower
-- @provenance independent
/-- **Lower bound** `16ⁿ ≤ 4n · C(2n, n)²` for `n ≥ 1`, i.e. `C(2n, n)/4ⁿ ≥ 1/(2√n)`. Induction
using `(n + 1) C(2n+2, n+1) = 2(2n + 1) C(2n, n)` and `4n(n + 1) ≤ (2n + 1)²`. -/
theorem central_binom_sq_lower : ∀ n : ℕ, 1 ≤ n → 16 ^ n ≤ 4 * n * (centralBinom n) ^ 2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [centralBinom]
    · have ih' := ih h
      have key := Nat.succ_mul_centralBinom_succ m
      -- multiply the target by (m + 1)², then use the recursion and the induction hypothesis
      have h2 : 16 ^ (m + 1) * (m + 1) ^ 2 ≤
          4 * (m + 1) * (centralBinom (m + 1)) ^ 2 * (m + 1) ^ 2 := by
        have e : 4 * (m + 1) * (centralBinom (m + 1)) ^ 2 * (m + 1) ^ 2 =
            4 * (m + 1) * ((m + 1) * centralBinom (m + 1)) ^ 2 := by ring
        rw [e, key]
        have : 16 ^ (m + 1) * (m + 1) ^ 2 = 16 * 16 ^ m * (m + 1) ^ 2 := by ring
        rw [this]
        calc 16 * 16 ^ m * (m + 1) ^ 2 ≤ 16 * (4 * m * centralBinom m ^ 2) * (m + 1) ^ 2 := by
              gcongr
          _ ≤ 4 * (m + 1) * (2 * (2 * m + 1) * centralBinom m) ^ 2 := by
              have : 4 * m * (m + 1) ≤ (2 * m + 1) ^ 2 := by nlinarith
              nlinarith [Nat.zero_le (centralBinom m ^ 2), this]
      exact Nat.le_of_mul_le_mul_right h2 (by positivity)
-- @endregion

-- @region random_geometry.central_binom_sq_upper
-- @provenance independent
/-- **Upper bound** `(2n + 1) · C(2n, n)² ≤ 16ⁿ`, i.e. `C(2n, n)/4ⁿ ≤ 1/√(2n + 1)`. Induction using
the same recursion and `(2n + 1)(2n + 3) ≤ 4(n + 1)²`. -/
theorem central_binom_sq_upper : ∀ n : ℕ, (2 * n + 1) * (centralBinom n) ^ 2 ≤ 16 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have key := Nat.succ_mul_centralBinom_succ m
    have h2 : (2 * (m + 1) + 1) * (centralBinom (m + 1)) ^ 2 * (m + 1) ^ 2 ≤
        16 ^ (m + 1) * (m + 1) ^ 2 := by
      have e : (2 * (m + 1) + 1) * (centralBinom (m + 1)) ^ 2 * (m + 1) ^ 2 =
          (2 * m + 3) * ((m + 1) * centralBinom (m + 1)) ^ 2 := by ring
      rw [e, key]
      have e2 : (2 * m + 3) * (2 * (2 * m + 1) * centralBinom m) ^ 2 =
          4 * (2 * m + 3) * (2 * m + 1) * ((2 * m + 1) * centralBinom m ^ 2) := by ring
      rw [e2]
      calc 4 * (2 * m + 3) * (2 * m + 1) * ((2 * m + 1) * centralBinom m ^ 2)
          ≤ 4 * (2 * m + 3) * (2 * m + 1) * 16 ^ m := by gcongr
        _ ≤ 16 ^ (m + 1) * (m + 1) ^ 2 := by
          have : (2 * m + 3) * (2 * m + 1) ≤ 4 * (m + 1) ^ 2 := by nlinarith
          have h16 : 16 ^ (m + 1) = 16 * 16 ^ m := by ring
          rw [h16]
          nlinarith [Nat.zero_le (16 ^ m)]
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
-- @endregion

-- @region random_geometry.not_summable_one_div_two_mul_add_one
-- @provenance independent
/-- `∑ 1/(2n + 1)` diverges: it dominates half the harmonic series, `1/(n + 1) ≤ 2/(2n + 1)`, and
Mathlib knows that `∑ 1/n` diverges (`Real.not_summable_one_div_natCast`). -/
theorem not_summable_one_div_two_mul_add_one :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (2 * n + 1)) := by
  intro h
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left 2)
    push_cast
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h2)
-- @endregion

-- @region random_geometry.return_1d_not_summable
-- @provenance independent
/-- **Pólya in dimension 1, analytically.** The probability that simple random walk on ℤ is at
the origin at time `2n` is `p₂ₙ = C(2n, n)/4ⁿ`, and `∑ p₂ₙ` (the expected number of returns)
diverges, because `p₂ₙ ≥ 1/(2n + 1)`. By the criterion proved in the lesson (Theorem 1), the
walk is recurrent. -/
theorem return_1d_not_summable :
    ¬ Summable (fun n : ℕ => (centralBinom n : ℝ) / 4 ^ n) := by
  intro h
  apply not_summable_one_div_two_mul_add_one
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  have hle : (4 : ℝ) ^ n ≤ (2 * n + 1) * centralBinom n := by
    exact_mod_cast four_pow_le_central_binom n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith
-- @endregion

-- @region random_geometry.return_2d_not_summable
-- @provenance independent
/-- **Pólya in dimension 2, analytically.** On ℤ² the return probability at time `2n` is
`(C(2n, n)/4ⁿ)²` (by the rotation trick below), and `∑ (C(2n, n)/4ⁿ)²` diverges, because by
`central_binom_sq_lower` each term is at least `1/(4n)`. -/
theorem return_2d_not_summable :
    ¬ Summable (fun n : ℕ => ((centralBinom n : ℝ) / 4 ^ n) ^ 2) := by
  intro h
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    have h' := (summable_nat_add_iff 1).mpr h
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h'.mul_left 4)
    have hlow : (16 : ℝ) ^ (n + 1) ≤
        4 * ((n + 1 : ℕ) : ℝ) * (centralBinom (n + 1) : ℝ) ^ 2 := by
      exact_mod_cast central_binom_sq_lower (n + 1) (by omega)
    have h16 : ((4 : ℝ) ^ (n + 1)) ^ 2 = 16 ^ (n + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    simp only [div_pow, h16]
    rw [div_le_iff₀ hpos,
      show 4 * ((centralBinom (n + 1) : ℝ) ^ 2 / 16 ^ (n + 1)) * ((n + 1 : ℕ) : ℝ)
        = 4 * ((n + 1 : ℕ) : ℝ) * (centralBinom (n + 1) : ℝ) ^ 2 / 16 ^ (n + 1) by ring,
      le_div_iff₀ (by positivity)]
    linarith
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h1)
-- @endregion

-- @region random_geometry.return_prob_tendsto_zero
-- @provenance independent
/-- Yet `p₂ₙ = C(2n, n)/4ⁿ → 0`: by `central_binom_sq_upper`, `p₂ₙ² ≤ 1/(2n + 1)`. The walk on ℤ
returns with probability one, but the chance of being home at any given late time is small — one
reason the expected return time is infinite. -/
theorem return_prob_tendsto_zero :
    Tendsto (fun n : ℕ => (centralBinom n : ℝ) / 4 ^ n) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => ((centralBinom n : ℝ) / 4 ^ n) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : (2 * (n : ℝ) + 1) * (centralBinom n : ℝ) ^ 2 ≤ 16 ^ n := by
      exact_mod_cast central_binom_sq_upper n
    have h16 : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, h16, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (centralBinom n : ℝ)]
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  refine h.congr (fun n => ?_)
  exact Real.sqrt_sq (by positivity)
-- @endregion

/-! ### The rotation trick: the planar walk is two independent walks -/

-- @region random_geometry.rot
-- @provenance definition
/-- The 45° rotation (and scaling by `√2`) `(x, y) ↦ (x + y, x − y)` of ℤ², as an additive map. -/
def rot : ℤ × ℤ →+ ℤ × ℤ where
  toFun v := (v.1 + v.2, v.1 - v.2)
  map_zero' := by simp
  map_add' u v := by ext <;> simp <;> ring
-- @endregion

-- @region random_geometry.rot_injective
-- @provenance independent
/-- The rotation is injective: from `x + y` and `x − y` one recovers `x` and `y`. -/
theorem rot_injective : Function.Injective rot := by
  intro u v h
  simp only [rot, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at h
  ext <;> omega
-- @endregion

-- @region random_geometry.unit_steps
-- @provenance definition
/-- The four unit steps of simple random walk on ℤ². -/
def unitSteps : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}
-- @endregion

-- @region random_geometry.diag_steps
-- @provenance definition
/-- The four diagonal steps `(±1, ±1)`: a pair of independent `±1` steps. -/
def diagSteps : Finset (ℤ × ℤ) := {(1, 1), (-1, -1), (1, -1), (-1, 1)}
-- @endregion

-- @region random_geometry.rot_unit_steps
-- @provenance independent
/-- The rotation maps the four unit steps bijectively onto the four diagonal steps (checked by
`decide`; injectivity is `rot_injective`). So a uniformly random unit step becomes a pair of
*independent* uniform `±1` steps, and simple random walk on ℤ² becomes two independent simple
random walks on ℤ. -/
theorem rot_unit_steps : unitSteps.image rot = diagSteps := by
  decide
-- @endregion

-- @region random_geometry.closed_iff_rot
-- @provenance independent
/-- A planar path (a list of steps) returns to the origin iff **both** rotated coordinate walks do.
With `rot_unit_steps` this gives `P(S₂ₙ = 0 in ℤ²) = P(S₂ₙ = 0 in ℤ)² = (C(2n, n)/4ⁿ)²`. -/
theorem closed_iff_rot (L : List (ℤ × ℤ)) :
    L.sum = 0 ↔ ((L.map rot).map Prod.fst).sum = 0 ∧ ((L.map rot).map Prod.snd).sum = 0 := by
  have e1 : ((L.map rot).map Prod.fst).sum = (rot L.sum).1 := by
    rw [map_list_sum rot L]
    exact (map_list_sum (AddMonoidHom.fst ℤ ℤ) _).symm
  have e2 : ((L.map rot).map Prod.snd).sum = (rot L.sum).2 := by
    rw [map_list_sum rot L]
    exact (map_list_sum (AddMonoidHom.snd ℤ ℤ) _).symm
  rw [e1, e2]
  constructor
  · intro h
    simp [h]
  · rintro ⟨h1, h2⟩
    apply rot_injective
    rw [map_zero]
    exact Prod.ext h1 h2
-- @endregion

/-! ### Electrical networks -/

-- @region random_geometry.nash_williams_diverges
-- @provenance independent
/-- **The Nash-Williams series for ℤ² diverges.** The edges joining the boundary of the box
`[-k, k]²` to the boundary of `[-(k+1), k+1]²` form a cutset of `8k + 4` unit resistors; the
Nash-Williams inequality gives `R_eff(0 ↔ ∞) ≥ ∑ₖ 1/(8k + 4) = ∞`, so the walk on ℤ² is
recurrent. Proof: compare with the harmonic series. -/
theorem nash_williams_diverges : ¬ Summable (fun k : ℕ => (1 : ℝ) / (8 * k + 4)) := by
  intro h
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left 8)
    push_cast
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h2)
-- @endregion

-- @region random_geometry.summable_inv_sq
-- @provenance library
/-- `∑ 1/n²` converges. In ℤ³ a unit flow from the origin spread evenly over spheres has energy
comparable to `∑ₖ k² · (1/k²)² = ∑ 1/k²`, finite, so by T. Lyons' criterion the walk on ℤ³ is
transient. This applies Mathlib's `Real.summable_one_div_nat_pow`. -/
theorem summable_inv_sq : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr one_lt_two
-- @endregion

/-! ### Percolation: Peierls' argument -/

-- @region random_geometry.peierls_tendsto
-- @provenance independent
/-- **Peierls' estimate.** If there are at most `cₙ ≤ 4 · 3ⁿ` self-avoiding paths of length `n`
from the origin and each is open with probability `pⁿ`, then for `p < 1/3` the expected number of
open such paths, at most `cₙ pⁿ ≤ 4(3p)ⁿ`, tends to `0`. So the origin lies in an infinite open
cluster with probability `0`, and `p_c(ℤ²) ≥ 1/3`. (The count `cₙ ≤ 4 · 3^{n-1}` is proved in the
lesson; here it is a hypothesis.) -/
theorem peierls_tendsto {c : ℕ → ℕ} (hc : ∀ n, c n ≤ 4 * 3 ^ n) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p < 1 / 3) : Tendsto (fun n => (c n : ℝ) * p ^ n) atTop (𝓝 0) := by
  have h3 : 3 * p < 1 := by linarith
  have hlim : Tendsto (fun n : ℕ => 4 * (3 * p) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) h3).const_mul 4
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have : (c n : ℝ) ≤ 4 * 3 ^ n := by exact_mod_cast hc n
  calc (c n : ℝ) * p ^ n ≤ (4 * 3 ^ n) * p ^ n := by gcongr
    _ = 4 * (3 * p) ^ n := by ring
-- @endregion

-- @region random_geometry.dual_circuits_summable
-- @provenance library
/-- **The dual half of Peierls' argument.** The number of dual circuits of length `n` surrounding
the origin is at most `n · 4 · 3ⁿ`, and each is closed with probability `qⁿ`, `q = 1 − p`. For
`q < 1/3` the series `∑ n · 4 · 3ⁿ qⁿ` converges, so its tails tend to `0`; this gives
`p_c(ℤ²) ≤ 2/3`. Uses Mathlib's `summable_pow_mul_geometric_of_norm_lt_one`. -/
theorem dual_circuits_summable {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1 / 3) :
    Summable (fun n : ℕ => (n : ℝ) * 4 * 3 ^ n * q ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := 3 * q)
    (by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith)
  refine (h.mul_left 4).congr (fun n => ?_)
  ring
-- @endregion

/-! ### Random graphs: no giant component below the threshold -/

-- @region random_geometry.no_giant_subcritical
-- @provenance independent
/-- **No giant component for `c ≤ 1`.** The fraction `β` of vertices of `G(n, c/n)` in the giant
component satisfies, in the limit, the survival equation of a Poisson(`c`) branching process,
`β = 1 − e^{−cβ}`. For `c ≤ 1` its only solution `β ≥ 0` is `β = 0`, because `1 − e^{−x} < x` for
`x > 0` (from Mathlib's `Real.add_one_lt_exp`). For `c > 1` a second, positive root appears. -/
theorem no_giant_subcritical {c β : ℝ} (hc : c ≤ 1) (hc0 : 0 ≤ c) (hβ : 0 ≤ β)
    (h : β = 1 - Real.exp (-(c * β))) : β = 0 := by
  by_contra hne
  have hpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hne)
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · subst hc0'
    simp at h
    exact hne h
  · have hx : 0 < c * β := mul_pos hc0' hpos
    have := Real.add_one_lt_exp (show -(c * β) ≠ 0 by linarith)
    nlinarith
-- @endregion

end Lumenary.RandomGeometry
