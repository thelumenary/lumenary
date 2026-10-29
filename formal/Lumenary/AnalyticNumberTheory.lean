/-
The Lumenary — formal mathematics
Analytic number theory: Möbius inversion, the Euler product, the Riemann zeta function, its
functional equation and zeros, Chebyshev's bounds, and Dirichlet's theorem.

What is proved here. Independently: Möbius inversion from the identity `ζ * μ = 1` in the ring of
arithmetic functions; the trigonometric inequality `3 + 4 cos θ + cos 2θ ≥ 0` behind the
non-vanishing of `ζ` on the line `Re s = 1`; `2ⁿ ≤ (n + 1) · lcm(1, …, n)`, and from it Chebyshev's
lower bound `ψ(n) ≥ n log 2 − log(n + 1)`.

What Mathlib provides. Arithmetic functions (`ArithmeticFunction`, with `μ`, `ζ`, `Λ`), the
Riemann zeta function `riemannZeta` (analytically continued to `ℂ ∖ {1}`), its Euler product,
`ζ(2) = π²/6`, the residue `1` at `s = 1`, the functional equation of the completed zeta function,
the trivial zeros, the non-vanishing of `ζ` on `Re s ≥ 1`, the divergence of `∑ 1/p`, the
Chebyshev functions `θ` and `ψ` with Chebyshev's upper bound, and Dirichlet's theorem on primes in
arithmetic progressions (`Nat.infinite_setOfPred_prime_and_eq_mod`). Mathlib also states the
Riemann hypothesis (`RiemannHypothesis`) — an open problem. Not in Mathlib (at this version): the
prime number theorem `π(x) ~ x / log x`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.Chebyshev

namespace Lumenary.AnalyticNumberTheory

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-! ### Arithmetic functions and Möbius inversion -/

-- @region analytic_number_theory.moebius_inversion
-- @provenance independent
/-- **Möbius inversion**, proved in the ring of arithmetic functions under Dirichlet convolution
`*`. If `g = f * ζ` — that is, `g(n) = ∑_{d ∣ n} f(d)` — then `f = g * μ`, i.e.
`f(n) = ∑_{d ∣ n} μ(d) g(n/d)`. The proof is three lines of algebra, using associativity of `*` and
the identity `ζ * μ = 1` (Mathlib: `coe_zeta_mul_moebius`), which says `∑_{d ∣ n} μ(d) = 0` for
`n > 1`. -/
theorem moebius_inversion (f g : ArithmeticFunction ℤ) (h : g = f * ζ) : f = g * μ :=
  calc f = f * 1 := (mul_one f).symm
    _ = f * ((ζ : ArithmeticFunction ℤ) * μ) := by rw [coe_zeta_mul_moebius]
    _ = (f * ζ) * μ := (mul_assoc _ _ _).symm
    _ = g * μ := by rw [h]
-- @endregion

-- @region analytic_number_theory.moebius_inversion_sums
-- @provenance library
/-- **Möbius inversion, written with sums**: `∑_{d ∣ n} f(d) = g(n)` for all `n > 0` if and only if
`f(n) = ∑_{ab = n} μ(a) g(b)` for all `n > 0`. Mathlib:
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`. -/
theorem moebius_inversion_sums {f g : ℕ → ℤ} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : ℤ) * g x.snd = f n :=
  sum_eq_iff_sum_mul_moebius_eq
-- @endregion

-- @region analytic_number_theory.von_mangoldt_sum
-- @provenance library
/-- **`∑_{d ∣ n} Λ(d) = log n`** — unique factorisation, written additively: if
`n = ∏ pᵢ^{aᵢ}` then the prime powers dividing `n` contribute `∑ aᵢ log pᵢ = log n`. As Dirichlet
series this is `−ζ'(s)/ζ(s) = ∑ Λ(n) n^{−s}`. Mathlib: `ArithmeticFunction.vonMangoldt_sum`. -/
theorem von_mangoldt_sum (n : ℕ) : ∑ i ∈ n.divisors, Λ i = Real.log n :=
  vonMangoldt_sum
-- @endregion

/-! ### The Riemann zeta function -/

-- @region analytic_number_theory.euler_product
-- @provenance library
/-- **Euler product**: for `Re s > 1`, `∏_p (1 − p^{−s})^{−1} = ζ(s)`, the analytic form of unique
factorisation. Mathlib: `riemannZeta_eulerProduct_tprod`. -/
theorem euler_product {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs
-- @endregion

-- @region analytic_number_theory.sum_inv_primes_diverges
-- @provenance library
/-- **Euler: `∑ 1/p` diverges**, so there are infinitely many primes, and they are not too sparse.
Mathlib: `Nat.Primes.not_summable_one_div` (proved by Erdős's elementary argument). -/
theorem sum_inv_primes_diverges : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div
-- @endregion

-- @region analytic_number_theory.zeta_two
-- @provenance library
/-- **The Basel problem**: `ζ(2) = π²/6` (Euler, 1734). Mathlib: `riemannZeta_two`. -/
theorem zeta_two : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 :=
  riemannZeta_two
-- @endregion

-- @region analytic_number_theory.zeta_residue
-- @provenance library
/-- **`ζ` has a simple pole with residue `1` at `s = 1`**: `(s − 1) ζ(s) → 1` as `s → 1`. Mathlib:
`riemannZeta_residue_one`. -/
theorem zeta_residue :
    Filter.Tendsto (fun s ↦ (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) :=
  riemannZeta_residue_one
-- @endregion

-- @region analytic_number_theory.functional_equation
-- @provenance library
/-- **The functional equation** (Riemann, 1859): the completed zeta function
`Λ(s) = π^{−s/2} Γ(s/2) ζ(s)` satisfies `Λ(1 − s) = Λ(s)` for every complex `s`. Mathlib:
`completedRiemannZeta_one_sub`. -/
theorem functional_equation (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s
-- @endregion

-- @region analytic_number_theory.trivial_zeros
-- @provenance library
/-- **The trivial zeros**: `ζ(−2), ζ(−4), ζ(−6), …` all vanish (the poles of `Γ(s/2)` must be
cancelled in the functional equation). Mathlib: `riemannZeta_neg_two_mul_nat_add_one`. -/
theorem trivial_zeros (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n
-- @endregion

-- @region analytic_number_theory.three_four_one
-- @provenance independent
/-- **The `3–4–1` inequality** (Mertens, 1898): `3 + 4 cos θ + cos 2θ ≥ 0` for all real `θ`, because
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)²`. Applied with `θ = t log n` it gives
`|ζ(σ)³ ζ(σ + it)⁴ ζ(σ + 2it)| ≥ 1` for `σ > 1`, which rules out a zero on the line `Re s = 1`. -/
theorem three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (1 + Real.cos θ)]
-- @endregion

-- @region analytic_number_theory.zeta_ne_zero_one_line
-- @provenance library
/-- **`ζ(s) ≠ 0` for `Re s ≥ 1`** (Hadamard and de la Vallée Poussin, 1896) — the analytic heart of
the prime number theorem. Mathlib: `riemannZeta_ne_zero_of_one_le_re`, proved with the `3–4–1`
trick. -/
theorem zeta_ne_zero_one_line {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs
-- @endregion

-- @region analytic_number_theory.critical_line_hypothesis
-- @provenance definition
/-- **The Riemann hypothesis, stated** (an open problem since 1859): every zero of `ζ` other than
the trivial zeros `−2, −4, −6, …` lies on the critical line `Re s = 1/2`. (The condition `s ≠ 1`
is harmless: Mathlib assigns `ζ(1)` a junk value.) Lean can *state* this precisely; no one can
prove it. -/
def CriticalLineHypothesis : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2
-- @endregion

-- @region analytic_number_theory.critical_line_iff
-- @provenance library
/-- **Our statement agrees with Mathlib's `RiemannHypothesis`** — a check that we have read the
definition correctly, not a proof of anything about zeros. -/
theorem critical_line_iff : CriticalLineHypothesis ↔ RiemannHypothesis :=
  Iff.rfl
-- @endregion

/-! ### Chebyshev's bounds -/

-- @region analytic_number_theory.two_pow_le_lcm
-- @provenance independent
/-- **`2ⁿ ≤ (n + 1) · lcm(1, 2, …, n)`.** Human proof: `2ⁿ = ∑_{k=0}^{n} C(n, k)` has `n + 1` terms,
and each binomial coefficient `C(n, k)` divides `lcm(1, …, n)` (Mathlib:
`Chebyshev.choose_dvd_lcmUpto`, a `p`-adic valuation argument), so is at most it. -/
theorem two_pow_le_lcm (n : ℕ) : 2 ^ n ≤ (n + 1) * Nat.lcmUpto n :=
  calc 2 ^ n = ∑ k ∈ Finset.range (n + 1), n.choose k := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _k ∈ Finset.range (n + 1), Nat.lcmUpto n := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact Nat.le_of_dvd (Nat.lcmUpto_pos n) (Chebyshev.choose_dvd_lcmUpto hkn)
    _ = (n + 1) * Nat.lcmUpto n := by simp
-- @endregion

-- @region analytic_number_theory.chebyshev_lower
-- @provenance independent
/-- **Chebyshev's lower bound**: `ψ(n) ≥ n log 2 − log(n + 1)`, so `ψ(x) ≫ x`. Take logarithms in
`two_pow_le_lcm` and use `ψ(n) = log lcm(1, …, n)` (Mathlib: `Chebyshev.psi_eq_log_lcmUpto`) — the
exponent of `p` in `lcm(1, …, n)` is the number of powers of `p` up to `n`. -/
theorem chebyshev_lower (n : ℕ) : n * Real.log 2 - Real.log (n + 1) ≤ Chebyshev.psi n := by
  have hpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have hkey : ((2 : ℝ) ^ n) ≤ (n + 1) * Nat.lcmUpto n := by exact_mod_cast two_pow_le_lcm n
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_pow, Real.log_mul (by positivity) hpos.ne'] at hlog
  rw [Chebyshev.psi_eq_log_lcmUpto]
  linarith
-- @endregion

-- @region analytic_number_theory.chebyshev_upper
-- @provenance library
/-- **Chebyshev's upper bound**: `θ(x) = ∑_{p ≤ x} log p ≤ x log 4`, from `∏_{p ≤ n} p ≤ 4ⁿ`
(Mathlib: `primorial_le_four_pow`). Mathlib: `Chebyshev.theta_le_log4_mul_x`. -/
theorem chebyshev_upper {x : ℝ} (hx : 0 ≤ x) : Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx
-- @endregion

/-! ### Primes in arithmetic progressions -/

-- @region analytic_number_theory.dirichlet_theorem
-- @provenance library
/-- **Dirichlet's theorem** (1837): if `a` is a unit modulo `q`, there are infinitely many primes
`p ≡ a (mod q)`. The proof needs `L(1, χ) ≠ 0` for every non-trivial Dirichlet character `χ`.
Mathlib: `Nat.infinite_setOfPred_prime_and_eq_mod`. -/
theorem dirichlet_theorem {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite :=
  Nat.infinite_setOfPred_prime_and_eq_mod ha
-- @endregion

end Lumenary.AnalyticNumberTheory
