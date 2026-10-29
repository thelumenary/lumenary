/-
The Lumenary — formal mathematics
Polynomials: special products, the remainder and factor theorems, the division algorithm, and
the bound "a non-zero polynomial of degree n has at most n roots".

Proved here (`@provenance independent`): the special products; `x − a ∣ xⁿ − aⁿ` by induction;
the remainder theorem `X − a ∣ p − p(a)` and the factor theorem, by the same argument as the
lesson; uniqueness of quotient and remainder in the division algorithm; the root bound for any
finite set of roots over an integral domain, by induction exactly as in the lesson; the identity
theorem (two polynomials of degree ≤ n that agree at n + 1 points are equal); and the fact that
`x² − 1` has four roots in the integers modulo 8, which shows why the root bound needs the
zero-product property.

From Mathlib (`@provenance library`): the remainder as `p %ₘ (X − C a) = C (p.eval a)`
(`Polynomial.modByMonic_X_sub_C_eq_C_eval`), existence in the division algorithm over a field
(`EuclideanDomain.div_add_mod`, `Polynomial.degree_mod_lt`), and the multiset version of the
root bound (`Polynomial.card_roots'`).

Notation: `R[X]` is Mathlib's type of polynomials with coefficients in `R`, `C a` is the constant
polynomial `a`, `p.eval a` is `p(a)` and `p.natDegree` is the degree of `p`.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Lemmas

namespace Lumenary.Polynomials

open Polynomial

/-! ### Special products -/

-- @region polynomials.diff_of_squares
-- @provenance independent
/-- **Difference of two squares:** `a² − b² = (a − b)(a + b)` in every commutative ring.
`ring` expands both sides and compares them — exactly the check you would do by hand. -/
theorem diff_of_squares {R : Type*} [CommRing R] (a b : R) :
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring
-- @endregion

-- @region polynomials.sum_of_cubes
-- @provenance independent
/-- **Sum and difference of two cubes:** `a³ + b³ = (a + b)(a² − ab + b²)` and
`a³ − b³ = (a − b)(a² + ab + b²)`. -/
theorem sum_and_diff_of_cubes {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) ∧
      a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  constructor <;> ring
-- @endregion

/-! ### The remainder and factor theorems -/

-- @region polynomials.sub_dvd_pow_sub_pow
-- @provenance independent
/-- **`x − a` divides `xⁿ − aⁿ`**, by induction on `n`, using the lesson's identity
`xⁿ⁺¹ − aⁿ⁺¹ = x(xⁿ − aⁿ) + aⁿ(x − a)`. (Mathlib: `sub_dvd_pow_sub_pow`.) -/
theorem sub_dvd_pow_sub_pow' {R : Type*} [CommRing R] (x a : R) (n : ℕ) :
    x - a ∣ x ^ n - a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨x * q + a ^ n, ?_⟩
    calc x ^ (n + 1) - a ^ (n + 1) = x * (x ^ n - a ^ n) + a ^ n * (x - a) := by ring
      _ = x * ((x - a) * q) + a ^ n * (x - a) := by rw [hq]
      _ = (x - a) * (x * q + a ^ n) := by ring
-- @endregion

-- @region polynomials.remainder_theorem
-- @provenance independent
/-- **Remainder theorem:** `X − a` divides `p − p(a)`, so `p = (X − a)·q + p(a)`.
As in the lesson: `p − p(a)` is a sum of terms `c (Xᵏ − aᵏ)`, and `X − a` divides each of them
(`sub_dvd_pow_sub_pow'`). Lean's induction principle `Polynomial.induction_on'` builds every
polynomial from single terms `c Xᵏ` by addition, so we check those two cases. -/
theorem remainder_theorem {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    X - C a ∣ p - C (p.eval a) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : p + q - C ((p + q).eval a) = (p - C (p.eval a)) + (q - C (q.eval a)) := by
      rw [eval_add, C_add]; ring
    rw [h]
    exact dvd_add hp hq
  | monomial n c =>
    have h : monomial n c - C ((monomial n c).eval a) = C c * (X ^ n - (C a) ^ n) := by
      rw [eval_monomial, ← C_mul_X_pow_eq_monomial, C_mul, C_pow]; ring
    rw [h]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow' X (C a) n) (C c)
-- @endregion

-- @region polynomials.remainder_theorem_library
-- @provenance library
/-- **Remainder theorem, Mathlib's form:** the remainder on dividing `p` by the monic polynomial
`X − a` is the constant `p(a)`. This applies `Polynomial.modByMonic_X_sub_C_eq_C_eval`. -/
theorem remainder_theorem_library {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    p %ₘ (X - C a) = C (p.eval a) :=
  modByMonic_X_sub_C_eq_C_eval p a
-- @endregion

-- @region polynomials.factor_theorem
-- @provenance independent
/-- **Factor theorem:** `X − a` divides `p` exactly when `p(a) = 0`.
(→) If `p = (X − a)·q` then `p(a) = (a − a)·q(a) = 0`.
(←) If `p(a) = 0`, the remainder theorem says `X − a` divides `p − 0 = p`.
(Mathlib: `Polynomial.dvd_iff_isRoot`.) -/
theorem factor_theorem {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    X - C a ∣ p ↔ p.eval a = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro h
    have := remainder_theorem p a
    rwa [h, C_0, sub_zero] at this
-- @endregion

/-! ### The division algorithm -/

-- @region polynomials.division_exists
-- @provenance library
/-- **Division algorithm (existence)** over a field such as `ℚ` or `ℝ`: for `d ≠ 0` there are
`q` and `r` with `p = q·d + r` and `deg r < deg d` (Mathlib's `degree` of the zero polynomial is
`⊥`, below every natural number, so `r = 0` is included). This applies
`EuclideanDomain.div_add_mod` and `Polynomial.degree_mod_lt`. -/
theorem division_exists {K : Type*} [Field K] (p d : K[X]) (hd : d ≠ 0) :
    ∃ q r : K[X], p = q * d + r ∧ r.degree < d.degree :=
  ⟨p / d, p % d, by rw [mul_comm]; exact (EuclideanDomain.div_add_mod p d).symm,
    degree_mod_lt p hd⟩
-- @endregion

-- @region polynomials.division_unique
-- @provenance independent
/-- **Division algorithm (uniqueness):** quotient and remainder are unique.
If `q₁d + r₁ = q₂d + r₂` with both remainders of degree `< deg d`, then
`(q₁ − q₂)·d = r₂ − r₁`. If `q₁ ≠ q₂`, the left side has degree `≥ deg d`, but the right side has
degree `< deg d` — impossible. So `q₁ = q₂`, and then `r₁ = r₂`. -/
theorem division_unique {K : Type*} [Field K] {d q₁ r₁ q₂ r₂ : K[X]}
    (h : q₁ * d + r₁ = q₂ * d + r₂) (h₁ : r₁.degree < d.degree) (h₂ : r₂.degree < d.degree) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have key : (q₁ - q₂) * d = r₂ - r₁ := by linear_combination h
  have hq : q₁ = q₂ := by
    by_contra hne
    have hd : d ≠ 0 := by
      rintro rfl
      simp at h₁
    have hsub : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hne
    -- the degree of the left side is at least `deg d`
    have hle : d.degree ≤ ((q₁ - q₂) * d).degree := by
      rw [degree_mul, add_comm]
      exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hsub)
    -- the degree of the right side is less than `deg d`
    have hlt : (r₂ - r₁).degree < d.degree :=
      lt_of_le_of_lt (degree_sub_le r₂ r₁) (max_lt h₂ h₁)
    rw [key] at hle
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  subst hq
  exact ⟨rfl, by linear_combination h⟩
-- @endregion

/-! ### Rational roots -/

-- @region polynomials.rational_root_cubic
-- @provenance independent
/-- **Rational root theorem (degree 3).** Suppose the fraction `p/q` in lowest terms is a root of
`a₃x³ + a₂x² + a₁x + a₀` with integer coefficients. Multiplying by `q³` gives the hypothesis `h`.
Then `p` divides the constant term `a₀` and `q` divides the leading coefficient `a₃`.
Proof: `a₀q³ = −p(a₃p² + a₂pq + a₁q²)` is a multiple of `p`, and `p` shares no factor with
`q³`, so `p ∣ a₀`; symmetrically for `q`. (The general degree-`n` statement is Mathlib's
`num_dvd_of_is_root` and `den_dvd_of_is_root`.) -/
theorem rational_root_cubic {a₀ a₁ a₂ a₃ p q : ℤ} (hpq : IsCoprime p q)
    (h : a₃ * p ^ 3 + a₂ * p ^ 2 * q + a₁ * p * q ^ 2 + a₀ * q ^ 3 = 0) :
    p ∣ a₀ ∧ q ∣ a₃ := by
  constructor
  · have h1 : p ∣ a₀ * q ^ 3 :=
      ⟨-(a₃ * p ^ 2 + a₂ * p * q + a₁ * q ^ 2), by linear_combination h⟩
    exact hpq.pow_right.dvd_of_dvd_mul_right h1
  · have h2 : q ∣ a₃ * p ^ 3 :=
      ⟨-(a₂ * p ^ 2 + a₁ * p * q + a₀ * q ^ 2), by linear_combination h⟩
    exact hpq.symm.pow_right.dvd_of_dvd_mul_right h2
-- @endregion

/-! ### At most `n` roots -/

-- @region polynomials.card_roots_le_nat_degree
-- @provenance independent
/-- **A non-zero polynomial of degree `n` has at most `n` roots** (over any integral domain:
`ℤ`, `ℚ`, `ℝ`, `ℂ`, …). If `S` is a finite set of roots of `p ≠ 0`, then `|S| ≤ deg p`.
Proof by induction on `S`, as in the lesson: if `a` is a root, the factor theorem gives
`p = (X − a)·q` with `deg q = deg p − 1`; every *other* root `b` of `p` satisfies
`(b − a)·q(b) = 0` with `b − a ≠ 0`, so `q(b) = 0` (zero-product property); induction on `q`
finishes. -/
theorem card_roots_le_natDegree {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (S : Finset R) : ∀ p : R[X], p ≠ 0 → (∀ a ∈ S, p.eval a = 0) → S.card ≤ p.natDegree := by
  induction S using Finset.induction_on with
  | empty => intro p _ _; simp
  | insert a S haS ih =>
    intro p hp hroots
    obtain ⟨q, rfl⟩ := (factor_theorem p a).mpr (hroots a (Finset.mem_insert_self a S))
    have hq : q ≠ 0 := by
      rintro rfl
      simp at hp
    -- every other root of `p` is a root of `q`
    have hS : ∀ b ∈ S, q.eval b = 0 := by
      intro b hb
      have hb' := hroots b (Finset.mem_insert_of_mem hb)
      rw [eval_mul, eval_sub, eval_X, eval_C] at hb'
      have hba : b - a ≠ 0 := sub_ne_zero.mpr (fun h => haS (h ▸ hb))
      exact (mul_eq_zero.mp hb').resolve_left hba
    have hdeg : ((X - C a) * q).natDegree = q.natDegree + 1 := by
      rw [natDegree_mul (X_sub_C_ne_zero a) hq, natDegree_X_sub_C, add_comm]
    rw [Finset.card_insert_of_notMem haS, hdeg]
    exact Nat.succ_le_succ (ih q hq hS)
-- @endregion

-- @region polynomials.card_roots_library
-- @provenance library
/-- **The root bound, Mathlib's form:** the multiset of roots of `p` (each root counted with
multiplicity) has at most `deg p` elements. This applies `Polynomial.card_roots'`. -/
theorem card_roots_library {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) :
    Multiset.card p.roots ≤ p.natDegree :=
  card_roots' p
-- @endregion

-- @region polynomials.eq_of_agree
-- @provenance independent
/-- **Identity theorem:** if two polynomials of degree `≤ n` agree at `n + 1` different points,
they are the same polynomial. Their difference has degree `≤ n` and at least `n + 1` roots, so by
`card_roots_le_natDegree` it must be the zero polynomial. -/
theorem eq_of_agree {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {p q : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (S : Finset R) (hS : n + 1 ≤ S.card)
    (hagree : ∀ a ∈ S, p.eval a = q.eval a) : p = q := by
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hroots : ∀ a ∈ S, (p - q).eval a = 0 := by
    intro a ha
    rw [eval_sub, hagree a ha, sub_self]
  have h1 := card_roots_le_natDegree S (p - q) hsub hroots
  have h2 : (p - q).natDegree ≤ n := (natDegree_sub_le p q).trans (max_le hp hq)
  omega
-- @endregion

-- @region polynomials.four_roots_mod_eight
-- @provenance independent
/-- **Why the zero-product property matters.** In the integers modulo 8 (where `2 · 4 = 0` with
neither factor zero) the degree-2 polynomial `x² − 1` has **four** roots: `1, 3, 5, 7`.
`decide` checks all eight residues. -/
theorem four_roots_mod_eight :
    ∀ x : ZMod 8, x ^ 2 - 1 = 0 ↔ x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7 := by
  decide
-- @endregion

-- @region polynomials.two_roots_mod_seven
-- @provenance independent
/-- **Contrast:** modulo the prime 7 there are no zero divisors, and `x² − 1` has only the two
roots `1` and `6 = −1`, as the root bound predicts. `decide` checks all seven residues. -/
theorem two_roots_mod_seven : ∀ x : ZMod 7, x ^ 2 - 1 = 0 ↔ x = 1 ∨ x = 6 := by
  decide
-- @endregion

end Lumenary.Polynomials
