/-
The Lumenary — formal mathematics
Rings, ideals and fields: units and zero divisors, finite integral domains, kernels and ideals,
prime and irreducible elements, and the hierarchy Euclidean domain ⇒ PID ⇒ UFD, with ℤ[√−5]
as a ring where unique factorisation fails.

What is proved here and what Mathlib provides. Proved independently: units are not zero divisors;
`ℤ/6ℤ` has zero divisors; in a finite integral domain every non-zero element is invertible; an
ideal containing a unit is everything, so a field has only two ideals; prime elements of a domain
are irreducible, and in a principal ideal domain irreducible elements are prime (Euclid's lemma,
the heart of "PID ⇒ UFD"); `ℤ[X]` is not a principal ideal domain; and in `ℤ[√−5]` the element `2`
is irreducible but not prime, so `ℤ[√−5]` is not a unique factorisation domain. Cited from Mathlib:
Euclidean domains are PIDs, PIDs are UFDs, `K[X]` and `ℤ[i]` are Euclidean, `ℤ[X]` is a UFD, and a
finite domain is a field. Mathlib writes `ℤ√d` for the ring `ℤ[√d]` (`Zsqrtd d`).
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic

namespace Lumenary.Rings

open Polynomial

/-! ### Units, zero divisors and finite domains -/

-- @region rings.unit_mul_eq_zero
-- @provenance independent
/-- A unit is never a zero divisor: if `u` is a unit and `u * a = 0` then `a = 0`, because
`a = u⁻¹ * (u * a) = u⁻¹ * 0 = 0`. (This works in every ring, commutative or not.) -/
theorem unit_mul_eq_zero {R : Type*} [Ring R] {u a : R} (hu : IsUnit u) (h : u * a = 0) :
    a = 0 := by
  obtain ⟨v, rfl⟩ := hu
  calc a = (↑v⁻¹ * ↑v) * a := by simp
    _ = ↑v⁻¹ * (↑v * a) := mul_assoc _ _ _
    _ = 0 := by rw [h, mul_zero]
-- @endregion

-- @region rings.zmod_six_zero_divisors
-- @provenance independent
/-- `ℤ/6ℤ` is not an integral domain: `2 · 3 = 0` although neither factor is `0`.
`decide` computes in `ZMod 6`. -/
theorem zmod_six_zero_divisors : (2 : ZMod 6) * 3 = 0 ∧ (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 := by
  decide
-- @endregion

-- @region rings.finite_domain_inverse
-- @provenance independent
/-- In a finite integral domain every non-zero `a` has an inverse. Multiplication by `a` is
injective (cancellation: `a * x = a * y` and `a ≠ 0` give `x = y`); an injective map from a
finite set to itself is surjective; so some `b` has `a * b = 1`. -/
theorem finite_domain_inverse {R : Type*} [CommRing R] [IsDomain R] [Finite R] (a : R)
    (ha : a ≠ 0) : ∃ b : R, a * b = 1 := by
  have inj : Function.Injective (fun x : R => a * x) := fun x y h => mul_left_cancel₀ ha h
  exact Finite.injective_iff_surjective.mp inj 1
-- @endregion

-- @region rings.finite_domain_is_field
-- @provenance library
/-- Every finite integral domain is a field. Mathlib's `Finite.isDomain_to_isField` proves this
even without commutativity — that stronger statement includes Wedderburn's little theorem that
finite division rings are commutative. -/
theorem finite_domain_is_field (R : Type*) [CommRing R] [IsDomain R] [Finite R] : IsField R :=
  Finite.isDomain_to_isField R
-- @endregion

/-! ### Kernels and ideals -/

-- @region rings.ker_ideal
-- @provenance definition
/-- The kernel of a ring homomorphism, built by hand as an ideal: it contains `0`, is closed
under addition, and absorbs multiplication, since `f (r * x) = f r * 0 = 0`. -/
def kerIdeal {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Ideal R where
  carrier := {x | f x = 0}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by simp_all
  smul_mem' r x hx := by simp_all
-- @endregion

-- @region rings.ker_ideal_eq
-- @provenance independent
/-- The hand-built kernel is Mathlib's `RingHom.ker f`: both are `{x | f x = 0}`. -/
theorem kerIdeal_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    kerIdeal f = RingHom.ker f := by
  ext x
  simp [kerIdeal, RingHom.mem_ker]
-- @endregion

-- @region rings.eq_top_of_unit_mem
-- @provenance independent
/-- An ideal that contains a unit `u` is the whole ring: it contains `u⁻¹ * u = 1`, and then
`r = r * 1` for every `r`. -/
theorem eq_top_of_unit_mem {R : Type*} [CommRing R] (I : Ideal R) {u : R} (hu : IsUnit u)
    (h : u ∈ I) : I = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  obtain ⟨v, rfl⟩ := hu
  have : (↑v⁻¹ * ↑v : R) ∈ I := I.mul_mem_left _ h
  simpa using this
-- @endregion

-- @region rings.field_ideals
-- @provenance independent
/-- A field has exactly two ideals, `0` and the whole field: a non-zero ideal contains a non-zero
element, which is a unit. -/
theorem field_ideals {K : Type*} [Field K] (I : Ideal K) : I = ⊥ ∨ I = ⊤ := by
  by_cases h : I = ⊥
  · exact Or.inl h
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact Or.inr (eq_top_of_unit_mem I (IsUnit.mk0 x hx0) hx)
-- @endregion

/-! ### Prime and irreducible elements -/

-- @region rings.prime_irreducible
-- @provenance independent
/-- In an integral domain every prime element is irreducible. If `p = a * b`, then `p ∣ a` or
`p ∣ b`; say `a = p * c`. Then `p = p * c * b`, and cancelling `p ≠ 0` gives `1 = c * b`, so `b`
is a unit. -/
theorem prime_irreducible {R : Type*} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) :
    Irreducible p := by
  refine ⟨hp.not_isUnit, fun a b hab => ?_⟩
  rcases hp.dvd_or_dvd ⟨1, by rw [← hab, mul_one]⟩ with ⟨c, hc⟩ | ⟨c, hc⟩
  · right
    have h : p * 1 = p * (c * b) := by
      calc p * 1 = a * b := by rw [mul_one, hab]
        _ = p * (c * b) := by rw [hc, mul_assoc]
    exact IsUnit.of_mul_eq_one_right c (mul_left_cancel₀ hp.ne_zero h).symm
  · left
    have h : p * 1 = p * (c * a) := by
      calc p * 1 = a * b := by rw [mul_one, hab]
        _ = p * (c * a) := by rw [hc, mul_comm a, mul_assoc]
    exact IsUnit.of_mul_eq_one_right c (mul_left_cancel₀ hp.ne_zero h).symm
-- @endregion

-- @region rings.pid_irreducible_prime
-- @provenance independent
/-- **Euclid's lemma in a principal ideal domain**: irreducible elements are prime. Let `p` be
irreducible with `p ∣ a * b` and `p ∤ a`. The ideal `(p, a)` is principal, say `(d)`. From
`p = d * x`, either `x` is a unit — then `(d) = (p)` contains `a`, so `p ∣ a`, impossible — or `d`
is a unit, so `(p, a)` is everything: `1 = r * p + s * a`. Then `b = r * p * b + s * (a * b)` is
divisible by `p`. -/
theorem pid_irreducible_prime {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {p : R} (hp : Irreducible p) : Prime p := by
  refine ⟨hp.ne_zero, hp.not_isUnit, fun a b hab => ?_⟩
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  right
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (Ideal.span {p, a})).principal
  have hd' : Ideal.span {p, a} = Ideal.span {d} := hd
  have hpd : p ∈ Ideal.span {d} := by rw [← hd']; exact Ideal.subset_span (by simp)
  have had : a ∈ Ideal.span {d} := by rw [← hd']; exact Ideal.subset_span (by simp)
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hpd
  have hpdx : p = d * x := by rw [← hx, mul_comm]
  rcases hp.isUnit_or_isUnit hpdx with hdu | hxu
  · -- `d` is a unit, so `1 ∈ (p, a)`.
    have h1 : (1 : R) ∈ Ideal.span {p, a} := by
      rw [hd', eq_top_of_unit_mem _ hdu (Ideal.mem_span_singleton_self d)]
      exact Submodule.mem_top
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp h1
    obtain ⟨c, hc⟩ := hab
    exact ⟨r * b + s * c, by
      calc b = (r * p + s * a) * b := by rw [hrs, one_mul]
        _ = p * (r * b + s * c) := by rw [add_mul, mul_assoc s, hc]; ring⟩
  · -- `x` is a unit, so `d` divides `p` and `p` divides `d ∣ a`: contradiction.
    exfalso
    apply hpa
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp had
    obtain ⟨u, rfl⟩ := hxu
    exact ⟨y * ↑u⁻¹, by rw [← hy, ← hx]; linear_combination (-(y * d)) * Units.mul_inv u⟩
-- @endregion

/-! ### Euclidean domain ⇒ PID ⇒ UFD -/

-- @region rings.ed_is_pid
-- @provenance library
/-- Every Euclidean domain is a principal ideal domain: a non-zero ideal is generated by any of
its elements of least size. This is Mathlib's instance `EuclideanDomain.instIsPrincipalIdealRing`. -/
theorem ed_is_pid (R : Type*) [EuclideanDomain R] : IsPrincipalIdealRing R :=
  inferInstance
-- @endregion

-- @region rings.pid_is_ufd
-- @provenance library
/-- Every principal ideal domain is a unique factorisation domain. Mathlib's instance
`PrincipalIdealRing.to_uniqueFactorizationMonoid` combines Euclid's lemma (`pid_irreducible_prime`
above) with the ascending chain condition on principal ideals. -/
theorem pid_is_ufd (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R :=
  inferInstance
-- @endregion

-- @region rings.polynomial_pid
-- @provenance library
/-- For a field `K`, the polynomial ring `K[X]` is Euclidean (divide with remainder, measuring
size by degree), hence a principal ideal domain. Mathlib: `Polynomial.instEuclideanDomain`. -/
theorem polynomial_pid (K : Type*) [Field K] : IsPrincipalIdealRing K[X] :=
  inferInstance
-- @endregion

-- @region rings.gaussian_pid
-- @provenance library
/-- The Gaussian integers `ℤ[i]` are Euclidean for the norm `a² + b²` (round the exact quotient
in `ℚ(i)` to the nearest lattice point), hence a principal ideal domain. Mathlib: the
`EuclideanDomain` instance on `GaussianInt`. -/
theorem gaussian_pid : IsPrincipalIdealRing GaussianInt :=
  inferInstance
-- @endregion

-- @region rings.int_poly_ufd
-- @provenance library
/-- `ℤ[X]` is a unique factorisation domain (Gauss's lemma: `R[X]` is a UFD when `R` is).
Mathlib: `Polynomial.uniqueFactorizationMonoid`. -/
theorem int_poly_ufd : UniqueFactorizationMonoid ℤ[X] :=
  inferInstance
-- @endregion

-- @region rings.int_poly_not_pid
-- @provenance independent
/-- `ℤ[X]` is **not** a principal ideal domain: the ideal `(2, X)` is not principal. If
`(2, X) = (f)`, then `f ∣ 2` forces `f` to be a constant `c`; `f ∣ X` forces `c ∣ 1`; but every
element `2g + Xh` of `(2, X)` has an even constant term, so `c` is even. -/
theorem int_poly_not_pid : ¬ IsPrincipalIdealRing ℤ[X] := by
  intro h
  obtain ⟨f, hf⟩ := (h.principal (Ideal.span {(2 : ℤ[X]), X})).principal
  have hfs : Ideal.span {(2 : ℤ[X]), X} = Ideal.span {f} := hf
  have h2 : (2 : ℤ[X]) ∈ Ideal.span {f} := by rw [← hfs]; exact Ideal.subset_span (by simp)
  have hX : (X : ℤ[X]) ∈ Ideal.span {f} := by rw [← hfs]; exact Ideal.subset_span (by simp)
  have hf' : f ∈ Ideal.span {(2 : ℤ[X]), X} := by rw [hfs]; exact Ideal.mem_span_singleton_self f
  -- The constant term of `f` is even.
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hf'
  have heven : f.coeff 0 = 2 * a.coeff 0 := by
    rw [← hab]
    simp [mul_comm]
  -- `f` is constant, because it divides `2`.
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h2
  have hf0 : f ≠ 0 := by rintro rfl; simp at hg
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hdeg : f.natDegree = 0 := by
    have := congrArg natDegree hg
    rw [natDegree_mul hg0 hf0] at this
    have h2deg : (2 : ℤ[X]).natDegree = 0 := natDegree_ofNat 2
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg] at hX
  -- `C c ∣ X` gives `c * q₁ = 1`, so `c ∣ 1`; but `c` is even.
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hX
  have h1 := congrArg (fun p : ℤ[X] => p.coeff 1) hq
  simp only [coeff_mul_C, coeff_X_one] at h1
  rw [heven] at h1
  have h21 : (2 : ℤ) ∣ 1 := ⟨q.coeff 1 * a.coeff 0, by rw [← h1]; ring⟩
  omega
-- @endregion

/-! ### ℤ[√−5]: unique factorisation fails -/

-- @region rings.norm_formula
-- @provenance independent
/-- The norm on `ℤ[√−5]` is `N(x + y√−5) = (x + y√−5)(x − y√−5) = x² + 5y²`. It is
multiplicative (Mathlib's `Zsqrtd.norm_mul`). -/
theorem norm_formula (z : ℤ√(-5)) : z.norm = z.re ^ 2 + 5 * z.im ^ 2 := by
  rw [Zsqrtd.norm_def]
  ring
-- @endregion

-- @region rings.norm_eq_zero
-- @provenance independent
/-- Only `0` has norm `0`: `x² + 5y² = 0` forces `x = y = 0`. -/
theorem norm_eq_zero (z : ℤ√(-5)) (h : z.norm = 0) : z = 0 := by
  rw [norm_formula] at h
  have hre : z.re ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have him : z.im ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  ext
  · simpa using hre
  · simpa using him
-- @endregion

-- @region rings.is_domain
-- @provenance definition
/-- `ℤ[√−5]` is an integral domain: if `a * b = 0` then `N(a) N(b) = N(a * b) = 0`, so one of
the norms is `0`, and only `0` has norm `0`. (Mathlib provides this instance for `ℤ[√d]` with
`d` a positive non-square; here `d = −5`.) -/
instance isDomain : IsDomain (ℤ√(-5)) :=
  @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} h => by
    have hn := congrArg Zsqrtd.norm h
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_zero] at hn
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl (norm_eq_zero a ha)
    · exact Or.inr (norm_eq_zero b hb)⟩
-- @endregion

-- @region rings.norm_ne_two
-- @provenance independent
/-- No element of `ℤ[√−5]` has norm `2`: `x² + 5y² = 2` forces `y = 0` and then `x² = 2`. -/
theorem norm_ne_two (z : ℤ√(-5)) : z.norm ≠ 2 := by
  rw [norm_formula]
  intro h
  have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  rw [him] at h
  have hle : z.re ≤ 1 := by nlinarith
  have hge : -1 ≤ z.re := by nlinarith
  interval_cases z.re <;> simp at h
-- @endregion

-- @region rings.two_mul_three
-- @provenance independent
/-- Two factorisations of `6`: `2 · 3 = (1 + √−5)(1 − √−5)`. -/
theorem two_mul_three : (2 : ℤ√(-5)) * 3 = ⟨1, 1⟩ * ⟨1, -1⟩ := by
  decide
-- @endregion

-- @region rings.two_irreducible
-- @provenance independent
/-- `2` is irreducible in `ℤ[√−5]`. It is not a unit (its norm is `4`, units have norm `1`). If
`2 = a * b` then `N(a) N(b) = 4`; neither norm is `2` (`norm_ne_two`), so one of them is `1`, and
that factor is a unit. -/
theorem two_irreducible : Irreducible (2 : ℤ√(-5)) := by
  have hunit : ∀ z : ℤ√(-5), z.norm = 1 → IsUnit z :=
    fun z hz => (Zsqrtd.norm_eq_one_iff' (by norm_num) z).mp hz
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) 2).mpr h
    rw [norm_formula] at this
    norm_num at this
  · have hn := congrArg Zsqrtd.norm hab
    rw [Zsqrtd.norm_mul, norm_formula 2] at hn
    norm_num at hn
    have ha0 := Zsqrtd.norm_nonneg (by norm_num) a
    have hb0 := Zsqrtd.norm_nonneg (by norm_num) b
    have ha2 := norm_ne_two a
    have hb2 := norm_ne_two b
    have hapos : 0 < a.norm := by
      rcases ha0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hn; simp at hn
    have hbpos : 0 < b.norm := by
      rcases hb0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hn; simp at hn
    have hale : a.norm ≤ 4 := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ b.norm by omega) ha0
      linarith
    interval_cases hna : a.norm
    · exact Or.inl (hunit a hna)
    · exact absurd rfl ha2
    · omega
    · exact Or.inr (hunit b (by omega))
-- @endregion

-- @region rings.two_not_prime
-- @provenance independent
/-- `2` is not prime in `ℤ[√−5]`: it divides `(1 + √−5)(1 − √−5) = 6` but neither factor, since
`2 * c` always has even real part while `1 ± √−5` has real part `1`. -/
theorem two_not_prime : ¬ Prime (2 : ℤ√(-5)) := by
  intro hp
  rcases hp.dvd_or_dvd ⟨3, two_mul_three.symm⟩ with ⟨c, hc⟩ | ⟨c, hc⟩
  · have := congrArg Zsqrtd.re hc
    simp at this
    omega
  · have := congrArg Zsqrtd.re hc
    simp at this
    omega
-- @endregion

-- @region rings.not_ufd
-- @provenance independent
/-- **`ℤ[√−5]` is not a unique factorisation domain.** In a UFD every irreducible element is
prime, but `2` is irreducible (`two_irreducible`) and not prime (`two_not_prime`). -/
theorem not_ufd : ¬ UniqueFactorizationMonoid (ℤ√(-5)) := fun h =>
  two_not_prime (h.irreducible_iff_prime.mp two_irreducible)
-- @endregion

end Lumenary.Rings
