/-
The Lumenary — formal mathematics
Algebraic number theory: failure of unique factorisation in `ℤ[√−5]`, units of quadratic rings,
unique factorisation of ideals, the class group, Dirichlet's unit theorem and cyclotomic integers.

What is proved here. Independently, by norm arguments in `ℤ√d = ℤ[√d]` (Mathlib's `Zsqrtd`):
`ℤ[√−5]` is an integral domain; no element has norm `2`; `2` is irreducible but not prime, so
`ℤ[√−5]` is not a unique factorisation domain; the only units of `ℤ[√−5]` are `±1`; and
`1 + √2` is a unit of infinite order in `ℤ[√2]`, so that ring has infinitely many units.

What Mathlib provides. Number fields and their rings of integers `𝓞 K`, the fact that `𝓞 K` is a
Dedekind domain, unique factorisation of ideals in Dedekind domains
(`Ideal.uniqueFactorizationMonoid`), finiteness of the class group and the class number
(`NumberField.classNumber`), "class number one ⇔ PID", the Minkowski bound, Dirichlet's unit
theorem (`NumberField.Units.exist_unique_eq_mul_prod`, `NumberField.Units.rank`), rings of
integers and discriminants of cyclotomic fields, and Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq`). Mathlib also proves the Kummer–Dedekind theorem
(`KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map`), which we
use in the lesson only informally.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

namespace Lumenary.AlgebraicNumberTheory

open NumberField

/-! ### `ℤ[√−5]`: unique factorisation of elements fails -/

-- @region algebraic_number_theory.norm_sqrt_neg_five
-- @provenance independent
/-- **The norm on `ℤ[√−5]`.** `N(a + b√−5) = (a + b√−5)(a − b√−5) = a² + 5b²`. In Mathlib the norm
of `z : ℤ√d` is `z.re * z.re - d * z.im * z.im`, multiplicative by `Zsqrtd.norm_mul`. -/
theorem norm_sqrt_neg_five (z : ℤ√(-5)) : z.norm = z.re ^ 2 + 5 * z.im ^ 2 := by
  rw [Zsqrtd.norm_def]
  ring
-- @endregion

-- @region algebraic_number_theory.is_domain_sqrt_neg_five
-- @provenance definition
/-- **`ℤ[√−5]` is an integral domain.** If `xy = 0` then `N(x) N(y) = N(xy) = 0`, so `N(x) = 0` or
`N(y) = 0`; and `N(a + b√−5) = a² + 5b² = 0` forces `a = b = 0` (Mathlib: `Zsqrtd.norm_eq_zero`,
since `−5` is not a square). -/
instance isDomain_sqrt_neg_five : IsDomain (ℤ√(-5)) := by
  have hns : ∀ n : ℤ, (-5 : ℤ) ≠ n * n := fun n h => by nlinarith [mul_self_nonneg n]
  have : NoZeroDivisors (ℤ√(-5)) :=
    ⟨fun {x y} hxy => by
      have h := congrArg Zsqrtd.norm hxy
      rw [Zsqrtd.norm_mul, Zsqrtd.norm_zero, mul_eq_zero] at h
      rcases h with h | h
      · exact Or.inl ((Zsqrtd.norm_eq_zero hns x).mp h)
      · exact Or.inr ((Zsqrtd.norm_eq_zero hns y).mp h)⟩
  exact NoZeroDivisors.to_isDomain _
-- @endregion

-- @region algebraic_number_theory.norm_ne_two
-- @provenance independent
/-- **No element of `ℤ[√−5]` has norm `2`.** If `a² + 5b² = 2` then `b = 0` (otherwise the left
side is at least `5`), and `a² = 2` has no integer solution. -/
theorem norm_ne_two (z : ℤ√(-5)) : z.norm ≠ 2 := by
  rw [norm_sqrt_neg_five]
  intro h
  have hb : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  rw [hb] at h
  have ha : z.re ^ 2 = 2 := by linarith
  have h1 : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re - 2)]
  have h2 : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re + 2)]
  interval_cases z.re <;> norm_num at ha
-- @endregion

-- @region algebraic_number_theory.two_irreducible
-- @provenance independent
/-- **`2` is irreducible in `ℤ[√−5]`.** It is not a unit, since `N(2) = 4 ≠ 1`. If `2 = xy` then
`N(x) N(y) = 4` with both norms non-negative; `N(x) = 2` is impossible, so `N(x) = 1` or
`N(y) = 1`, and an element of norm `1` is a unit (Mathlib: `Zsqrtd.norm_eq_one_iff'`). -/
theorem two_irreducible : Irreducible (2 : ℤ√(-5)) := by
  have hd : (-5 : ℤ) ≤ 0 := by norm_num
  have hnorm2 : (2 : ℤ√(-5)).norm = 4 := by
    rw [norm_sqrt_neg_five]; simp
  refine ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff' hd 2).mpr hu
    rw [hnorm2] at this
    norm_num at this
  · have h := congrArg Zsqrtd.norm hxy
    rw [Zsqrtd.norm_mul, hnorm2] at h
    have hx0 := Zsqrtd.norm_nonneg hd x
    have hy0 := Zsqrtd.norm_nonneg hd y
    have hx2 := norm_ne_two x
    have hypos : 0 < y.norm := by
      rcases hy0.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at h; norm_num at h
    have hxle : x.norm ≤ 4 := by nlinarith
    have hxpos : 0 < x.norm := by
      rcases hx0.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at h; norm_num at h
    interval_cases hn : x.norm
    · exact Or.inl ((Zsqrtd.norm_eq_one_iff' hd x).mp hn)
    · exact absurd rfl hx2
    · omega
    · right
      exact (Zsqrtd.norm_eq_one_iff' hd y).mp (by omega)
-- @endregion

-- @region algebraic_number_theory.two_not_prime
-- @provenance independent
/-- **…but `2` is not prime in `ℤ[√−5]`.** `2` divides `(1 + √−5)(1 − √−5) = 6 = 2 · 3`, yet it
divides neither factor: `1 ± √−5 = 2(a + b√−5)` would give `1 = 2a`. -/
theorem two_not_prime : ¬ Prime (2 : ℤ√(-5)) := by
  intro hp
  have hdvd : (2 : ℤ√(-5)) ∣ ⟨1, 1⟩ * ⟨1, -1⟩ :=
    ⟨3, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  rcases hp.dvd_or_dvd hdvd with ⟨c, hc⟩ | ⟨c, hc⟩
  · have := congrArg Zsqrtd.re hc
    simp [Zsqrtd.re_mul] at this
    omega
  · have := congrArg Zsqrtd.re hc
    simp [Zsqrtd.re_mul] at this
    omega
-- @endregion

-- @region algebraic_number_theory.not_ufd
-- @provenance independent
/-- **`ℤ[√−5]` is not a unique factorisation domain.** In a UFD every irreducible element is
prime, but `2` is irreducible and not prime. Concretely, `6 = 2 · 3 = (1 + √−5)(1 − √−5)` are
two factorisations into irreducibles that do not match up to units. (The *ideals* still factor
uniquely: `(6) = 𝔭₂² 𝔭₃ 𝔭₃'` — see the lesson.) -/
theorem not_ufd : ¬ UniqueFactorizationMonoid (ℤ√(-5)) := by
  intro h
  exact two_not_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp two_irreducible)
-- @endregion

/-! ### Units of quadratic rings -/

-- @region algebraic_number_theory.units_sqrt_neg_five
-- @provenance independent
/-- **The units of `ℤ[√−5]` are `±1`** — the imaginary quadratic case of Dirichlet's unit theorem
(rank `r₁ + r₂ − 1 = 0 + 1 − 1 = 0`). A unit has norm `1`, and `a² + 5b² = 1` forces `b = 0` and
`a = ±1`. -/
theorem units_sqrt_neg_five (z : ℤ√(-5)) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  have hd : (-5 : ℤ) ≤ 0 := by norm_num
  constructor
  · intro hu
    have h := (Zsqrtd.norm_eq_one_iff' hd z).mpr hu
    rw [norm_sqrt_neg_five] at h
    have hb : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    rw [hb] at h
    have ha : z.re ^ 2 = 1 := by linarith
    have h1 : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re - 1)]
    have h2 : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re + 1)]
    interval_cases hre : z.re
    · right; ext <;> simp [hre, hb]
    · norm_num at ha
    · left; ext <;> simp [hre, hb]
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg
-- @endregion

-- @region algebraic_number_theory.one_add_sqrt_two_unit
-- @provenance independent
/-- **`1 + √2` is a unit of `ℤ[√2]`**: `(1 + √2)(−1 + √2) = 2 − 1 = 1`. Units of `ℤ[√2]` are the
elements of norm `a² − 2b² = ±1`, i.e. solutions of Pell-type equations. -/
theorem one_add_sqrt_two_unit : IsUnit (⟨1, 1⟩ : ℤ√2) :=
  IsUnit.of_mul_eq_one ⟨-1, 1⟩ (by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul])
-- @endregion

-- @region algebraic_number_theory.one_add_sqrt_two_infinite_order
-- @provenance independent
/-- **`1 + √2` has infinite order**, so `ℤ[√2]` has infinitely many units — the real quadratic
case of Dirichlet's unit theorem (rank `r₁ + r₂ − 1 = 2 + 0 − 1 = 1`). Proof: multiplying
`a + b√2` by `1 + √2` gives `(a + 2b) + (a + b)√2`, so by induction every power
`(1 + √2)ⁿ⁺¹` has both coordinates at least `1`; but `1 = 1 + 0√2`. -/
theorem one_add_sqrt_two_infinite_order (n : ℕ) : (⟨1, 1⟩ : ℤ√2) ^ (n + 1) ≠ 1 := by
  have key : ∀ m : ℕ, 1 ≤ ((⟨1, 1⟩ : ℤ√2) ^ (m + 1)).re ∧ 1 ≤ ((⟨1, 1⟩ : ℤ√2) ^ (m + 1)).im := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
      obtain ⟨h1, h2⟩ := ih
      constructor <;> simp <;> omega
  intro h
  have := (key n).2
  rw [h] at this
  simp at this
-- @endregion

/-! ### Number fields: what Mathlib proves -/

-- @region algebraic_number_theory.ring_of_integers_dedekind
-- @provenance library
/-- **The ring of integers of a number field is a Dedekind domain**: Noetherian, integrally closed
and of dimension one. Mathlib: an instance in `Mathlib.NumberTheory.NumberField.Basic`, proved
from the fact that `𝓞 K` is the integral closure of the Dedekind domain `ℤ` in `K`. -/
theorem ring_of_integers_dedekind (K : Type*) [Field K] [NumberField K] :
    IsDedekindDomain (𝓞 K) :=
  inferInstance
-- @endregion

-- @region algebraic_number_theory.ideals_factor_uniquely
-- @provenance library
/-- **Unique factorisation of ideals.** In a Dedekind domain the non-zero ideals form a unique
factorisation monoid: every non-zero ideal is a product of prime ideals, uniquely up to order.
Mathlib: `Ideal.uniqueFactorizationMonoid`. -/
theorem ideals_factor_uniquely (K : Type*) [Field K] [NumberField K] :
    UniqueFactorizationMonoid (Ideal (𝓞 K)) :=
  inferInstance
-- @endregion

-- @region algebraic_number_theory.class_group_finite
-- @provenance library
/-- **The class group of a number field is finite.** Mathlib proves it by showing that every
ideal class contains an ideal of bounded norm (`ClassGroup.fintypeOfAdmissibleOfFinite`); the
lesson's proof uses the Minkowski bound instead (Mathlib:
`NumberField.exists_ideal_in_class_of_norm_le`). -/
theorem class_group_finite (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) :=
  inferInstance
-- @endregion

-- @region algebraic_number_theory.class_number_one_iff
-- @provenance library
/-- **Class number one ⇔ principal ideal domain** (and, for Dedekind domains, ⇔ unique
factorisation domain, as proved in the lesson). Mathlib: `NumberField.classNumber_eq_one_iff`. -/
theorem class_number_one_iff (K : Type*) [Field K] [NumberField K] :
    classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  classNumber_eq_one_iff
-- @endregion

-- @region algebraic_number_theory.dirichlet_unit_theorem
-- @provenance library
/-- **Dirichlet's unit theorem.** There are units `ε₁, …, ε_r` (a fundamental system) such that
every unit of `𝓞 K` is uniquely `ζ ε₁^{n₁} ⋯ ε_r^{n_r}` with `ζ` a root of unity and `nᵢ ∈ ℤ`;
here `r = r₁ + r₂ − 1` is one less than the number of infinite places. Mathlib:
`NumberField.Units.exist_unique_eq_mul_prod`. -/
theorem dirichlet_unit_theorem (K : Type*) [Field K] [NumberField K] (x : (𝓞 K)ˣ) :
    ∃! ζe : Units.torsion K × (Fin (Units.rank K) → ℤ),
      x = ζe.1 * ∏ i, (Units.fundSystem K i) ^ (ζe.2 i) :=
  Units.exist_unique_eq_mul_prod K x
-- @endregion

-- @region algebraic_number_theory.unit_rank
-- @provenance library
/-- **The rank of the unit group is `r₁ + r₂ − 1`.** Mathlib defines `Units.rank K` as the number of
infinite places minus one, and counts the infinite places as `r₁ + r₂`
(`InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces`). -/
theorem unit_rank (K : Type*) [Field K] [NumberField K] :
    Units.rank K = InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 := by
  rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
-- @endregion

-- @region algebraic_number_theory.cyclotomic_integers
-- @provenance library
/-- **The ring of integers of `ℚ(ζ_p)` is `ℤ[ζ_p]`.** For a prime `p` and a primitive `p`-th root of
unity `ζ`, the integral closure of `ℤ` in `ℚ(ζ)` is generated by `ζ`. Mathlib:
`IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime` (proved via the
Eisenstein criterion for the minimal polynomial of `ζ − 1`). -/
theorem cyclotomic_integers {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K :=
  IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime hζ
-- @endregion

-- @region algebraic_number_theory.sum_of_two_squares
-- @provenance library
/-- **Fermat's two-squares theorem**: a prime `p` with `p mod 4 ≠ 3` is a sum of two squares.
In the lesson's language: such a `p` splits in `ℤ[i]` as `(a + bi)(a − bi)`. Mathlib:
`Nat.Prime.sq_add_sq` (proved via the Gaussian integers, a Euclidean domain). -/
theorem sum_of_two_squares {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hp
-- @endregion

end Lumenary.AlgebraicNumberTheory
