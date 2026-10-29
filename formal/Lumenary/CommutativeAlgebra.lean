/-
The Lumenary — formal mathematics
Commutative algebra: prime and maximal ideals, Noetherian rings and Hilbert's basis theorem,
Nakayama's lemma, localisation, the Nullstellensatz and Krull dimension.

What is proved here. Independently: the zero ideal of `ℤ` is prime but not maximal; the
polynomial ring in infinitely many variables `k[x₀, x₁, …]` is not Noetherian (the chain
`(x₀) ⊂ (x₀, x₁) ⊂ ⋯` never stabilises); Nakayama's lemma, from the "determinant trick"; and the
ideal `(x²)` of `k[x]` is not radical (`x² ∈ (x²)` but `x ∉ (x²)`).

What Mathlib provides. Ideals, `Ideal.IsPrime`, `Ideal.IsMaximal`, `PrimeSpectrum`, localisation
(`IsLocalization`, `Localization.AtPrime`), Hilbert's basis theorem
(`Polynomial.isNoetherianRing`, and `MvPolynomial.isNoetherianRing` for finitely many variables),
Nakayama's lemma (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) and the determinant trick
(`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`), the correspondence between
primes of a localisation and primes of the ring (`IsLocalization.orderIsoOfPrime`), Hilbert's
Nullstellensatz (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`) and
`dim k[x₁, …, xₙ] = n` (`MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`). Not formalised
here: primary decomposition, going-up and Noether normalisation (Mathlib has them as
`Submodule.isLasker`, `Ideal.exists_ideal_over_prime_of_isIntegral` and
`exists_finite_inj_algHom_of_fg`).
-/
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div

namespace Lumenary.CommutativeAlgebra

open Ideal

/-! ### Prime and maximal ideals -/

-- @region commutative_algebra.zero_prime_not_maximal
-- @provenance independent
/-- **A prime ideal need not be maximal.** In `ℤ` the zero ideal is prime (because `ℤ` is an
integral domain: `ab = 0` forces `a = 0` or `b = 0`), but it is not maximal, since
`(0) ⊊ (2) ⊊ ℤ`. In a PID every *non-zero* prime ideal is maximal, so `(0)` is the only
exception in `ℤ`. -/
theorem zero_prime_not_maximal : (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal := by
  refine ⟨Ideal.isPrime_bot, fun hmax => ?_⟩
  -- `(2)` lies strictly between `(0)` and `ℤ`
  have h2 : (⊥ : Ideal ℤ) < Ideal.span {2} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have htop : Ideal.span {(2 : ℤ)} = ⊤ := hmax.1.2 _ h2
  rw [Ideal.span_singleton_eq_top] at htop
  exact absurd (Int.isUnit_iff.mp htop) (by norm_num)
-- @endregion

-- @region commutative_algebra.maximal_is_prime
-- @provenance library
/-- **Every maximal ideal is prime** (because `R/𝔪` is a field, hence a domain).
Mathlib: `Ideal.IsMaximal.isPrime`. -/
theorem maximal_is_prime {R : Type*} [CommRing R] {m : Ideal R} (hm : m.IsMaximal) : m.IsPrime :=
  hm.isPrime
-- @endregion

/-! ### Noetherian rings -/

-- @region commutative_algebra.hilbert_basis
-- @provenance library
/-- **Hilbert's basis theorem**: if `R` is Noetherian, so is `R[X]`. Mathlib:
`Polynomial.isNoetherianRing`, proved via ideals of leading coefficients, as in the lesson. -/
theorem hilbert_basis (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (Polynomial R) :=
  Polynomial.isNoetherianRing
-- @endregion

-- @region commutative_algebra.hilbert_basis_mv
-- @provenance library
/-- **Corollary**: `k[x₁, …, xₙ]` (more generally `R[x₁, …, xₙ]` for Noetherian `R`) is
Noetherian, by induction on `n`. Mathlib: `MvPolynomial.isNoetherianRing`. -/
theorem hilbert_basis_mv (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin n) R) :=
  inferInstance
-- @endregion

-- @region commutative_algebra.infinitely_many_variables_not_noetherian
-- @provenance independent
/-- **`k[x₀, x₁, x₂, …]` is not Noetherian.** Human proof: let `Iₙ = (x₀, …, xₙ₋₁)`. The chain
`I₀ ⊆ I₁ ⊆ ⋯` is increasing; if it stabilised at `n`, then `xₙ ∈ Iₙ₊₁ = Iₙ`. But the evaluation
homomorphism sending `xᵢ ↦ 0` for `i < n` and `xᵢ ↦ 1` otherwise kills `Iₙ` and sends `xₙ ↦ 1`. -/
theorem infinitely_many_variables_not_noetherian (k : Type*) [Field k] :
    ¬ IsNoetherianRing (MvPolynomial ℕ k) := by
  intro hnoeth
  let I : ℕ →o Ideal (MvPolynomial ℕ k) :=
    ⟨fun n => Ideal.span (MvPolynomial.X '' {i | i < n}), fun a b hab =>
      Ideal.span_mono (Set.image_mono fun i (hi : i < a) => lt_of_lt_of_le hi hab)⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian).mpr hnoeth I
  -- evaluation killing the first `n` variables
  let φ : MvPolynomial ℕ k →+* k := MvPolynomial.eval fun i => if i < n then 0 else 1
  have hker : I n ≤ RingHom.ker φ := by
    show Ideal.span _ ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, φ, MvPolynomial.eval_X]
    exact (ite_eq_left_iff.mpr fun h => absurd hi h)
  have hmem : (MvPolynomial.X n : MvPolynomial ℕ k) ∈ I n := by
    rw [hn (n + 1) (Nat.le_succ n)]
    exact Ideal.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  have h1 : φ (MvPolynomial.X n) = 0 := hker hmem
  simp [φ] at h1
-- @endregion

/-! ### Nakayama's lemma -/

-- @region commutative_algebra.nakayama
-- @provenance independent
/-- **Nakayama's lemma.** Let `N` be a finitely generated module and `I` an ideal contained in
the Jacobson radical. If `N ⊆ I N` then `N = 0`. Human proof: the determinant trick
(Cayley–Hamilton applied to a matrix expressing the generators in terms of themselves with
coefficients in `I`) gives `r ∈ R` with `r - 1 ∈ I` and `r N = 0`. Since `r - 1` lies in the
Jacobson radical, `r = 1 + (r - 1)` is a unit, so `N = r⁻¹ r N = 0`. (Mathlib's version is
`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`.) -/
theorem nakayama {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (N : Submodule R M) (hN : N.FG) (hIN : N ≤ I • N) (hjac : I ≤ Ideal.jacobson ⊥) :
    N = ⊥ := by
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN
  -- `r = 1 + (r - 1)` is a unit, because `r - 1` lies in the Jacobson radical
  have hunit : IsUnit r := by
    have h := (Ideal.mem_jacobson_bot.mp (hjac hr)) 1
    simpa using h
  rw [eq_bot_iff]
  intro n hn
  have h0 : r • n = 0 := hrN n hn
  rw [Submodule.mem_bot]
  calc n = (1 : R) • n := (one_smul R n).symm
    _ = ((hunit.unit⁻¹ : Rˣ) * r : R) • n := by rw [hunit.val_inv_mul]
    _ = (hunit.unit⁻¹ : Rˣ) • (r • n) := mul_smul _ _ _
    _ = 0 := by rw [h0, smul_zero]
-- @endregion

-- @region commutative_algebra.nakayama_library
-- @provenance library
/-- **Nakayama's lemma, Mathlib's version** (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`). For a
local ring, `I = 𝔪` lies in the Jacobson radical, giving the familiar form: if `M` is finitely
generated and `𝔪 M = M` then `M = 0`. -/
theorem nakayama_library {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (N : Submodule R M) (hN : N.FG) (hIN : N ≤ I • N) (hjac : I ≤ Ideal.jacobson ⊥) :
    N = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I N hN hIN hjac
-- @endregion

/-! ### Localisation -/

-- @region commutative_algebra.localization_primes
-- @provenance library
/-- **Primes of a localisation.** If `S` is the localisation of `R` at the complement of a prime
`𝔭`, the prime ideals of `S` correspond, preserving inclusion, to the prime ideals of `R`
contained in `𝔭`. Mathlib: `IsLocalization.AtPrime.orderIsoOfPrime`. In particular `R_𝔭` has a
unique maximal ideal: it is local. -/
noncomputable def localization_primes {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] :
    { q : Ideal S // q.IsPrime } ≃o { q : Ideal R // q.IsPrime ∧ q ≤ p } :=
  IsLocalization.AtPrime.orderIsoOfPrime S p
-- @endregion

-- @region commutative_algebra.localization_local
-- @provenance library
/-- **`R_𝔭` is a local ring.** Mathlib: the instance `Localization.AtPrime.isLocalRing`. -/
theorem localization_local {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) :=
  inferInstance
-- @endregion

/-! ### The Nullstellensatz and dimension -/

-- @region commutative_algebra.x_sq_not_radical
-- @provenance independent
/-- **`(x²)` is not a radical ideal of `k[x]`.** Its zero set is the single point `0`, whose
vanishing ideal is `(x)`; and indeed `x ∉ (x²)` although `x² ∈ (x²)`. So the Nullstellensatz
must return the radical `√I`, not `I`. Proof: `x² ∣ x` would force the coefficient of `x` in
`x` to vanish. -/
theorem x_sq_not_radical (k : Type*) [Field k] :
    (Polynomial.X : Polynomial k) ^ 2 ∈ Ideal.span {Polynomial.X ^ 2} ∧
      (Polynomial.X : Polynomial k) ∉ Ideal.span {Polynomial.X ^ 2} := by
  refine ⟨Ideal.subset_span rfl, fun h => ?_⟩
  rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at h
  have := h 1 (by norm_num)
  simp at this
-- @endregion

-- @region commutative_algebra.nullstellensatz
-- @provenance library
/-- **Hilbert's Nullstellensatz** (strong form): over an algebraically closed field `k`, a
polynomial vanishes on the zero set of an ideal `I ⊆ k[x₁, …, xₙ]` exactly when some power of it
lies in `I`: `I(V(I)) = √I`. Mathlib: `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`. -/
theorem nullstellensatz {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I
-- @endregion

-- @region commutative_algebra.maximal_ideals_are_points
-- @provenance library
/-- **Weak Nullstellensatz**: over an algebraically closed field, the maximal ideals of
`k[x₁, …, xₙ]` are exactly the ideals `𝔪ₐ = {f : f(a) = 0}` of points `a ∈ kⁿ`. Mathlib:
`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`. -/
theorem maximal_ideals_are_points {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) :
    I.IsMaximal ↔ ∃ a : Fin n → k, I = MvPolynomial.vanishingIdeal k {a} :=
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton
-- @endregion

-- @region commutative_algebra.krull_dim_polynomial
-- @provenance library
/-- **`dim k[x₁, …, xₙ] = n`.** The chain `0 ⊂ (x₁) ⊂ (x₁, x₂) ⊂ ⋯ ⊂ (x₁, …, xₙ)` shows `≥ n`; the
reverse inequality is the hard part. Mathlib: `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`
(`dim R[x₁, …, xₙ] = dim R + n` for Noetherian `R`) and `ringKrullDim_eq_zero_of_field`. -/
theorem krull_dim_polynomial (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
-- @endregion

end Lumenary.CommutativeAlgebra
