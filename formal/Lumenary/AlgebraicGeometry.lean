/-
The Lumenary — formal mathematics
Algebraic geometry: algebraic sets and the Zariski topology, the algebra–geometry dictionary,
the cusp and its normalisation, points of the projective plane over a finite field, and affine
schemes.

What is proved here. Independently: `V(IJ) = V(I) ∪ V(J)` (finite unions of algebraic sets are
algebraic); over an infinite field any two non-empty basic open subsets of the affine line meet,
which is why the Zariski topology is not Hausdorff; `Spec ℤ` is not Hausdorff; the
parametrisation `t ↦ (t², t³)` of the cusp is injective, but `t ∉ k[t², t³]`, so the cusp is not
isomorphic to the line; and `|ℙ²(𝔽_q)| = q² + q + 1`.

What Mathlib provides. Algebraic sets (`MvPolynomial.zeroLocus`) and vanishing ideals, the
Nullstellensatz (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`), the prime spectrum with
its Zariski topology (`PrimeSpectrum`), irreducible closed sets ↔ prime ideals
(`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`), projective spaces
(`Projectivization`), schemes (`AlgebraicGeometry.Scheme`), `Γ(Spec R) ≅ R`
(`AlgebraicGeometry.Scheme.ΓSpecIso`), sections over basic opens as localisations, and the
anti-equivalence of affine schemes with commutative rings
(`AlgebraicGeometry.AffineScheme.equivCommRingCat`). Not formalised here: Bézout's theorem
(Mathlib has neither intersection multiplicities of plane curves nor Bézout), and the classical
equivalence between affine varieties and reduced finitely generated algebras, which Mathlib
expresses through schemes instead.
-/
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.AlgebraicGeometry.AffineScheme

namespace Lumenary.AlgebraicGeometry

open Polynomial

/-! ### Algebraic sets and the Zariski topology -/

-- @region algebraic_geometry.zero_locus_mul
-- @provenance independent
/-- **Finite unions of algebraic sets are algebraic**: `V(IJ) = V(I) ∪ V(J)`. Human proof: if
`x` lies in `V(I)` (or `V(J)`), every element of `IJ ⊆ I` (or `⊆ J`) vanishes at `x`.
Conversely, if `x` lies in neither, choose `f ∈ I` and `g ∈ J` with `f(x) ≠ 0 ≠ g(x)`; then
`fg ∈ IJ` and `(fg)(x) = f(x) g(x) ≠ 0` because `K` is a field. Together with
`V(∑ Iᵢ) = ⋂ V(Iᵢ)`, this makes the algebraic sets the closed sets of a topology. -/
theorem zeroLocus_mul {σ k K : Type*} [Field k] [Field K] [Algebra k K]
    (I J : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus K (I * J) = MvPolynomial.zeroLocus K I ∪ MvPolynomial.zeroLocus K J := by
  ext x
  simp only [Set.mem_union, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro hx
    by_contra h
    simp only [not_or, not_forall] at h
    obtain ⟨⟨f, hfI, hf⟩, ⟨g, hgJ, hg⟩⟩ := h
    have hmem : f * g ∈ I * J := Ideal.mul_mem_mul hfI hgJ
    have hfg : MvPolynomial.aeval x (f * g) = 0 := hx (f * g) hmem
    rw [map_mul] at hfg
    exact mul_ne_zero hf hg hfg
  · rintro (hx | hx) p hp
    · have hpI : p ∈ I := Ideal.mul_le_left (I := I) (J := J) hp
      exact hx p hpI
    · have hpJ : p ∈ J := Ideal.mul_le_right (I := I) (J := J) hp
      exact hx p hpJ
-- @endregion

-- @region algebraic_geometry.basic_opens_meet
-- @provenance independent
/-- **The Zariski topology on the affine line is not Hausdorff.** Over an infinite field `k`,
the non-empty open sets of `𝔸¹` are complements of finite sets, and any two of them meet: for
non-zero polynomials `f, g` there is a point `a` with `f(a) ≠ 0` and `g(a) ≠ 0`. Proof: `fg ≠ 0`
has only finitely many roots, and `k` is infinite, so some `a` is not a root of `fg`. So two
distinct points never have disjoint neighbourhoods. -/
theorem basic_opens_meet {k : Type*} [Field k] [Infinite k] {f g : k[X]} (hf : f ≠ 0)
    (hg : g ≠ 0) : ∃ a : k, f.eval a ≠ 0 ∧ g.eval a ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (f * g).roots.toFinset
  refine ⟨a, ?_⟩
  have hfg : (f * g).eval a ≠ 0 := by
    intro h0
    apply ha
    rw [Multiset.mem_toFinset, mem_roots (mul_ne_zero hf hg)]
    exact h0
  rw [eval_mul] at hfg
  exact ⟨left_ne_zero_of_mul hfg, right_ne_zero_of_mul hfg⟩
-- @endregion

-- @region algebraic_geometry.spec_int_not_t2
-- @provenance independent
/-- **`Spec ℤ` is not Hausdorff** — it is not even T₁. Mathlib's
`PrimeSpectrum.t1Space_iff_isField` says that the spectrum of a domain is T₁ exactly when the
domain is a field (the generic point `(0)` is closed only in a field), and `ℤ` is not a field
(`Int.not_isField`). Every Hausdorff space is T₁, so `Spec ℤ` is not Hausdorff. -/
theorem spec_int_not_t2 : ¬ T2Space (PrimeSpectrum ℤ) := by
  intro h
  have h1 : T1Space (PrimeSpectrum ℤ) := inferInstance
  rw [PrimeSpectrum.t1Space_iff_isField] at h1
  exact Int.not_isField h1
-- @endregion

/-! ### The algebra–geometry dictionary -/

-- @region algebraic_geometry.prime_ideal_of_irreducible
-- @provenance library
/-- **Irreducible closed sets correspond to prime ideals.** In `Spec R`, a set `s` is irreducible
exactly when its vanishing ideal is prime. Mathlib:
`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. For `R = k[x₁, …, xₙ]` with `k`
algebraically closed, this is the statement "affine varieties ↔ prime ideals". -/
theorem prime_ideal_of_irreducible {R : Type*} [CommRing R] (s : Set (PrimeSpectrum R)) :
    IsIrreducible s ↔ (PrimeSpectrum.vanishingIdeal s).IsPrime :=
  PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime
-- @endregion

-- @region algebraic_geometry.vanishing_of_prime
-- @provenance library
/-- **Prime ideals are recovered from their varieties.** Over an algebraically closed field `K`,
a prime ideal `P` of `k[x₁, …, xₙ]` is the ideal of all polynomials vanishing on `V(P)`:
`I(V(P)) = P`. This is the Nullstellensatz for prime (hence radical) ideals. Mathlib:
`MvPolynomial.IsPrime.vanishingIdeal_zeroLocus`. -/
theorem vanishing_of_prime {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] :
    MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K P) = P :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P
-- @endregion

/-! ### The cusp `y² = x³` -/

-- @region algebraic_geometry.cusp_param_injective
-- @provenance independent
/-- **The cusp is in bijection with the line.** The morphism `𝔸¹ → C`, `t ↦ (t², t³)`, onto the
cusp `C : y² = x³` is injective: if `s² = t²` and `s³ = t³` then `s = t`. Proof: if `s = 0` then
`t² = 0`, so `t = 0`. Otherwise `t ≠ 0` too, and `s = s³/s² = t³/t² = t`. (It is also surjective
onto `C` over any field, with inverse `(x, y) ↦ y/x` away from the origin.) -/
theorem cusp_param_injective {k : Type*} [Field k] {s t : k} (h2 : s ^ 2 = t ^ 2)
    (h3 : s ^ 3 = t ^ 3) : s = t := by
  by_cases hs : s = 0
  · subst hs
    have ht : t ^ 2 = 0 := by rw [← h2]; ring
    exact (pow_eq_zero_iff two_ne_zero |>.mp ht).symm
  · have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    have ht2 : t ^ 2 ≠ 0 := h2 ▸ hs2
    calc s = s ^ 3 / s ^ 2 := by field_simp
      _ = t ^ 3 / t ^ 2 := by rw [h2, h3]
      _ = t := by field_simp
-- @endregion

-- @region algebraic_geometry.cusp_not_normal
-- @provenance independent
/-- **…but the cusp is not isomorphic to the line.** The coordinate ring of the cusp is the
subalgebra `k[t², t³] ⊆ k[t]`, and `t` does not lie in it. Proof: the polynomials whose
coefficient of `t` vanishes form a subalgebra (the `t`-coefficient of a product `pq` is
`p₀q₁ + p₁q₀`), which contains `t²` and `t³` but not `t`. So the bijective morphism
`t ↦ (t², t³)` is not an isomorphism: its comorphism `k[t², t³] → k[t]` is not surjective. -/
theorem cusp_not_normal (k : Type*) [Field k] :
    (X : k[X]) ∉ Algebra.adjoin k ({X ^ 2, X ^ 3} : Set k[X]) := by
  -- the subalgebra of polynomials with no linear term
  let S : Subalgebra k k[X] :=
    { carrier := {p | p.coeff 1 = 0}
      mul_mem' := by
        intro p q hp hq
        simp only [Set.mem_ofPred_eq] at hp hq ⊢
        rw [coeff_mul, Finset.Nat.antidiagonal_succ]
        simp [hp, hq]
      add_mem' := by
        intro p q hp hq
        simp only [Set.mem_ofPred_eq, coeff_add] at hp hq ⊢
        rw [hp, hq, add_zero]
      algebraMap_mem' := by
        intro c
        simp }
  have hle : Algebra.adjoin k ({X ^ 2, X ^ 3} : Set k[X]) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    intro p hp
    rcases hp with rfl | rfl
    · show (X ^ 2 : k[X]).coeff 1 = 0
      simp [coeff_X_pow]
    · show (X ^ 3 : k[X]).coeff 1 = 0
      simp [coeff_X_pow]
  intro hX
  have h1 : (X : k[X]).coeff 1 = 0 := hle hX
  simp at h1
-- @endregion

/-! ### Projective space -/

open scoped LinearAlgebra.Projectivization

-- @region algebraic_geometry.projective_plane_card
-- @provenance independent
/-- **Counting points of the projective plane over a finite field.** `ℙ²(𝔽_q)` — lines through
the origin in `𝔽_q³` — has `q² + q + 1` points: the `q² ` points of the affine plane plus the
`q + 1` points of the line at infinity. Derived from Mathlib's `Projectivization.card_of_finrank`
(`|ℙ(V)| = 1 + q + ⋯ + q^(n-1)` when `dim V = n`). -/
theorem projective_plane_card (k : Type*) [Field k] [Fintype k] :
    Nat.card (ℙ k (Fin 3 → k)) = Fintype.card k ^ 2 + Fintype.card k + 1 := by
  rw [Projectivization.card_of_finrank k (Fin 3 → k) (n := 3) (by simp)]
  simp [Finset.sum_range_succ, Nat.card_eq_fintype_card]
  ring
-- @endregion

-- @region algebraic_geometry.roots_on_a_line
-- @provenance library
/-- **The one-variable case of Bézout.** Over an algebraically closed field a polynomial of
degree `d` has exactly `d` roots counted with multiplicity. Restricting a plane curve of degree
`d` to a line gives such a polynomial (or a binary form of degree `d`, in homogeneous
coordinates), which is why a line meets a curve of degree `d` in exactly `d` points of `ℙ²`.
Mathlib: `IsAlgClosed.card_roots_eq_natDegree`. -/
theorem roots_on_a_line {k : Type*} [Field k] [IsAlgClosed k] (p : k[X]) :
    p.roots.card = p.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree
-- @endregion

/-! ### Affine schemes -/

open _root_.AlgebraicGeometry CategoryTheory
open scoped _root_.AlgebraicGeometry

-- @region algebraic_geometry.global_sections_spec
-- @provenance library
/-- **The global sections of `Spec R` are `R`.** The structure sheaf of the affine scheme
`Spec R` has `R` itself as its ring of global sections — the key theorem of affine schemes
(Hartshorne, Proposition II.2.2). Mathlib: `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
noncomputable def global_sections_spec (R : CommRingCat) : Γ(Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R
-- @endregion

-- @region algebraic_geometry.sections_basic_open
-- @provenance library
/-- **Sections over a basic open set are a localisation.** On an affine scheme `X`, the ring of
sections over `D(f) = {f ≠ 0}` is the localisation `Γ(X)_f = Γ(X)[1/f]`: "functions on the open
set where `f` does not vanish may have powers of `f` in the denominator". Mathlib:
`AlgebraicGeometry.isLocalization_away_of_isAffine`. -/
theorem sections_basic_open (X : Scheme) [IsAffine X] (f : Γ(X, ⊤)) :
    IsLocalization.Away f Γ(X, X.basicOpen f) :=
  inferInstance
-- @endregion

-- @region algebraic_geometry.affine_schemes_equiv_rings
-- @provenance library
/-- **Affine schemes are the opposite of commutative rings.** `Spec` and global sections `Γ` are
inverse equivalences `AffineScheme ≌ CommRingᵒᵖ`: morphisms of affine schemes `Spec S → Spec R`
are exactly ring homomorphisms `R → S`. This is the scheme version of "affine varieties are the
opposite of reduced finitely generated `k`-algebras". Mathlib:
`AlgebraicGeometry.AffineScheme.equivCommRingCat`. -/
noncomputable def affine_schemes_equiv_rings : AffineScheme ≌ CommRingCatᵒᵖ :=
  AffineScheme.equivCommRingCat
-- @endregion

end Lumenary.AlgebraicGeometry
