/-
The Lumenary — formal mathematics
Quotient groups and quotient rings: why normal subgroups and ideals are exactly what is needed,
the universal property, the isomorphism theorems, ℤ/nℤ, the Chinese remainder theorem, and
fields built as quotients.

What is proved here and what Mathlib provides. Proved independently: multiplication of cosets is
well defined when the subgroup is normal, and *only* then; multiplication of residues modulo an
additive subgroup is well defined exactly when it is an ideal; the universal property of `G ⧸ N`
(from Mathlib's `lift`); quotients of abelian groups are abelian; `ℤ/nℤ` is a field exactly when
`n` is prime; and `X² + X + 1` is irreducible over `𝔽₂`, so `𝔽₂[X]/(X² + X + 1)` is a field with
four elements' worth of structure (`𝔽₄`). Cited from Mathlib: the kernel of the quotient map, the
three isomorphism theorems, the first isomorphism theorem for rings, `ℤ/(n) ≅ ZMod n`, the Chinese
remainder theorem, and "R/I is a field iff I is maximal, a domain iff I is prime".
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

namespace Lumenary.Quotients

open Polynomial

/-! ### Quotient groups -/

-- @region quotients.coset_mul_well_defined
-- @provenance independent
/-- **Coset multiplication is well defined when `N` is normal.** If `aN = a'N` and `bN = b'N`
(that is, `a⁻¹a' ∈ N` and `b⁻¹b' ∈ N`), then `abN = a'b'N`:
`(ab)⁻¹(a'b') = (b⁻¹ (a⁻¹a') b) (b⁻¹b')`, a conjugate of an element of `N` times an element
of `N`. -/
theorem coset_mul_well_defined {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    {a a' b b' : G} (ha : a⁻¹ * a' ∈ N) (hb : b⁻¹ * b' ∈ N) : (a * b)⁻¹ * (a' * b') ∈ N := by
  have hconj : b⁻¹ * (a⁻¹ * a') * b ∈ N := by
    simpa using hN.conj_mem _ ha b⁻¹
  have key : (a * b)⁻¹ * (a' * b') = (b⁻¹ * (a⁻¹ * a') * b) * (b⁻¹ * b') := by group
  rw [key]
  exact N.mul_mem hconj hb
-- @endregion

-- @region quotients.normal_of_coset_mul_well_defined
-- @provenance independent
/-- **Conversely, if coset multiplication is well defined, the subgroup is normal.** Given
`n ∈ H` and `g`, compare the products `1 · g⁻¹` and `n · g⁻¹`: since `1H = nH`, well-definedness
gives `g⁻¹H = ng⁻¹H`, i.e. `(g⁻¹)⁻¹ (n g⁻¹) = g n g⁻¹ ∈ H`. -/
theorem normal_of_coset_mul_well_defined {G : Type*} [Group G] (H : Subgroup G)
    (h : ∀ a a' b b' : G, a⁻¹ * a' ∈ H → b⁻¹ * b' ∈ H → (a * b)⁻¹ * (a' * b') ∈ H) :
    H.Normal where
  conj_mem n hn g := by
    have := h 1 n g⁻¹ g⁻¹ (by simpa using hn) (by simp)
    simpa [mul_assoc] using this
-- @endregion

-- @region quotients.ker_mk
-- @provenance library
/-- The kernel of the quotient map `G → G ⧸ N` is exactly `N` — so every normal subgroup is a
kernel. This is Mathlib's `QuotientGroup.ker_mk'`. -/
theorem ker_mk {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N :=
  QuotientGroup.ker_mk' N
-- @endregion

-- @region quotients.universal_property
-- @provenance independent
/-- **Universal property of the quotient.** A homomorphism `φ : G → H` with `N ⊆ ker φ` factors
through the quotient map by exactly one homomorphism `ψ : G ⧸ N → H`, namely `ψ(gN) = φ(g)`.
Existence is Mathlib's `QuotientGroup.lift`; uniqueness holds because every element of `G ⧸ N`
is some `gN` (`QuotientGroup.monoidHom_ext`). -/
theorem universal_property {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal]
    (φ : G →* H) (hN : N ≤ φ.ker) :
    ∃! ψ : G ⧸ N →* H, ψ.comp (QuotientGroup.mk' N) = φ := by
  refine ⟨QuotientGroup.lift N φ hN, ?_, ?_⟩
  · ext g
    simp
  · intro ψ hψ
    apply QuotientGroup.monoidHom_ext
    rw [hψ]
    ext g
    simp
-- @endregion

-- @region quotients.first_iso
-- @provenance library
/-- **First isomorphism theorem**: `G ⧸ ker φ ≅ im φ`. This applies Mathlib's
`QuotientGroup.quotientKerEquivRange`, built (as in the lesson) from the universal property and
the fact that the induced map has trivial kernel. -/
theorem first_iso {G H : Type*} [Group G] [Group H] (φ : G →* H) :
    Nonempty (G ⧸ φ.ker ≃* φ.range) :=
  ⟨QuotientGroup.quotientKerEquivRange φ⟩
-- @endregion

-- @region quotients.second_iso
-- @provenance library
/-- **Second isomorphism theorem**: for `H ≤ G` and `N` normal, `H/(H ∩ N) ≅ HN/N`. Mathlib
writes `H ∩ N` as `N.subgroupOf H` (viewed inside `H`) and `HN` as `H ⊔ N`. This is
`QuotientGroup.quotientInfEquivProdNormalQuotient`. -/
theorem second_iso {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    Nonempty (H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N)) :=
  ⟨QuotientGroup.quotientInfEquivProdNormalQuotient H N⟩
-- @endregion

-- @region quotients.third_iso
-- @provenance library
/-- **Third isomorphism theorem**: for normal `N ≤ M`, `(G/N)/(M/N) ≅ G/M`. Here `M/N` is the
image of `M` under the quotient map. This is `QuotientGroup.quotientQuotientEquivQuotient`. -/
theorem third_iso {G : Type*} [Group G] (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M) :=
  ⟨QuotientGroup.quotientQuotientEquivQuotient N M h⟩
-- @endregion

-- @region quotients.quotient_comm
-- @provenance independent
/-- A quotient of an abelian group is abelian: `(aN)(bN) = abN = baN = (bN)(aN)`. (The converse
fails: `S₃/A₃` is abelian although `S₃` is not.) -/
theorem quotient_comm {G : Type*} [CommGroup G] (N : Subgroup G) (x y : G ⧸ N) :
    x * y = y * x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    induction y using QuotientGroup.induction_on with
    | H b => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm]
-- @endregion

/-! ### Quotient rings -/

-- @region quotients.ideal_mul_well_defined
-- @provenance independent
/-- **Multiplication of residues is well defined modulo an ideal.** If `a ≡ a'` and `b ≡ b'`
modulo `I`, then `ab - a'b' = a(b - b') + (a - a')b' ∈ I`. -/
theorem ideal_mul_well_defined {R : Type*} [CommRing R] (I : Ideal R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) : a * b - a' * b' ∈ I := by
  have key : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [key]
  exact I.add_mem (I.mul_mem_left a hb) (I.mul_mem_right b' ha)
-- @endregion

-- @region quotients.ideal_of_mul_well_defined
-- @provenance independent
/-- **Conversely, only ideals work.** If `I` is an additive subgroup for which multiplication of
residues is well defined, then `I` absorbs multiplication: for `x ∈ I`, compare `r · x` with
`r · 0` (since `x ≡ 0`), giving `r * x - r * 0 = r * x ∈ I`. -/
theorem ideal_of_mul_well_defined {R : Type*} [CommRing R] (I : AddSubgroup R)
    (h : ∀ a a' b b' : R, a - a' ∈ I → b - b' ∈ I → a * b - a' * b' ∈ I)
    (r x : R) (hx : x ∈ I) : r * x ∈ I := by
  have := h r r x 0 (by simp) (by simpa using hx)
  simpa using this
-- @endregion

-- @region quotients.ring_first_iso
-- @provenance library
/-- **First isomorphism theorem for rings**: `R ⧸ ker f ≅ im f`. Mathlib's
`RingHom.quotientKerEquivRange`. -/
theorem ring_first_iso {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Nonempty (R ⧸ RingHom.ker f ≃+* f.range) :=
  ⟨RingHom.quotientKerEquivRange f⟩
-- @endregion

-- @region quotients.int_quotient_zmod
-- @provenance library
/-- `ℤ ⧸ (n)` is the ring `ZMod n` of residues modulo `n` — by the first isomorphism theorem for
the reduction map `ℤ → ZMod n`, whose kernel is `(n)`. Mathlib's `Int.quotientSpanEquivZMod`. -/
theorem int_quotient_zmod (n : ℕ) : Nonempty (ℤ ⧸ Ideal.span {(n : ℤ)} ≃+* ZMod n) :=
  ⟨Int.quotientSpanEquivZMod n⟩
-- @endregion

-- @region quotients.crt
-- @provenance library
/-- **Chinese remainder theorem**: for coprime `m` and `n`, `ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ` as rings.
Mathlib's `ZMod.chineseRemainder`, proved from the first isomorphism theorem for
`x ↦ (x mod m, x mod n)`. -/
theorem crt {m n : ℕ} (h : m.Coprime n) : Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩
-- @endregion

-- @region quotients.maximal_iff_field
-- @provenance library
/-- For a commutative ring `R`, `R ⧸ I` is a field exactly when `I` is a maximal ideal.
Mathlib's `Ideal.Quotient.maximal_ideal_iff_isField_quotient`. -/
theorem maximal_iff_field {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) :=
  Ideal.Quotient.maximal_ideal_iff_isField_quotient I
-- @endregion

-- @region quotients.prime_iff_domain
-- @provenance library
/-- `R ⧸ I` is an integral domain exactly when `I` is a prime ideal.
Mathlib's `Ideal.Quotient.isDomain_iff_prime`. -/
theorem prime_iff_domain {R : Type*} [CommRing R] (I : Ideal R) :
    IsDomain (R ⧸ I) ↔ I.IsPrime :=
  Ideal.Quotient.isDomain_iff_prime I
-- @endregion

-- @region quotients.zmod_is_field_iff
-- @provenance independent
/-- `ℤ/nℤ` (for `n > 1`) is a field exactly when `n` is prime. If `n` is prime, Mathlib's field
structure on `ZMod n` applies. If `n = m * k` with `1 < m, k < n`, then `m · k = 0` in `ZMod n`
with `m ≠ 0`; an inverse `b` of `m` would give `k = b · (m · k) = 0`, but `0 < k < n`. -/
theorem zmod_isField_iff (n : ℕ) (hn : 1 < n) : IsField (ZMod n) ↔ n.Prime := by
  constructor
  · intro hF
    by_contra hp
    obtain ⟨m, hmn, hm1, hmn'⟩ : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
      by_contra hcon
      simp only [not_exists, not_and, ne_eq, not_not] at hcon
      exact hp (Nat.prime_def.mpr ⟨hn, fun m hm => by
        by_cases h1 : m = 1
        · exact Or.inl h1
        · exact Or.inr (hcon m hm h1)⟩)
    obtain ⟨k, rfl⟩ := hmn
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmlt : m < m * k := by
      rcases Nat.lt_or_ge 1 k with h | h
      · exact lt_mul_of_one_lt_right hm0 h
      · exact absurd (by nlinarith : k = 1) (by rintro rfl; simp at hmn')
    have hklt : k < m * k := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact lt_mul_of_one_lt_left hk0 h
      · omega
    have hmz : (m : ZMod (m * k)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => absurd (Nat.le_of_dvd hm0 hd) (by omega)
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hmz
    have hk : (k : ZMod (m * k)) = 0 := by
      calc (k : ZMod (m * k)) = (m * b) * k := by rw [hb, one_mul]
        _ = b * ((m * k : ℕ) : ZMod (m * k)) := by push_cast; ring
        _ = 0 := by rw [ZMod.natCast_self, mul_zero]
    rw [ZMod.natCast_eq_zero_iff] at hk
    exact absurd (Nat.le_of_dvd hk0 hk) (by omega)
  · intro hp
    have := Fact.mk hp
    exact Field.toIsField (ZMod n)
-- @endregion

-- @region quotients.zmod_four_not_domain
-- @provenance independent
/-- `ℤ/4ℤ` is not a field — not even a domain: `2 · 2 = 0`. (Compare `𝔽₄` below, the field with
four elements, which is a different ring.) -/
theorem zmod_four_not_domain : (2 : ZMod 4) * 2 = 0 ∧ (2 : ZMod 4) ≠ 0 := by
  decide
-- @endregion

-- @region quotients.f4_irreducible
-- @provenance independent
/-- `X² + X + 1` is irreducible over `𝔽₂ = ZMod 2`: it has degree 2 and no root, since its
values at `0` and `1` are `1` and `3 = 1`. (Mathlib's
`Polynomial.irreducible_of_degree_le_three_of_not_isRoot` turns "no root" into irreducibility for
degrees 2 and 3.) -/
theorem f4_irreducible : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    rw [this]
    decide
  · intro x hx
    rw [IsRoot.def, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
    revert hx
    fin_cases x <;> decide
-- @endregion

-- @region quotients.f4
-- @provenance definition
/-- The field with four elements, built as the quotient `𝔽₂[X] ⧸ (X² + X + 1)`
(`AdjoinRoot f` is Mathlib's name for `K[X] ⧸ (f)`). -/
abbrev F4 : Type := AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])
-- @endregion

-- @region quotients.f4_fact
-- @provenance definition
/-- Record the irreducibility proof as an instance, so that Lean can find the field structure
`AdjoinRoot.instField` on `F4`. -/
instance f4_fact : Fact (Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X])) :=
  ⟨f4_irreducible⟩
-- @endregion

-- @region quotients.f4_is_field
-- @provenance library
/-- `F4` is a field: the ideal generated by an irreducible polynomial over a field is maximal
(`AdjoinRoot.span_maximal_of_irreducible`), so the quotient is a field. -/
theorem f4_isField : IsField F4 :=
  Field.toIsField F4
-- @endregion

end Lumenary.Quotients
