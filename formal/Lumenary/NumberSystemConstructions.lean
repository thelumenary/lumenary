/-
The Lumenary — formal mathematics
Constructing ℤ, ℚ and ℝ: integers as classes of pairs of naturals, fractions as classes of
pairs, and real numbers as Dedekind cuts, with the least-upper-bound property.

Mathlib builds its own number systems differently: `Int` is an inductive type (`ofNat n` and
`negSucc n`), `ℚ` is a structure of reduced fractions, and `ℝ` is the completion of `ℚ` by
Cauchy sequences. Below, the lesson's constructions are carried out by hand: the relation on
`ℕ × ℕ` is an equivalence, addition and multiplication of classes are well defined, and the
quotient is in bijection with Mathlib's `ℤ`, preserving both operations; the equivalence of
fractions is transitive exactly because there are no zero divisors; and Dedekind cuts
(including one for `√2`) satisfy the least-upper-bound property. Mathlib's completeness of `ℝ`
and the uniqueness of complete ordered fields are cited (`@provenance library`).
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.CompleteField
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace Lumenary.NumberSystemConstructions

/-! ### ℤ from pairs of natural numbers -/

-- @region number_system_constructions.int_rel_trans
-- @provenance independent
/-- **Transitivity of `(a, b) ~ (c, d) ⟺ a + d = c + b`.** Adding the two hypotheses gives
`(a + f) + (c + d) = (e + b) + (c + d)`, and in `ℕ` we may cancel `c + d`. Cancellation is the one
property of `ℕ` that the construction really needs. -/
theorem intRel_trans {a b c d e f : ℕ} (h₁ : a + d = c + b) (h₂ : c + f = e + d) :
    a + f = e + b := by
  have h : (a + f) + (c + d) = (e + b) + (c + d) :=
    calc (a + f) + (c + d) = (a + d) + (c + f) := by ring
      _ = (c + b) + (e + d) := by rw [h₁, h₂]
      _ = (e + b) + (c + d) := by ring
  exact Nat.add_right_cancel h
-- @endregion

-- @region number_system_constructions.int_setoid
-- @provenance definition
/-- The equivalence relation on `ℕ × ℕ` whose classes are the integers: `(a, b) ~ (c, d)` means
`a + d = c + b`, i.e. "`a - b = c - d`" written without subtraction. Reflexivity and symmetry are
immediate; transitivity is `intRel_trans`. -/
def intSetoid : Setoid (ℕ × ℕ) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => intRel_trans h₁ h₂⟩
-- @endregion

-- @region number_system_constructions.pair_int
-- @provenance definition
/-- The constructed integers: equivalence classes of pairs of natural numbers. -/
def PairInt : Type := Quotient intSetoid
-- @endregion

-- @region number_system_constructions.add_respects
-- @provenance independent
/-- **Addition of classes is well defined.** If `(a, b) ~ (a', b')` and `(c, d) ~ (c', d')`, then
`(a + c, b + d) ~ (a' + c', b' + d')`: add the two equations. -/
theorem add_respects {a b c d a' b' c' d' : ℕ} (h₁ : a + b' = a' + b) (h₂ : c + d' = c' + d) :
    (a + c) + (b' + d') = (a' + c') + (b + d) := by
  calc (a + c) + (b' + d') = (a + b') + (c + d') := by ring
    _ = (a' + b) + (c' + d) := by rw [h₁, h₂]
    _ = (a' + c') + (b + d) := by ring
-- @endregion

-- @region number_system_constructions.mul_respects_left
-- @provenance independent
/-- **Multiplication of classes is well defined (first argument).** With
`(a, b) · (c, d) = (ac + bd, ad + bc)` — the rule `(a - b)(c - d) = (ac + bd) - (ad + bc)` —
replacing `(a, b)` by an equivalent `(a', b')` gives an equivalent product. The key step groups
the terms as `(a + b')c + (a' + b)d` and uses `a + b' = a' + b`. -/
theorem mul_respects_left {a b a' b' c d : ℕ} (h : a + b' = a' + b) :
    (a * c + b * d) + (a' * d + b' * c) = (a' * c + b' * d) + (a * d + b * c) := by
  calc (a * c + b * d) + (a' * d + b' * c) = (a + b') * c + (a' + b) * d := by ring
    _ = (a' + b) * c + (a + b') * d := by rw [h]
    _ = (a' * c + b' * d) + (a * d + b * c) := by ring
-- @endregion

-- @region number_system_constructions.mul_respects_right
-- @provenance independent
/-- **Multiplication of classes is well defined (second argument):** the same computation with
the roles of the factors exchanged, grouping as `a(c + d') + b(c' + d)`. -/
theorem mul_respects_right {a b c d c' d' : ℕ} (h : c + d' = c' + d) :
    (a * c + b * d) + (a * d' + b * c') = (a * c' + b * d') + (a * d + b * c) := by
  calc (a * c + b * d) + (a * d' + b * c') = a * (c + d') + b * (c' + d) := by ring
    _ = a * (c' + d) + b * (c + d') := by rw [h]
    _ = (a * c' + b * d') + (a * d + b * c) := by ring
-- @endregion

namespace PairInt

-- @region number_system_constructions.pair_int.add
-- @provenance definition
/-- Addition on the constructed integers: `[(a, b)] + [(c, d)] = [(a + c, b + d)]`. It is
well defined by `add_respects`. -/
def add : PairInt → PairInt → PairInt :=
  Quotient.map₂ (fun p q => (p.1 + q.1, p.2 + q.2))
    (fun _ _ h₁ _ _ h₂ => add_respects h₁ h₂)
-- @endregion

-- @region number_system_constructions.pair_int.mul
-- @provenance definition
/-- Multiplication: `[(a, b)] · [(c, d)] = [(ac + bd, ad + bc)]`. Well defined because changing
one argument at a time gives equivalent results (`mul_respects_left`, `mul_respects_right`),
and the relation is transitive. -/
def mul : PairInt → PairInt → PairInt :=
  Quotient.map₂ (fun p q => (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1))
    (fun _p p' hp q _q' hq =>
      intRel_trans (mul_respects_left (c := q.1) (d := q.2) hp)
        (mul_respects_right (a := p'.1) (b := p'.2) hq))
-- @endregion

-- @region number_system_constructions.pair_int.to_int
-- @provenance definition
/-- The comparison map to Mathlib's integers: `[(a, b)] ↦ a - b`. It is well defined because
`a + d = c + b` implies `a - b = c - d` in `ℤ`. -/
def toInt : PairInt → ℤ :=
  Quotient.lift (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
    (fun p q (h : p.1 + q.2 = q.1 + p.2) => by
      have h' : (p.1 : ℤ) + q.2 = q.1 + p.2 := by exact_mod_cast h
      linear_combination h')
-- @endregion

-- @region number_system_constructions.pair_int.to_int_add
-- @provenance independent
/-- The comparison map turns the constructed addition into the addition of `ℤ`:
`(a + c) - (b + d) = (a - b) + (c - d)`. -/
theorem toInt_add (x y : PairInt) : toInt (add x y) = toInt x + toInt y := by
  induction x using Quotient.inductionOn with | h p =>
  induction y using Quotient.inductionOn with | h q =>
  show ((p.1 + q.1 : ℕ) : ℤ) - ((p.2 + q.2 : ℕ) : ℤ) = ((p.1 : ℤ) - p.2) + ((q.1 : ℤ) - q.2)
  push_cast
  ring
-- @endregion

-- @region number_system_constructions.pair_int.to_int_mul
-- @provenance independent
/-- …and the constructed multiplication into the multiplication of `ℤ`:
`(ac + bd) - (ad + bc) = (a - b)(c - d)`. -/
theorem toInt_mul (x y : PairInt) : toInt (mul x y) = toInt x * toInt y := by
  induction x using Quotient.inductionOn with | h p =>
  induction y using Quotient.inductionOn with | h q =>
  show ((p.1 * q.1 + p.2 * q.2 : ℕ) : ℤ) - ((p.1 * q.2 + p.2 * q.1 : ℕ) : ℤ)
    = ((p.1 : ℤ) - p.2) * ((q.1 : ℤ) - q.2)
  push_cast
  ring
-- @endregion

-- @region number_system_constructions.pair_int.to_int_bijective
-- @provenance independent
/-- **The construction really produces the integers.** The comparison map is a bijection:
injective because `a - b = c - d` in `ℤ` gives `a + d = c + b` in `ℕ`, and surjective because
`n = n⁺ - n⁻` with `n⁺ = max(n, 0)` and `n⁻ = max(-n, 0)`. Together with `toInt_add` and
`toInt_mul`, it is an isomorphism of rings. -/
theorem toInt_bijective : Function.Bijective toInt := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | h p =>
    induction y using Quotient.inductionOn with | h q =>
    change (p.1 : ℤ) - p.2 = (q.1 : ℤ) - q.2 at hxy
    apply Quotient.sound
    show p.1 + q.2 = q.1 + p.2
    omega
  · intro n
    refine ⟨Quotient.mk intSetoid (n.toNat, (-n).toNat), ?_⟩
    show ((n.toNat : ℕ) : ℤ) - (((-n).toNat : ℕ) : ℤ) = n
    omega
-- @endregion

end PairInt

/-! ### ℚ from pairs of integers: why there must be no zero divisors -/

-- @region number_system_constructions.frac_trans
-- @provenance independent
/-- **Transitivity of equality of fractions**, `(a, b) ~ (c, d) ⟺ ad = cb`, in any commutative
ring without zero divisors (such as `ℤ`). From `ad = cb` and `cf = ed` we get
`(af)d = (eb)d`, and we cancel `d ≠ 0`. That cancellation is exactly where "no zero divisors"
is used. -/
theorem frac_trans {R : Type*} [CommRing R] [NoZeroDivisors R] {a b c d e f : R} (hd : d ≠ 0)
    (h₁ : a * d = c * b) (h₂ : c * f = e * d) : a * f = e * b := by
  have h : (a * f) * d = (e * b) * d :=
    calc (a * f) * d = (a * d) * f := by ring
      _ = (c * b) * f := by rw [h₁]
      _ = b * (c * f) := by ring
      _ = b * (e * d) := by rw [h₂]
      _ = (e * b) * d := by ring
  exact mul_right_cancel₀ hd h
-- @endregion

-- @region number_system_constructions.frac_trans_fails_zmod6
-- @provenance independent
/-- **With zero divisors, "fractions" break.** In `ℤ/6ℤ`, using the same rule
`(a, b) ~ (c, d) ⟺ ad = cb` with non-zero denominators, `3/1 ~ 0/2` and `0/2 ~ 0/1`, but
`3/1 ≁ 0/1`: the relation is not transitive, because `2 · 3 = 0` lets us "cancel" wrongly. -/
theorem frac_trans_fails_zmod6 :
    let r : ZMod 6 × ZMod 6 → ZMod 6 × ZMod 6 → Prop := fun p q => p.1 * q.2 = q.1 * p.2
    r (3, 1) (0, 2) ∧ r (0, 2) (0, 1) ∧ ¬ r (3, 1) (0, 1) := by
  decide
-- @endregion

-- @region number_system_constructions.rat_is_fraction_ring
-- @provenance library
/-- **`ℚ` is the field of fractions of `ℤ`.** Mathlib's instance `Rat.isFractionRing`: every
rational is `a / b` with `a, b ∈ ℤ`, `b ≠ 0`, and `a / b = c / d` exactly when `ad = cb`. -/
theorem rat_isFractionRing : IsFractionRing ℤ ℚ := Rat.isFractionRing
-- @endregion

-- @region number_system_constructions.ring_hom_rat_unique
-- @provenance library
/-- **A universal property in miniature:** there is at most one ring homomorphism from `ℚ` to
any ring, because it is forced on `ℤ` and then on fractions. Mathlib's `RingHom.ext_rat`. -/
theorem ringHom_rat_unique {R : Type*} [Semiring R] (f g : ℚ →+* R) : f = g :=
  RingHom.ext_rat f g
-- @endregion

/-! ### ℝ from Dedekind cuts -/

-- @region number_system_constructions.cut
-- @provenance definition
/-- A **Dedekind cut**: a set of rationals that is non-empty, not everything, closed downwards,
and has no greatest element. Think of it as "the rationals below a real number". -/
structure Cut where
  /-- The rationals below the real number. -/
  carrier : Set ℚ
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ Set.univ
  lower : ∀ ⦃p q : ℚ⦄, p ∈ carrier → q < p → q ∈ carrier
  no_max : ∀ p ∈ carrier, ∃ q ∈ carrier, p < q
-- @endregion

namespace Cut

-- @region number_system_constructions.cut.inst_le
-- @provenance definition
/-- Cuts are ordered by inclusion. -/
instance instLE : LE Cut := ⟨fun A B => A.carrier ⊆ B.carrier⟩
-- @endregion

-- @region number_system_constructions.cut.of_rat
-- @provenance definition
/-- The cut of a rational number `r`: all rationals below `r`. -/
def ofRat (r : ℚ) : Cut where
  carrier := {q | q < r}
  nonempty := ⟨r - 1, by simp⟩
  ne_univ := fun h => lt_irrefl r (h ▸ Set.mem_univ r : r ∈ {q : ℚ | q < r})
  lower := fun _ _ hp hq => lt_trans hq hp
  no_max := fun p hp => by
    have hp' : p < r := hp
    exact ⟨(p + r) / 2, show (p + r) / 2 < r by linarith, by linarith⟩
-- @endregion

-- @region number_system_constructions.cut.sqrt_two
-- @provenance definition
/-- **The cut of `√2`:** the rationals `q` with `q < 0` or `q² < 2`. It has no greatest element:
if `0 ≤ p` and `p² < 2`, the rational `(2p + 2)/(p + 2)` is larger than `p` and its square is
still below `2`. -/
def sqrtTwo : Cut where
  carrier := {q | q < 0 ∨ q * q < 2}
  nonempty := ⟨0, Or.inr (by norm_num)⟩
  ne_univ := by
    intro h
    have h2 : (2 : ℚ) ∈ {q : ℚ | q < 0 ∨ q * q < 2} := h ▸ Set.mem_univ 2
    rcases h2 with h2 | h2 <;> norm_num at h2
  lower := by
    intro p q hp hqp
    rcases lt_or_ge q 0 with hq | hq
    · exact Or.inl hq
    · right
      rcases hp with hp | hp
      · linarith
      · nlinarith
  no_max := by
    intro p hp
    rcases lt_or_ge p 0 with hp0 | hp0
    · exact ⟨0, Or.inr (by norm_num), hp0⟩
    · have hp2 : p * p < 2 := by
        rcases hp with hp | hp
        · linarith
        · exact hp
      have hpos : 0 < p + 2 := by linarith
      refine ⟨(2 * p + 2) / (p + 2), Or.inr ?_, ?_⟩
      · rw [div_mul_div_comm, div_lt_iff₀ (by positivity)]
        nlinarith
      · rw [lt_div_iff₀ hpos]
        nlinarith
-- @endregion

-- @region number_system_constructions.cut.le_total
-- @provenance independent
/-- **Cuts are totally ordered.** If `A ⊄ B`, pick `p ∈ A` with `p ∉ B`. Every `q ∈ B` is below
`p` (otherwise `p ≤ q` would put `p` in `B`, which is closed downwards), so `q ∈ A`. -/
theorem le_total (A B : Cut) : A ≤ B ∨ B ≤ A := by
  by_cases h : A ≤ B
  · exact Or.inl h
  · right
    obtain ⟨p, hpA, hpB⟩ := Set.not_subset.mp h
    intro q hqB
    rcases lt_or_ge q p with hqp | hpq
    · exact A.lower hpA hqp
    · exfalso
      rcases hpq.lt_or_eq with hlt | heq
      · exact hpB (B.lower hqB hlt)
      · exact hpB (heq ▸ hqB)
-- @endregion

-- @region number_system_constructions.cut.sup
-- @provenance definition
/-- The **supremum** of a non-empty family `S` of cuts that is bounded above by a cut `B`: the
union of the family. The proofs check that the union is again a cut: it is non-empty because `S`
and its members are; it is not everything because it lies inside `B`; and it is closed
downwards and has no greatest element because each member is and has none. -/
def sup (S : Set Cut) (hS : S.Nonempty) (hB : ∃ B : Cut, ∀ A ∈ S, A ≤ B) : Cut where
  carrier := ⋃ A ∈ S, A.carrier
  nonempty := by
    obtain ⟨A, hA⟩ := hS
    obtain ⟨p, hp⟩ := A.nonempty
    exact ⟨p, Set.mem_biUnion hA hp⟩
  ne_univ := by
    obtain ⟨B, hB⟩ := hB
    obtain ⟨q, hq⟩ : ∃ q, q ∉ B.carrier := by
      by_contra h
      exact B.ne_univ (Set.eq_univ_of_forall fun q => by_contra fun hq => h ⟨q, hq⟩)
    intro h
    have hq' : q ∈ ⋃ A ∈ S, A.carrier := h ▸ Set.mem_univ q
    obtain ⟨A, hA, hqA⟩ := Set.mem_iUnion₂.mp hq'
    exact hq (hB A hA hqA)
  lower := by
    intro p q hp hqp
    obtain ⟨A, hA, hpA⟩ := Set.mem_iUnion₂.mp hp
    exact Set.mem_biUnion hA (A.lower hpA hqp)
  no_max := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨q, hqA, hpq⟩ := A.no_max p hpA
    exact ⟨q, Set.mem_biUnion hA hqA, hpq⟩
-- @endregion

-- @region number_system_constructions.cut.sup_is_lub
-- @provenance independent
/-- **The least-upper-bound property of the cuts.** The union `sup S` is an upper bound of `S`
(each member is contained in the union) and it is the least one (if every member of `S` lies in
`C`, so does their union). -/
theorem sup_isLUB (S : Set Cut) (hS : S.Nonempty) (hB : ∃ B : Cut, ∀ A ∈ S, A ≤ B) :
    (∀ A ∈ S, A ≤ sup S hS hB) ∧ (∀ C : Cut, (∀ A ∈ S, A ≤ C) → sup S hS hB ≤ C) := by
  constructor
  · intro A hA p hp
    exact Set.mem_biUnion hA hp
  · intro C hC p hp
    obtain ⟨A, hA, hpA⟩ := Set.mem_iUnion₂.mp hp
    exact hC A hA hpA
-- @endregion

end Cut

/-! ### What Mathlib provides -/

-- @region number_system_constructions.real_complete
-- @provenance library
/-- **Completeness of Mathlib's `ℝ`** (built from Cauchy sequences of rationals): every non-empty
set of reals that is bounded above has a least upper bound. This is `Real.exists_isLUB`. -/
theorem real_complete {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLUB S x :=
  Real.exists_isLUB hne hbdd
-- @endregion

-- @region number_system_constructions.complete_ordered_field_unique
-- @provenance library
/-- **Uniqueness of the complete ordered field.** Any two conditionally complete linearly
ordered fields are isomorphic as ordered rings: Mathlib's
`ConditionallyCompleteLinearOrderedField.inducedOrderRingIso`, which sends `x` to the supremum
of the rationals below `x`. (Mathlib also proves the isomorphism is unique.) -/
noncomputable def complete_ordered_field_unique (F G : Type*)
    [Field F] [ConditionallyCompleteLinearOrder F] [IsStrictOrderedRing F]
    [Field G] [ConditionallyCompleteLinearOrder G] [IsStrictOrderedRing G] : F ≃+*o G :=
  ConditionallyCompleteLinearOrderedField.inducedOrderRingIso F G
-- @endregion

end Lumenary.NumberSystemConstructions
