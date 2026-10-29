/-
The Lumenary — formal mathematics
Orders, lattices and well-orders: divisibility as a partial order, maximal versus greatest
elements, maximal elements of finite posets, the lattice of subsets, the well-ordering of ℕ,
Knaster–Tarski, and Zorn's lemma.

Mathlib's order library is built from type classes: `Preorder`, `PartialOrder`, `LinearOrder`,
`Lattice` (with `⊔` for join and `⊓` for meet) and `CompleteLattice` (with `sSup` and `sInf`);
`IsLUB s a` says that `a` is a least upper bound of `s`, and `IsMax m` that nothing is strictly
above `m`. Below, the main results of the lesson are proved from the definitions
(`@provenance independent`) — antisymmetry of divisibility, the existence of maximal elements in
finite posets, the well-ordering of ℕ by strong induction, the Knaster–Tarski fixed-point
theorem — and Zorn's lemma and some library facts are cited (`@provenance library`).
-/
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

namespace Lumenary.OrderTheory

/-! ### Divisibility is a partial order on ℕ, but only a preorder on ℤ -/

-- @region order_theory.nat_dvd_antisymm
-- @provenance independent
/-- **Antisymmetry of divisibility on ℕ.** If `a ∣ b` and `b ∣ a` then `a = b`. Write `b = ak` and
`a = bl = a(kl)`. If `a = 0` then `b = 0` too; otherwise cancel `a` to get `kl = 1`, so `k = 1`
and `b = a`. (Reflexivity, `a ∣ a`, and transitivity are immediate.) -/
theorem nat_dvd_antisymm {a b : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨l, hl⟩ := h₂
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have hkl : k * l = 1 := by
      have h : a * 1 = a * (k * l) := by rw [mul_one, ← mul_assoc]; exact hl
      exact (Nat.eq_of_mul_eq_mul_left ha h).symm
    rw [Nat.eq_one_of_mul_eq_one_right hkl, mul_one]
-- @endregion

-- @region order_theory.div_nat
-- @provenance definition
/-- A copy of `ℕ` ordered by divisibility (`a ≤ b` means `a ∣ b`), so that Mathlib's order
library can be used on it. The axioms are `dvd_refl`, `dvd_trans` and `nat_dvd_antisymm`. In this
order `1` is the least element and `0` the greatest (every number divides `0`). -/
def DivNat : Type := ℕ
-- @endregion

-- @region order_theory.div_nat.inst_partial_order
-- @provenance definition
/-- The partial order on `DivNat`. -/
instance DivNat.instPartialOrder : PartialOrder DivNat where
  le a b := @Dvd.dvd ℕ _ a b
  le_refl a := @dvd_refl ℕ _ a
  le_trans a b c := @dvd_trans ℕ _ a b c
  le_antisymm a b := @nat_dvd_antisymm a b
-- @endregion

-- @region order_theory.int_dvd_not_antisymm
-- @provenance independent
/-- **On ℤ, divisibility is only a preorder.** `2 ∣ -2` and `-2 ∣ 2`, yet `2 ≠ -2`:
antisymmetry fails because `2` and `-2` are *associates* (they differ by the unit `-1`). -/
theorem int_dvd_not_antisymm : (2 : ℤ) ∣ -2 ∧ (-2 : ℤ) ∣ 2 ∧ (2 : ℤ) ≠ -2 := by
  refine ⟨⟨-1, by norm_num⟩, ⟨-1, by norm_num⟩, by norm_num⟩
-- @endregion

/-! ### Maximal is not the same as greatest -/

-- @region order_theory.maximal_in_one_to_twelve
-- @provenance independent
/-- **The maximal elements of `({1, …, 12}, ∣)` are `7, 8, 9, 10, 11, 12`:** exactly the numbers
`m` with no proper multiple in the set. Checked by `decide`. -/
theorem maximal_in_one_to_twelve :
    (Finset.Icc 1 12).filter (fun m => ∀ x ∈ Finset.Icc 1 12, m ∣ x → x = m) =
      {7, 8, 9, 10, 11, 12} := by
  decide
-- @endregion

-- @region order_theory.no_greatest_in_one_to_twelve
-- @provenance independent
/-- **…but there is no greatest element:** no `g ∈ {1, …, 12}` is divisible by every member. With
several maximal elements, none of them can be greatest. -/
theorem no_greatest_in_one_to_twelve :
    ¬ ∃ g ∈ Finset.Icc 1 12, ∀ x ∈ Finset.Icc 1 12, x ∣ g := by
  decide
-- @endregion

-- @region order_theory.exists_maximal_of_finite
-- @provenance independent
/-- **Every finite non-empty poset has a maximal element.** Choose `m` with the largest number of
elements below it. If `m ≤ x`, everything below `m` is below `x`, so the down-set of `m` is
contained in that of `x`; by the choice of `m` the two down-sets have the same size, hence are
equal. Then `x` (which is below `x`) is below `m`, and antisymmetry gives `x = m`. -/
theorem exists_maximal_of_finite {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α] :
    ∃ m : α, ∀ x, m ≤ x → x = m := by
  classical
  obtain ⟨m, hm⟩ := Finite.exists_max (fun y : α => (Finset.univ.filter (· ≤ y)).card)
  refine ⟨m, fun x hmx => ?_⟩
  have hsub : Finset.univ.filter (· ≤ m) ⊆ Finset.univ.filter (· ≤ x) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact le_trans hy hmx
  have heq := Finset.eq_of_subset_of_card_le hsub (hm x)
  have hx : x ∈ Finset.univ.filter (· ≤ m) := by
    rw [heq]
    simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact le_antisymm hx hmx
-- @endregion

/-! ### Joins, meets and lattices -/

-- @region order_theory.union_is_lub
-- @provenance independent
/-- **In `(P(A), ⊆)` the join of two sets is their union:** `s ∪ t` is an upper bound of
`{s, t}`, and any set containing both `s` and `t` contains `s ∪ t`. -/
theorem union_isLUB {A : Type*} (s t : Set A) : IsLUB {s, t} (s ∪ t) := by
  constructor
  · rintro u (rfl | rfl)
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  · intro u hu
    exact Set.union_subset (hu (Set.mem_insert s {t})) (hu (Set.mem_insert_of_mem s rfl))
-- @endregion

-- @region order_theory.inter_is_glb
-- @provenance independent
/-- **…and the meet is the intersection**, by the dual argument. So `(P(A), ⊆)` is a lattice. -/
theorem inter_isGLB {A : Type*} (s t : Set A) : IsGLB {s, t} (s ∩ t) := by
  constructor
  · rintro u (rfl | rfl)
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right
  · intro u hu
    exact Set.subset_inter (hu (Set.mem_insert s {t})) (hu (Set.mem_insert_of_mem s rfl))
-- @endregion

-- @region order_theory.gcd_is_meet
-- @provenance library
/-- **In `(ℕ, ∣)` the meet of `a` and `b` is `gcd(a, b)`:** `d` divides `gcd(a, b)` exactly when it
divides both. This is core Lean's `Nat.dvd_gcd_iff`. (Dually, the join is `lcm(a, b)`.) -/
theorem gcd_is_meet (a b d : ℕ) : d ∣ Nat.gcd a b ↔ d ∣ a ∧ d ∣ b := Nat.dvd_gcd_iff
-- @endregion

-- @region order_theory.lub_not_mem
-- @provenance library
/-- **A least upper bound need not belong to the set:** in `ℚ`, the set of rationals below `1`
has least upper bound `1`, which is not in the set. Mathlib's `isLUB_Iio`. -/
theorem lub_not_mem : IsLUB (Set.Iio (1 : ℚ)) 1 ∧ (1 : ℚ) ∉ Set.Iio 1 :=
  ⟨isLUB_Iio, fun h => lt_irrefl (1 : ℚ) h⟩
-- @endregion

-- @region order_theory.absorption
-- @provenance independent
/-- **The absorption law** `a ⊔ (a ⊓ b) = a`, which holds in every lattice: `a` is an upper bound
of `a` and of `a ⊓ b ≤ a`, so the join is at most `a`; and `a ≤ a ⊔ (a ⊓ b)` always. Mathlib's
`sup_inf_self`. Absorption, with associativity and commutativity of `⊔` and `⊓`, characterises
lattices algebraically. -/
theorem absorption {L : Type*} [Lattice L] (a b : L) : a ⊔ (a ⊓ b) = a :=
  le_antisymm (sup_le le_rfl inf_le_left) le_sup_left
-- @endregion

/-! ### Well-orders -/

-- @region order_theory.nat_well_ordered
-- @provenance independent
/-- **ℕ is well-ordered: every non-empty set of naturals has a least element.** Suppose `S` has no
least element. By strong induction no `k` lies in `S`: if `k ∈ S`, then since `k` is not least
there is a smaller `n ∈ S`, contradicting the induction hypothesis for `n`. So `S` is empty. -/
theorem nat_wellOrdered (S : Set ℕ) (hS : S.Nonempty) : ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  by_contra h
  have h' : ∀ m ∈ S, ∃ n ∈ S, n < m := by
    intro m hm
    by_contra hne
    exact h ⟨m, hm, fun n hn => not_lt.mp fun hnm => hne ⟨n, hn, hnm⟩⟩
  have key : ∀ k, k ∉ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      obtain ⟨n, hn, hnk⟩ := h' k hk
      exact ih n hnk hn
  obtain ⟨x, hx⟩ := hS
  exact key x hx
-- @endregion

-- @region order_theory.int_not_well_ordered
-- @provenance independent
/-- **ℤ is not well-ordered by `≤`:** the whole of `ℤ` (a non-empty set) has no least element,
since `m - 1 < m` for every `m`. -/
theorem int_not_wellOrdered : ¬ ∃ m : ℤ, ∀ x : ℤ, m ≤ x := by
  rintro ⟨m, hm⟩
  have := hm (m - 1)
  omega
-- @endregion

-- @region order_theory.rat_pos_no_least
-- @provenance independent
/-- **Nor is ℚ, even on the positive part:** the positive rationals have no least element, since
`0 < m/2 < m` whenever `0 < m`. -/
theorem rat_pos_no_least : ¬ ∃ m : ℚ, 0 < m ∧ ∀ q : ℚ, 0 < q → m ≤ q := by
  rintro ⟨m, hm, hmin⟩
  have := hmin (m / 2) (by linarith)
  linarith
-- @endregion

/-! ### Fixed points and Zorn's lemma -/

-- @region order_theory.knaster_tarski
-- @provenance independent
/-- **Knaster–Tarski: every monotone map on a complete lattice has a least fixed point**, namely
`a = inf {x | f x ≤ x}`. For each such `x`, `a ≤ x` gives `f a ≤ f x ≤ x`, so `f a` is a lower
bound and `f a ≤ a`. Then `f (f a) ≤ f a`, so `f a` belongs to the set and `a ≤ f a`. Any fixed
point `b` belongs to the set, so `a ≤ b`. (Mathlib's version is `OrderHom.lfp`.) -/
theorem knaster_tarski {L : Type*} [CompleteLattice L] (f : L → L) (hf : Monotone f) :
    ∃ a, f a = a ∧ ∀ b, f b = b → a ≤ b := by
  set a := sInf {x | f x ≤ x} with ha
  have h1 : f a ≤ a := le_sInf fun x hx => le_trans (hf (sInf_le hx)) hx
  have h2 : a ≤ f a := sInf_le (show f (f a) ≤ f a from hf h1)
  exact ⟨a, le_antisymm h1 h2, fun b hb => sInf_le (show f b ≤ b from hb.le)⟩
-- @endregion

-- @region order_theory.zorn
-- @provenance library
/-- **Zorn's lemma:** in a preorder in which every chain has an upper bound, there is a maximal
element (nothing strictly above it). Mathlib's `zorn_le`, proved there from the axiom of choice;
over ZF the two are equivalent (see the lesson on the axiom of choice). -/
theorem zorn {α : Type*} [Preorder α] (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ m : α, IsMax m :=
  zorn_le h
-- @endregion

end Lumenary.OrderTheory
