/-
The Lumenary — formal mathematics
Combinatorics: binomial coefficients as counts of subsets, Pascal's rule, the binomial theorem,
the pigeonhole principle and inclusion–exclusion.

Proved here (`@provenance independent`): Pascal's rule for subsets, by splitting the
`(k + 1)`-element subsets of `insert a s` into those that avoid `a` and those that contain it;
the theorem that the number of `k`-element subsets of an `n`-element set is `n.choose k` (Mathlib
*defines* `Nat.choose` by Pascal's rule, so this says "counting subsets builds Pascal's
triangle"); the binomial theorem for `(1 + x)ⁿ` by induction on `n`; the row sums `2ⁿ` and the
alternating row sums `0`; the pigeonhole principle, by counting the objects box by box; an
application to remainders; and inclusion–exclusion for three sets, from the two-set version.

From Mathlib (`@provenance library`): the factorial formula
`Nat.choose_mul_factorial_mul_factorial`, the symmetry `Nat.choose_symm`, the binomial theorem
for `(x + y)ⁿ` (`add_pow`), the pigeonhole principle
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, and two-set inclusion–exclusion
`Finset.card_union_add_card_inter`.

Notation: `#s` is the number of elements of the finite set `s`, `powersetCard k s` is the finite
set of `k`-element subsets of `s`, and `n.choose k` is the binomial coefficient `C(n, k)`.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval

namespace Lumenary.Combinatorics

open Finset

/-! ### Binomial coefficients count subsets -/

-- @region combinatorics.pascal_subsets
-- @provenance independent
/-- **Pascal's rule, by counting.** Let `a` be a new element, not in `s`. A `(k + 1)`-element
subset of `insert a s` either avoids `a` — then it is a `(k + 1)`-element subset of `s` — or
contains `a` — then it is `insert a t` for exactly one `k`-element subset `t` of `s`. The two
kinds do not overlap, so their numbers add up. -/
theorem pascal_subsets {α : Type*} [DecidableEq α] {a : α} {s : Finset α} (ha : a ∉ s)
    (k : ℕ) :
    #(powersetCard (k + 1) (insert a s)) = #(powersetCard (k + 1) s) + #(powersetCard k s) := by
  rw [powersetCard_succ_insert ha, card_union_of_disjoint]
  · -- putting `a` back is one-to-one on the subsets of `s`, since none of them contains `a`
    congr 1
    apply card_image_of_injOn
    intro t ht u hu htu
    have hat : a ∉ t := fun h => ha ((mem_powersetCard.1 ht).1 h)
    have hau : a ∉ u := fun h => ha ((mem_powersetCard.1 hu).1 h)
    have := congrArg (fun v => v.erase a) htu
    simpa [erase_insert hat, erase_insert hau] using this
  · -- no subset of `s` contains `a`, so the two kinds are disjoint
    rw [disjoint_left]
    intro t ht ht'
    obtain ⟨u, -, rfl⟩ := mem_image.1 ht'
    exact ha ((mem_powersetCard.1 ht).1 (mem_insert_self a u))
-- @endregion

-- @region combinatorics.card_subsets_eq_choose
-- @provenance independent
/-- **`C(n, k)` counts the `k`-element subsets of an `n`-element set.** Mathlib defines
`Nat.choose` by the rules `C(n, 0) = 1`, `C(0, k + 1) = 0` and Pascal's rule
`C(n + 1, k + 1) = C(n, k) + C(n, k + 1)`. Counting subsets obeys the same three rules
(the last one is `pascal_subsets`), so, by induction on the set, the two agree.
(Mathlib states this as `Finset.card_powersetCard`.) -/
theorem card_subsets_eq_choose {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ) :
    #(powersetCard k s) = (#s).choose k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => rw [powersetCard_zero, card_singleton, card_empty, Nat.choose_zero_right]
    | succ k =>
      rw [powersetCard_eq_empty.2 (by simp), card_empty, card_empty, Nat.choose_zero_succ]
  | insert a s ha ih =>
    cases k with
    | zero => rw [powersetCard_zero, card_singleton, Nat.choose_zero_right]
    | succ k =>
      rw [pascal_subsets ha, ih, ih, card_insert_of_notMem ha, Nat.choose_succ_succ', add_comm]
-- @endregion

-- @region combinatorics.choose_factorial
-- @provenance library
/-- **The factorial formula.** For `k ≤ n`, `C(n, k) · k! · (n − k)! = n!`, that is
`C(n, k) = n! / (k! (n − k)!)`. This applies Mathlib's `Nat.choose_mul_factorial_mul_factorial`. -/
theorem choose_factorial {n k : ℕ} (hk : k ≤ n) :
    n.choose k * k.factorial * (n - k).factorial = n.factorial :=
  Nat.choose_mul_factorial_mul_factorial hk
-- @endregion

-- @region combinatorics.choose_symm
-- @provenance library
/-- **Symmetry of Pascal's triangle:** `C(n, n − k) = C(n, k)` for `k ≤ n` — choosing the `k`
members of a committee is the same as choosing the `n − k` people left out.
This applies Mathlib's `Nat.choose_symm`. -/
theorem choose_symm {n k : ℕ} (hk : k ≤ n) : n.choose (n - k) = n.choose k :=
  Nat.choose_symm hk
-- @endregion

-- @region combinatorics.five_card_hands
-- @provenance independent
/-- There are `C(52, 5) = 2 598 960` five-card hands from a standard pack. Lean evaluates the
factorial formula exactly. -/
theorem five_card_hands : Nat.choose 52 5 = 2598960 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  rfl
-- @endregion

/-! ### The binomial theorem -/

-- @region combinatorics.binomial_one_add
-- @provenance independent
/-- **The binomial theorem for `(1 + x)ⁿ`, by induction on `n`.** Multiplying
`(1 + x)ⁿ = Σₖ C(n, k) xᵏ` by `1 + x` gives the sum once as it is and once shifted up by one
power of `x`. Collecting the coefficient of `xᵏ⁺¹` gives `C(n, k + 1) + C(n, k)`, which is
`C(n + 1, k + 1)` by Pascal's rule. -/
theorem binomial_one_add {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    (1 + x) ^ n = ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- the old sum with one extra (zero) term on top
    have top : ∑ k ∈ range (n + 2), (n.choose k : R) * x ^ k =
        ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ k := by
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    -- Pascal's rule, term by term
    have pascal : ∑ k ∈ range (n + 2), ((n + 1).choose k : R) * x ^ k =
        ∑ k ∈ range (n + 1), (n.choose k : R) * x ^ (k + 1) +
          ∑ k ∈ range (n + 2), (n.choose k : R) * x ^ k := by
      rw [sum_range_succ' _ (n + 1), sum_range_succ' (fun k => (n.choose k : R) * x ^ k) (n + 1)]
      simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
        Nat.choose_zero_right]
      ring
    rw [pascal, top, pow_succ, ih, mul_add, mul_one, sum_mul]
    simp only [mul_assoc, ← pow_succ]
    ring
-- @endregion

-- @region combinatorics.binomial_theorem
-- @provenance library
/-- **The binomial theorem** `(x + y)ⁿ = Σₖ C(n, k) xᵏ yⁿ⁻ᵏ` in any commutative semiring.
This applies Mathlib's `add_pow` (proved there for any two commuting elements of a semiring). -/
theorem binomial_theorem {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ range (n + 1), x ^ k * y ^ (n - k) * (n.choose k : R) :=
  add_pow x y n
-- @endregion

-- @region combinatorics.row_sum
-- @provenance independent
/-- **Each row of Pascal's triangle adds up to a power of two:** `Σₖ C(n, k) = 2ⁿ`.
Put `x = 1` in `binomial_one_add`. (Counting proof: both sides count all subsets of an
`n`-element set.) -/
theorem row_sum (n : ℕ) : ∑ k ∈ range (n + 1), n.choose k = 2 ^ n := by
  have h := binomial_one_add (1 : ℕ) n
  simpa [one_add_one_eq_two] using h.symm
-- @endregion

-- @region combinatorics.alternating_row_sum
-- @provenance independent
/-- **Alternating row sums vanish:** `Σₖ (−1)ᵏ C(n + 1, k) = 0`. Put `x = −1` in
`binomial_one_add`: the left side is `(1 − 1)ⁿ⁺¹ = 0`. So a non-empty set has as many subsets
of even size as of odd size. -/
theorem alternating_row_sum (n : ℕ) :
    ∑ k ∈ range (n + 2), ((n + 1).choose k : ℤ) * (-1) ^ k = 0 := by
  have h := binomial_one_add (-1 : ℤ) (n + 1)
  rw [← h]
  simp
-- @endregion

/-! ### The pigeonhole principle -/

-- @region combinatorics.pigeonhole
-- @provenance independent
/-- **The pigeonhole principle.** If `f` puts every object of `s` into a box of `t`, and there
are more objects than boxes, then two different objects share a box. Proof by counting: the
number of objects is the sum, over the boxes, of the number of objects in each box. If no box
held two objects, every term would be at most `1`, so there would be at most `#t` objects. -/
theorem pigeonhole {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hst : #t < #s) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra! h
  -- if no two objects share a box, every box holds at most one object
  have hbox : ∀ b ∈ t, #{a ∈ s | f a = b} ≤ 1 := by
    intro b _
    rw [card_le_one]
    intro x hx y hy
    rw [mem_filter] at hx hy
    by_contra hxy
    exact h x hx.1 y hy.1 hxy (hx.2.trans hy.2.symm)
  have : #s ≤ #t :=
    calc #s = ∑ b ∈ t, #{a ∈ s | f a = b} := card_eq_sum_card_fiberwise (fun a ha => hf a ha)
      _ ≤ ∑ b ∈ t, 1 := sum_le_sum hbox
      _ = #t := by simp
  omega
-- @endregion

-- @region combinatorics.pigeonhole_library
-- @provenance library
/-- The same principle from Mathlib: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`. -/
theorem pigeonhole_library {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hst : #t < #s) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
  exists_ne_map_eq_of_card_lt_of_maps_to hst (fun a ha => hf a ha)
-- @endregion

-- @region combinatorics.same_remainder
-- @provenance independent
/-- **Among any `n + 1` integers, two differ by a multiple of `n`.** The boxes are the `n`
possible remainders `0, 1, …, n − 1` on division by `n`; there are `n + 1` integers, so two of
them have the same remainder, and their difference is divisible by `n`. Nothing tells us
*which* two — the pigeonhole principle only proves that they exist. -/
theorem same_remainder (n : ℕ) (hn : 0 < n) (a : Fin (n + 1) → ℤ) :
    ∃ i j, i ≠ j ∧ (n : ℤ) ∣ a i - a j := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  obtain ⟨i, -, j, -, hij, h⟩ :=
    pigeonhole (univ : Finset (Fin (n + 1))) (Ico (0 : ℤ) n) (fun i => a i % n)
      (fun i _ => mem_Ico.2 ⟨Int.emod_nonneg _ hn'.ne', Int.emod_lt_of_pos _ hn'⟩)
      (by simp)
  exact ⟨i, j, hij, Int.ModEq.dvd h.symm⟩
-- @endregion

/-! ### Inclusion–exclusion -/

-- @region combinatorics.incl_excl_two
-- @provenance library
/-- **Inclusion–exclusion for two sets:** `|A ∪ B| + |A ∩ B| = |A| + |B|` (written without
subtraction, which is awkward in `ℕ`). This applies Mathlib's
`Finset.card_union_add_card_inter`. -/
theorem incl_excl_two {α : Type*} [DecidableEq α] (A B : Finset α) :
    #(A ∪ B) + #(A ∩ B) = #A + #B :=
  card_union_add_card_inter A B
-- @endregion

-- @region combinatorics.incl_excl_three
-- @provenance independent
/-- **Inclusion–exclusion for three sets:**
`|A ∪ B ∪ C| = |A| + |B| + |C| − |A ∩ B| − |A ∩ C| − |B ∩ C| + |A ∩ B ∩ C|`,
written with every term on the side where it is added. The proof is the lesson's: apply the
two-set rule to `A ∪ B` and `C`, then to `A` and `B`, then to `A ∩ C` and `B ∩ C`, using
`(A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)`. -/
theorem incl_excl_three {α : Type*} [DecidableEq α] (A B C : Finset α) :
    #(A ∪ B ∪ C) + #(A ∩ B) + #(A ∩ C) + #(B ∩ C) = #A + #B + #C + #(A ∩ B ∩ C) := by
  have h1 := card_union_add_card_inter (A ∪ B) C
  have h2 := card_union_add_card_inter A B
  have h3 := card_union_add_card_inter (A ∩ C) (B ∩ C)
  have e1 : (A ∪ B) ∩ C = A ∩ C ∪ B ∩ C := union_inter_distrib_right A B C
  have e2 : A ∩ C ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp only [mem_inter]
    tauto
  rw [e1] at h1
  rw [e2] at h3
  omega
-- @endregion

-- @region combinatorics.divisible_by_2_3_or_5
-- @provenance independent
/-- Of the numbers `1, 2, …, 100`, exactly `74` are divisible by `2`, `3` or `5`, as
inclusion–exclusion predicts: `50 + 33 + 20 − 16 − 10 − 6 + 3 = 74`. Lean checks all hundred. -/
theorem divisible_by_2_3_or_5 :
    #{n ∈ Icc 1 100 | 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n} = 74 := by
  decide
-- @endregion

end Lumenary.Combinatorics
