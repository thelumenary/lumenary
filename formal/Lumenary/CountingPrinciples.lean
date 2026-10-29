/-
The Lumenary — formal mathematics
Counting principles: the addition and multiplication principles, factorials, ordered
selections, arrangements, complementary counting and the overlap rule.

Finite collections are modelled as lists, so "how many?" is the length of a list. We prove the
counting principles for lists by induction (`@provenance independent`), define factorials and
ordered selections recursively, and build the list of all arrangements of a list by inserting
the first object into every position of every arrangement of the rest. Lean then checks that
there are exactly `n!` arrangements. Concrete counts (PINs, podiums, codes) are computed by
Lean and checked with `decide`. Core Lean only, no Mathlib.
Mathlib analogue: `Nat.factorial`, `Nat.descFactorial`, `Finset.card_product`,
`Finset.card_union_add_card_inter`, `List.permutations` and `List.length_permutations`.
-/

namespace Lumenary.CountingPrinciples

variable {α β : Type}

/-! ### The addition and multiplication principles -/

-- @region counting_principles.addition_principle
-- @provenance library
/-- **The addition principle.** Choosing one item from a list `A` or from a separate list `B`
can be done in `|A| + |B|` ways: putting the two lists together adds their lengths.
This applies core Lean's `List.length_append`. -/
theorem addition_principle (A B : List α) : (A ++ B).length = A.length + B.length :=
  List.length_append
-- @endregion

-- @region counting_principles.pairs
-- @provenance definition
/-- All ordered pairs `(a, b)` with `a` from `A` and `b` from `B` (the Cartesian product, as a
list): for each `a`, pair it with every `b`. -/
def pairs (A : List α) (B : List β) : List (α × β) := A.flatMap (fun a => B.map (fun b => (a, b)))
-- @endregion

-- @region counting_principles.multiplication_principle
-- @provenance independent
/-- **The multiplication principle.** There are `|A| · |B|` ordered pairs. The proof is the
addition principle used again and again: the pairs starting with the first `a` (there are
`|B|` of them), then those starting with the next `a`, and so on. -/
theorem multiplication_principle (A : List α) (B : List β) :
    (pairs A B).length = A.length * B.length := by
  induction A with
  | nil => simp [pairs]
  | cons a A ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]
-- @endregion

/-! ### Complements and overlaps -/

-- @region counting_principles.complement_principle
-- @provenance independent
/-- **Complementary counting.** Every item either has property `p` or does not, so
`|with p| = |all| - |without p|`. Here in the form `|with p| + |without p| = |all|`.
Proof by induction on the list. -/
theorem complement_principle (S : List α) (p : α → Bool) :
    (S.filter p).length + (S.filter (fun x => !p x)).length = S.length := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    cases h : p a <;> simp [h] <;> omega
-- @endregion

-- @region counting_principles.overlap_rule
-- @provenance independent
/-- **Counting overlapping cases.** Items with property `p` or `q`, plus items with both, equal
items with `p` plus items with `q`: `|A ∪ B| + |A ∩ B| = |A| + |B|`. Adding `|A| + |B|` counts the
overlap twice, so it must be subtracted once. Induction, with four cases for the first item. -/
theorem overlap_rule (S : List α) (p q : α → Bool) :
    (S.filter (fun x => p x || q x)).length + (S.filter (fun x => p x && q x)).length
      = (S.filter p).length + (S.filter q).length := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega
-- @endregion

/-! ### Factorials and ordered selections -/

-- @region counting_principles.fact
-- @provenance definition
/-- The factorial `n! = n · (n - 1) ⋯ 2 · 1`, with `0! = 1`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
-- @endregion

-- @region counting_principles.perm
-- @provenance definition
/-- `perm n k` is the number of ordered selections of `k` objects from `n` different objects:
`n · (n - 1) ⋯ (n - k + 1)`. To choose `k + 1` objects in order from `n + 1`, pick the first
(`n + 1` ways), then `k` more in order from the `n` that are left. -/
def perm : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * perm n k
-- @endregion

-- @region counting_principles.perm_mul_fact
-- @provenance independent
/-- **Ordered selections: `P(n, k) = n! / (n - k)!`**, in the division-free form
`P(n, k) · (n - k)! = n!` for `k ≤ n`. Proof by induction on `n`. -/
theorem perm_mul_fact : ∀ n k : Nat, k ≤ n → perm n k * fact (n - k) = fact n := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => simp [perm]
    | succ k =>
      have hk' : k ≤ n := by omega
      have hsub : n + 1 - (k + 1) = n - k := by omega
      rw [perm, hsub, Nat.mul_assoc, ih k hk', fact]
-- @endregion

-- @region counting_principles.perm_self
-- @provenance independent
/-- Arranging all `n` objects in order: `P(n, n) = n!`. (Take `k = n` in `perm_mul_fact`:
`(n - n)! = 0! = 1`.) -/
theorem perm_self (n : Nat) : perm n n = fact n := by
  have h := perm_mul_fact n n (Nat.le_refl n)
  rw [Nat.sub_self, fact, Nat.mul_one] at h
  exact h
-- @endregion

-- @region counting_principles.perm_eq_zero
-- @provenance independent
/-- You cannot choose more objects than you have: `P(n, k) = 0` when `k > n`. -/
theorem perm_eq_zero : ∀ n k : Nat, n < k → perm n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => rw [perm, ih k (by omega), Nat.mul_zero]
-- @endregion

/-! ### All the arrangements of a list -/

-- @region counting_principles.insert_all
-- @provenance definition
/-- `insertAll a l` lists the ways of inserting a new object `a` into the row `l`: in front, or
after the first object, …, or at the end. -/
def insertAll (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertAll a l).map (fun m => b :: m)
-- @endregion

-- @region counting_principles.arrangements
-- @provenance definition
/-- All arrangements (orderings) of a list: arrange the rest, then insert the first object in
every possible position. -/
def arrangements : List α → List (List α)
  | [] => [[]]
  | a :: l => (arrangements l).flatMap (insertAll a)
-- @endregion

-- @region counting_principles.length_insert_all
-- @provenance independent
/-- A new object can go into a row of `n` objects in `n + 1` places. -/
theorem length_insert_all (a : α) (l : List α) : (insertAll a l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [insertAll, ih]
-- @endregion

-- @region counting_principles.mem_insert_all_length
-- @provenance independent
/-- Every row obtained by inserting `a` into `l` has one more object than `l`. -/
theorem mem_insert_all_length (a : α) (l m : List α) (h : m ∈ insertAll a l) :
    m.length = l.length + 1 := by
  induction l generalizing m with
  | nil =>
    simp [insertAll] at h
    subst h
    rfl
  | cons b l ih =>
    simp only [insertAll, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨m', hm', rfl⟩
    · subst h
      simp
    · simp [ih m' hm']
-- @endregion

-- @region counting_principles.mem_arrangements_length
-- @provenance independent
/-- Every arrangement of `l` has the same length as `l`. -/
theorem mem_arrangements_length (l m : List α) (h : m ∈ arrangements l) : m.length = l.length := by
  induction l generalizing m with
  | nil =>
    simp [arrangements] at h
    subst h
    rfl
  | cons a l ih =>
    simp only [arrangements, List.mem_flatMap] at h
    obtain ⟨m', hm', hm⟩ := h
    rw [mem_insert_all_length a m' m hm, ih m' hm', List.length_cons]
-- @endregion

-- @region counting_principles.length_arrangements
-- @provenance independent
/-- **`n` different objects can be arranged in `n!` ways.** Each of the `(n - 1)!` arrangements of
the other objects (induction hypothesis) gives `n` arrangements, one for each place the new
object can go, so there are `(n - 1)! · n = n!` in all. -/
theorem length_arrangements (l : List α) : (arrangements l).length = fact l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [arrangements, List.length_flatMap]
    have hconst : (arrangements l).map (fun m => (insertAll a m).length)
        = (arrangements l).map (fun _ => l.length + 1) := by
      apply List.map_congr_left
      intro m hm
      rw [length_insert_all, mem_arrangements_length l m hm]
    rw [hconst, List.map_const', List.sum_replicate_nat, ih, List.length_cons, fact,
      Nat.mul_comm]
-- @endregion

-- @region counting_principles.arrangements_three
-- @provenance independent
/-- The `3! = 6` arrangements of three objects, listed by Lean. -/
theorem arrangements_three :
    arrangements [1, 2, 3] = [[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]] := by
  decide
-- @endregion

-- @region counting_principles.arrangements_four_distinct
-- @provenance independent
/-- The arrangements of four different objects are all different from one another, and there
are `4! = 24` of them: nothing is missed and nothing is counted twice. Checked by Lean. -/
theorem arrangements_four_distinct :
    (arrangements [1, 2, 3, 4]).Nodup ∧ (arrangements [1, 2, 3, 4]).length = 24 := by
  decide
-- @endregion

/-! ### Counts from the lesson -/

-- @region counting_principles.lesson_counts
-- @provenance independent
/-- Counts from the lesson, computed by Lean: 4-digit PINs with no repeated digit (`5040`),
podium finishes for 8 runners (`336`), arrangements of 5 different letters (`120`), and
4-symbol passwords from 26 letters and 10 digits that contain at least one digit. -/
theorem lesson_counts :
    perm 10 4 = 5040 ∧ perm 8 3 = 336 ∧ fact 5 = 120 ∧ 36 ^ 4 - 26 ^ 4 = 1222640 := by
  decide
-- @endregion

-- @region counting_principles.at_least_one_seven
-- @provenance independent
/-- **Complementary counting, checked by brute force.** Of the 1000 codes `000`–`999`, the
number containing at least one digit `7` is `1000 - 9³ = 271`. Lean checks this by going
through all 1000 codes. -/
theorem at_least_one_seven :
    ((List.range 1000).filter
      (fun n => n % 10 == 7 || n / 10 % 10 == 7 || n / 100 == 7)).length = 1000 - 9 ^ 3 := by
  decide +kernel
-- @endregion

end Lumenary.CountingPrinciples
