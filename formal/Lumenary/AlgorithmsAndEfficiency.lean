/-
The Lumenary — formal mathematics
Algorithms, correctness and efficiency.

Proved here (`@provenance independent`), mirroring the lesson: linear search is correct and
makes at most `n` comparisons; binary search (in its "find the first yes" form) returns the
least point where a monotone test turns true — proved by a loop invariant and a decreasing
measure — and makes at most `⌊log₂ n⌋ + 1` probes; Euclid's algorithm computes the gcd
(invariant `gcd(a, b) = gcd(b, a mod b)`); a binary decision tree of height `h` has at most
`2^h` leaves, so a comparison sort of `n` items needs height at least `log₂ n!` — for
example, sorting 5 items needs 7 comparisons in the worst case.

From the library (`@provenance library`): Mathlib's `List.pairwise_insertionSort` and
`List.perm_insertionSort` (insertion sort returns a sorted rearrangement of its input). Our
algorithms are written as recursive functions, the functional counterpart of loops: each
recursive call is one pass of the loop, and the hypotheses carried into the call are the loop
invariant.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Factorial.Basic

namespace Lumenary.AlgorithmsAndEfficiency

/-! ### Linear search -/

-- @region algorithms_and_efficiency.linear_search
-- @provenance definition
/-- **Linear search**: is `t` in the list? Compare `t` with each entry in turn. -/
def linearSearch (t : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => x == t || linearSearch t xs
-- @endregion

-- @region algorithms_and_efficiency.linear_search_correct
-- @provenance independent
/-- **Linear search is correct**: it answers `true` exactly when `t` is in the list. Proof by
induction on the list (the loop invariant "`t` is not among the entries already checked"). -/
theorem linearSearch_correct (t : ℕ) (xs : List ℕ) : linearSearch t xs = true ↔ t ∈ xs := by
  induction xs with
  | nil => simp [linearSearch]
  | cons x xs ih => simp [linearSearch, ih, @eq_comm _ x t]
-- @endregion

-- @region algorithms_and_efficiency.linear_comparisons
-- @provenance definition
/-- The number of comparisons linear search makes: it stops at the first match. -/
def linearComparisons (t : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => if x = t then 1 else 1 + linearComparisons t xs
-- @endregion

-- @region algorithms_and_efficiency.linear_comparisons_le
-- @provenance independent
/-- Linear search makes **at most `n` comparisons** on a list of length `n`. -/
theorem linearComparisons_le (t : ℕ) (xs : List ℕ) : linearComparisons t xs ≤ xs.length := by
  induction xs with
  | nil => simp [linearComparisons]
  | cons x xs ih =>
    simp only [linearComparisons, List.length_cons]
    split_ifs <;> omega
-- @endregion

-- @region algorithms_and_efficiency.linear_comparisons_absent
-- @provenance independent
/-- …and **exactly `n`** when `t` is absent: the worst case really happens. -/
theorem linearComparisons_absent (t : ℕ) (xs : List ℕ) (h : t ∉ xs) :
    linearComparisons t xs = xs.length := by
  induction xs with
  | nil => simp [linearComparisons]
  | cons x xs ih =>
    have hx : x ≠ t := fun hxt => h (hxt ▸ List.mem_cons_self)
    have hxs : t ∉ xs := fun ht => h (List.mem_cons_of_mem x ht)
    simp [linearComparisons, hx, ih hxs]
    omega
-- @endregion

/-! ### Binary search -/

-- @region algorithms_and_efficiency.bsearch
-- @provenance definition
/-- **Binary search for the first "yes".** `p` is a yes/no test on `lo, …, hi`. Probe the
middle `m = ⌊(lo + hi)/2⌋`: if `p m` is true, the first "yes" is at most `m`, so continue with
`lo, …, m`; otherwise it is after `m`, so continue with `m + 1, …, hi`. Stop when `lo = hi`.
Lean accepts the definition because `hi - lo` strictly decreases at each call. -/
def bsearch (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if lo < hi then
    if p ((lo + hi) / 2) then bsearch p lo ((lo + hi) / 2)
    else bsearch p ((lo + hi) / 2 + 1) hi
  else lo
termination_by hi - lo
decreasing_by all_goals omega
-- @endregion

-- @region algorithms_and_efficiency.bsearch_correct
-- @provenance independent
/-- **Binary search is correct.** Suppose `p` is monotone (once true, it stays true). The
**loop invariant** is:
* `lo ≤ hi`,
* `p hi` is true (there is a "yes" at the right end), and
* `p k` is false for every `k < lo` (everything left of `lo` is a "no").
It holds initially by hypothesis, and each probe preserves it: if `p m` is true we move `hi`
down to `m`; if `p m` is false then, by monotonicity, so is every `k ≤ m`, and we move `lo`
up to `m + 1`. When the loop stops, `lo = hi`, and the invariant says exactly that `lo` is
the first "yes". The proof is a strong induction on the size `hi - lo` (the **termination
measure**). -/
theorem bsearch_correct (p : ℕ → Bool) (hmono : ∀ a b, a ≤ b → p a = true → p b = true) :
    ∀ lo hi, lo ≤ hi → p hi = true → (∀ k, k < lo → p k = false) →
      p (bsearch p lo hi) = true ∧ ∀ k, k < bsearch p lo hi → p k = false := by
  intro lo hi
  induction h : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | _ n ih =>
    intro hle hhi hlo
    rw [bsearch]
    split_ifs with hlt hp
    · -- `p m` true: continue on `lo, …, m`; the invariant holds with `hi := m`.
      exact ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega) hp hlo
    · -- `p m` false: continue on `m + 1, …, hi`; everything up to `m` is a "no".
      refine ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl (by omega) hhi ?_
      intro k hk
      cases hpk : p k with
      | false => rfl
      | true => exact absurd (hmono k ((lo + hi) / 2) (by omega) hpk) hp
    · -- `lo = hi`: the invariant says `lo` is the first "yes".
      have hEq : lo = hi := by omega
      subst hEq
      exact ⟨hhi, hlo⟩
-- @endregion

-- @region algorithms_and_efficiency.bsearch_steps
-- @provenance definition
/-- The number of probes `bsearch` makes on `lo, …, hi` (same recursion, counting `1` per
probe). -/
def bsearchSteps (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if lo < hi then
    1 + if p ((lo + hi) / 2) then bsearchSteps p lo ((lo + hi) / 2)
        else bsearchSteps p ((lo + hi) / 2 + 1) hi
  else 0
termination_by hi - lo
decreasing_by all_goals omega
-- @endregion

-- @region algorithms_and_efficiency.bsearch_steps_le
-- @provenance independent
/-- **Halving bound.** If the range has fewer than `2^k` points beyond `lo` (that is,
`hi - lo < 2^k`), binary search makes at most `k` probes. Each probe leaves a range of size at
most `⌊(hi - lo)/2⌋ < 2^(k-1)`; induction on `k`. -/
theorem bsearchSteps_le (p : ℕ → Bool) :
    ∀ k lo hi, hi - lo < 2 ^ k → bsearchSteps p lo hi ≤ k := by
  intro k
  induction k with
  | zero =>
    intro lo hi h
    have hlt : ¬ lo < hi := by simp at h; omega
    rw [bsearchSteps]
    simp [hlt]
  | succ k ih =>
    intro lo hi h
    rw [Nat.pow_succ] at h
    rw [bsearchSteps]
    split_ifs with hlt hp
    · have := ih lo ((lo + hi) / 2) (by omega)
      omega
    · have := ih ((lo + hi) / 2 + 1) hi (by omega)
      omega
    · omega
-- @endregion

-- @region algorithms_and_efficiency.bsearch_steps_le_log
-- @provenance independent
/-- **Binary search makes at most `⌊log₂ n⌋ + 1` probes** on a range of size `n = hi - lo`.
Since `n < 2^(⌊log₂ n⌋ + 1)` (`Nat.lt_pow_succ_log_self`), this is `bsearchSteps_le`. -/
theorem bsearchSteps_le_log (p : ℕ → Bool) (lo hi : ℕ) :
    bsearchSteps p lo hi ≤ Nat.log 2 (hi - lo) + 1 :=
  bsearchSteps_le p _ lo hi (Nat.lt_pow_succ_log_self Nat.one_lt_two _)
-- @endregion

/-! ### Euclid's algorithm -/

-- @region algorithms_and_efficiency.euclid
-- @provenance definition
/-- **Euclid's algorithm**: replace `(a, b)` by `(b, a mod b)` until `b = 0`; answer `a`. It
terminates because the second number strictly decreases (`a mod b < b`). -/
def euclid (a b : ℕ) : ℕ :=
  if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt a (by omega)
-- @endregion

-- @region algorithms_and_efficiency.euclid_eq_gcd
-- @provenance independent
/-- **Euclid's algorithm is correct**: `euclid a b = gcd(a, b)`. The loop invariant is that
the gcd of the current pair never changes: `gcd(a, b) = gcd(b, a mod b)` (from `Nat.gcd_rec`
and `Nat.gcd_comm`), and at the end `gcd(a, 0) = a`. Strong induction on `b`. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rw [euclid]
    split_ifs with hb
    · subst hb
      exact (Nat.gcd_zero_right a).symm
    · rw [ih (a % b) (Nat.mod_lt a (Nat.pos_of_ne_zero hb)) b]
      -- invariant: gcd(b, a mod b) = gcd(a mod b, b) = gcd(b, a) = gcd(a, b)
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]
-- @endregion

/-! ### Sorting -/

-- @region algorithms_and_efficiency.insertion_sort_sorted
-- @provenance library
/-- Insertion sort returns a **sorted** list: Mathlib's `List.pairwise_insertionSort` (sorted
means every earlier entry is `≤` every later one). -/
theorem insertionSort_sorted (l : List ℕ) :
    (l.insertionSort (· ≤ ·)).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ l
-- @endregion

-- @region algorithms_and_efficiency.insertion_sort_perm
-- @provenance library
/-- …which is a **rearrangement** of the input (`~` means "permutation of"):
Mathlib's `List.perm_insertionSort`. Together: insertion sort meets its specification. -/
theorem insertionSort_perm (l : List ℕ) : (l.insertionSort (· ≤ ·)).Perm l :=
  List.perm_insertionSort _ l
-- @endregion

-- @region algorithms_and_efficiency.decision_tree
-- @provenance definition
/-- A **binary decision tree**: each internal node is one yes/no comparison with two
subtrees for the two answers; each leaf is a final answer. -/
inductive DecisionTree where
  | leaf : DecisionTree
  | node : DecisionTree → DecisionTree → DecisionTree
-- @endregion

-- @region algorithms_and_efficiency.leaves
-- @provenance definition
/-- The number of leaves (possible final answers). -/
def DecisionTree.leaves : DecisionTree → ℕ
  | leaf => 1
  | node l r => l.leaves + r.leaves
-- @endregion

-- @region algorithms_and_efficiency.height
-- @provenance definition
/-- The height: the largest number of comparisons on any path from the root to a leaf, i.e.
the worst-case number of comparisons. -/
def DecisionTree.height : DecisionTree → ℕ
  | leaf => 0
  | node l r => max l.height r.height + 1
-- @endregion

-- @region algorithms_and_efficiency.leaves_le_two_pow_height
-- @provenance independent
/-- **A decision tree of height `h` has at most `2^h` leaves.** Each comparison at most
doubles the number of reachable outcomes: by induction,
`leaves ≤ 2^(height l) + 2^(height r) ≤ 2 · 2^(max) = 2^(max + 1)`. -/
theorem leaves_le_two_pow_height : ∀ t : DecisionTree, t.leaves ≤ 2 ^ t.height
  | .leaf => by simp [DecisionTree.leaves, DecisionTree.height]
  | .node l r => by
    have hl := leaves_le_two_pow_height l
    have hr := leaves_le_two_pow_height r
    have hl' : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right Nat.two_pos (le_max_left _ _)
    have hr' : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right Nat.two_pos (le_max_right _ _)
    simp only [DecisionTree.leaves, DecisionTree.height, Nat.pow_succ]
    omega
-- @endregion

-- @region algorithms_and_efficiency.sorting_lower_bound
-- @provenance independent
/-- **Lower bound for comparison sorting.** A decision tree that sorts `n` distinct items must
be able to give `n!` different answers (one for each order of the input), so it has at least
`n!` leaves. Then `n! ≤ 2^height`: in the worst case it makes at least `log₂ n!`
comparisons. -/
theorem sorting_lower_bound (n : ℕ) (t : DecisionTree) (h : n.factorial ≤ t.leaves) :
    n.factorial ≤ 2 ^ t.height :=
  h.trans (leaves_le_two_pow_height t)
-- @endregion

-- @region algorithms_and_efficiency.five_items_need_seven
-- @provenance independent
/-- **Sorting 5 items needs 7 comparisons** in the worst case: `5! = 120 > 64 = 2^6`, so a
tree with at least 120 leaves has height at least 7. (Seven comparisons also suffice, by a
clever method; that part is not formalised here.) -/
theorem five_items_need_seven (t : DecisionTree) (h : Nat.factorial 5 ≤ t.leaves) :
    7 ≤ t.height := by
  have h2 := sorting_lower_bound 5 t h
  by_contra hlt
  have h6 : 2 ^ t.height ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos (by omega)
  have h120 : Nat.factorial 5 = 120 := rfl
  omega
-- @endregion

end Lumenary.AlgorithmsAndEfficiency
