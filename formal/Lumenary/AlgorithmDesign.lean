/-
The Lumenary — formal mathematics
Algorithm design and analysis: mergesort (correctness and a comparison bound), the
decision-tree lower bound for sorting, dynamic programming for the longest common subsequence,
a greedy algorithm that fails, and the graph facts behind Kruskal's algorithm.

What is proved here and what Lean and Mathlib provide. Core Lean's `List.mergeSort` comes with
proofs that its output is sorted and a permutation of its input (cited as *library*). The
*independent* declarations prove the lesson's analysis: mergesort's comparison count satisfies
`C(n) ≤ n ⌈log₂ n⌉`; a binary decision tree of height `h` has at most `2ʰ` leaves, so sorting
`n` items needs at least `log₂ n!` comparisons in the worst case; and the recursive
characterisation of the longest common subsequence used by dynamic programming is correct — the
value it computes is the length of a longest common subsequence. Kruskal's and Dijkstra's
algorithms are *not* formalised here; we cite Mathlib's theorem that a maximal acyclic subgraph
of a connected graph is a spanning tree, which is the structural fact behind Kruskal's output.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Lumenary.AlgorithmDesign

/-! ### Mergesort -/

-- @region algorithm_design.merge_sort_perm
-- @provenance library
/-- Mergesort returns a rearrangement (permutation, `~`) of its input. This applies core Lean's
`List.mergeSort_perm`; the comparison `le` is a Boolean-valued function. -/
theorem mergeSort_perm (l : List ℕ) : (l.mergeSort (fun a b => decide (a ≤ b))).Perm l :=
  List.mergeSort_perm l _
-- @endregion

-- @region algorithm_design.merge_sort_sorted
-- @provenance library
/-- Mergesort's output is sorted: every earlier entry is `≤` every later one (`List.Pairwise`).
This applies core Lean's `List.pairwise_mergeSort`, which needs the comparison to be transitive
and total. Together with `mergeSort_perm` this is the full specification of a sorting
algorithm. -/
theorem mergeSort_sorted (l : List ℕ) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Pairwise (fun a b => decide (a ≤ b)) :=
  List.pairwise_mergeSort
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
-- @endregion

-- @region algorithm_design.merge_comparisons
-- @provenance definition
/-- The worst-case number of comparisons made by mergesort on `n` items: sort the two halves
(sizes `⌊n/2⌋` and `⌈n/2⌉`), then merge, which takes at most `n − 1` comparisons. -/
def mergeComparisons (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else mergeComparisons (n / 2) + mergeComparisons (n - n / 2) + (n - 1)
decreasing_by all_goals omega
-- @endregion

-- @region algorithm_design.merge_comparisons_le
-- @provenance independent
/-- **Mergesort makes at most `n ⌈log₂ n⌉` comparisons.** Strong induction: with
`k = ⌈log₂ n⌉`, both halves have size at most `2ᵏ⁻¹`, so each needs at most (its size)·`(k − 1)`
comparisons, and `n (k − 1) + (n − 1) ≤ n k`. Mathlib's `Nat.clog 2 n` is `⌈log₂ n⌉`, and
`Nat.clog_of_two_le` gives `⌈log₂ n⌉ = ⌈log₂ ⌈n/2⌉⌉ + 1` for `n ≥ 2`. -/
theorem mergeComparisons_le (n : ℕ) : mergeComparisons n ≤ n * Nat.clog 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [mergeComparisons]
    split_ifs with h
    · exact Nat.zero_le _
    · rw [not_le] at h
      have hk : Nat.clog 2 n = Nat.clog 2 ((n + 2 - 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) h
      have hb : n - n / 2 = (n + 2 - 1) / 2 := by omega
      set j := Nat.clog 2 ((n + 2 - 1) / 2) with hj
      have ha : Nat.clog 2 (n / 2) ≤ j := Nat.clog_mono_right 2 (by omega)
      have h1 : mergeComparisons (n / 2) ≤ n / 2 * j :=
        (ih (n / 2) (by omega)).trans (Nat.mul_le_mul_left _ ha)
      have h2 : mergeComparisons (n - n / 2) ≤ (n - n / 2) * j := by
        have := ih (n - n / 2) (by omega)
        rw [hb] at this ⊢
        exact this
      rw [hk]
      calc mergeComparisons (n / 2) + mergeComparisons (n - n / 2) + (n - 1)
          ≤ n / 2 * j + (n - n / 2) * j + (n - 1) := by omega
        _ = n * j + (n - 1) := by
          rw [← Nat.add_mul, Nat.add_sub_cancel' (Nat.div_le_self n 2)]
        _ ≤ n * (j + 1) := by rw [Nat.mul_succ]; omega
-- @endregion

/-! ### The lower bound for comparison sorting -/

-- @region algorithm_design.decision_tree
-- @provenance definition
/-- A binary **decision tree**: each internal node is a comparison "is `aᵢ ≤ aⱼ`?" with a
subtree for each answer, and each leaf is an output. (We record only the shape, which is all
the counting argument needs.) -/
inductive DecisionTree where
  | leaf : DecisionTree
  | node : DecisionTree → DecisionTree → DecisionTree
-- @endregion

-- @region algorithm_design.decision_tree_leaves
-- @provenance definition
/-- The number of leaves (possible outcomes) of a decision tree. -/
def DecisionTree.leaves : DecisionTree → ℕ
  | .leaf => 1
  | .node l r => l.leaves + r.leaves
-- @endregion

-- @region algorithm_design.decision_tree_height
-- @provenance definition
/-- The height of a decision tree: the largest number of comparisons on a path from the root
to a leaf, i.e. the worst-case number of comparisons. -/
def DecisionTree.height : DecisionTree → ℕ
  | .leaf => 0
  | .node l r => max l.height r.height + 1
-- @endregion

-- @region algorithm_design.leaves_le_two_pow_height
-- @provenance independent
/-- **A tree of height `h` has at most `2ʰ` leaves.** Induction on the tree: each subtree of a
node has height at most `h − 1`, hence at most `2ʰ⁻¹` leaves, and `2ʰ⁻¹ + 2ʰ⁻¹ = 2ʰ`. -/
theorem leaves_le_two_pow_height (t : DecisionTree) : t.leaves ≤ 2 ^ t.height := by
  induction t with
  | leaf => simp [DecisionTree.leaves, DecisionTree.height]
  | node l r ihl ihr =>
    simp only [DecisionTree.leaves, DecisionTree.height]
    have hl : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    rw [pow_succ]
    omega
-- @endregion

-- @region algorithm_design.sorting_lower_bound
-- @provenance independent
/-- **The comparison lower bound.** A decision tree that sorts `n` distinct items must reach a
different leaf for each of the `n!` orderings, so it has at least `n!` leaves; therefore
`n! ≤ 2^(height)`, i.e. the worst case needs at least `log₂ n!` comparisons. -/
theorem sorting_lower_bound (n : ℕ) (t : DecisionTree) (h : n.factorial ≤ t.leaves) :
    n.factorial ≤ 2 ^ t.height :=
  h.trans (leaves_le_two_pow_height t)
-- @endregion

-- @region algorithm_design.five_items_need_seven
-- @provenance independent
/-- A concrete case: sorting `5` items needs at least `7` comparisons in the worst case,
because `5! = 120 > 64 = 2⁶`. (Seven comparisons are in fact enough for five items.) -/
theorem five_items_need_seven (t : DecisionTree) (h : (5 : ℕ).factorial ≤ t.leaves) :
    7 ≤ t.height := by
  have h2 := sorting_lower_bound 5 t h
  by_contra hlt
  rw [not_le] at hlt
  have : 2 ^ t.height ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : (5 : ℕ).factorial = 120 := rfl
  omega
-- @endregion

-- @region algorithm_design.four_items_need_five
-- @provenance independent
/-- Sorting `4` items needs at least `5` comparisons in the worst case: `4! = 24 > 16 = 2⁴`.
(Five comparisons suffice: mergesort uses at most `5` on four items.) -/
theorem four_items_need_five (t : DecisionTree) (h : (4 : ℕ).factorial ≤ t.leaves) :
    5 ≤ t.height := by
  have h2 := sorting_lower_bound 4 t h
  by_contra hlt
  rw [not_le] at hlt
  have : 2 ^ t.height ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (4 : ℕ).factorial = 24 := rfl
  omega
-- @endregion

/-! ### Dynamic programming: the longest common subsequence -/

section LCS

open List

variable {α : Type*} [DecidableEq α]

-- @region algorithm_design.lcs
-- @provenance definition
/-- The length of a longest common subsequence, by the recursion that dynamic programming
tabulates: drop the first letter of one word or of the other, or — if the first letters agree —
keep it in both. (The usual table only takes the third option when the letters agree; that it
loses nothing is a further lemma. Here all options are compared, which makes the proofs short.)
-/
def lcs : List α → List α → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys =>
    max (max (lcs xs (y :: ys)) (lcs (x :: xs) ys)) (if x = y then lcs xs ys + 1 else 0)
termination_by xs ys => xs.length + ys.length
-- @endregion

-- @region algorithm_design.lcs_optimal
-- @provenance independent
/-- **No common subsequence is longer than `lcs`.** By induction along the recursion: a
common subsequence `z :: zs` of `x :: xs` and `y :: ys` either avoids `x` (so it is a common
subsequence of `xs` and `y :: ys`), or avoids `y`, or uses both — and then `x = z = y` and `zs`
is a common subsequence of `xs` and `ys`. (`List.sublist_cons_iff` is the case split.) -/
theorem lcs_optimal : ∀ (xs ys zs : List α), zs <+ xs → zs <+ ys → zs.length ≤ lcs xs ys
  | [], _, zs, h1, _ => by simp [List.sublist_nil.mp h1, lcs]
  | _ :: _, [], zs, _, h2 => by simp [List.sublist_nil.mp h2, lcs]
  | x :: xs, y :: ys, zs, h1, h2 => by
    rw [lcs]
    rcases List.sublist_cons_iff.mp h1 with h1' | ⟨r, rfl, hr1⟩
    · have := lcs_optimal xs (y :: ys) zs h1' h2
      omega
    · rcases List.sublist_cons_iff.mp h2 with h2' | ⟨r', hr', hr2⟩
      · have := lcs_optimal (x :: xs) ys (x :: r) h1 h2'
        omega
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr'
        have := lcs_optimal xs ys r hr1 hr2
        rw [ite_eq_left rfl, List.length_cons]
        omega
termination_by xs ys => xs.length + ys.length
-- @endregion

-- @region algorithm_design.lcs_achieved
-- @provenance independent
/-- **Some common subsequence has length exactly `lcs`.** By induction along the same recursion,
building the subsequence from whichever option attains the maximum. Together with
`lcs_optimal`, the recursion computes the length of a *longest* common subsequence. -/
theorem lcs_achieved :
    ∀ (xs ys : List α), ∃ zs, zs <+ xs ∧ zs <+ ys ∧ zs.length = lcs xs ys
  | [], _ => ⟨[], List.nil_sublist _, List.nil_sublist _, by simp [lcs]⟩
  | _ :: _, [] => ⟨[], List.nil_sublist _, List.nil_sublist _, by simp [lcs]⟩
  | x :: xs, y :: ys => by
    obtain ⟨a, ha1, ha2, ha⟩ := lcs_achieved xs (y :: ys)
    obtain ⟨b, hb1, hb2, hb⟩ := lcs_achieved (x :: xs) ys
    obtain ⟨c, hc1, hc2, hc⟩ := lcs_achieved xs ys
    rw [lcs]
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl]
      by_cases h3 : max (lcs xs (x :: ys)) (lcs (x :: xs) ys) ≤ lcs xs ys + 1
      · exact ⟨x :: c, hc1.cons_cons x, hc2.cons_cons x, by simp [hc, max_eq_right h3]⟩
      · rw [not_le] at h3
        rw [max_eq_left h3.le]
        by_cases h4 : lcs (x :: xs) ys ≤ lcs xs (x :: ys)
        · exact ⟨a, ha1.cons x, ha2, by rw [ha, max_eq_left h4]⟩
        · rw [not_le] at h4
          exact ⟨b, hb1, hb2.cons x, by rw [hb, max_eq_right h4.le]⟩
    · rw [ite_eq_right hxy, max_eq_left (Nat.zero_le _)]
      by_cases h4 : lcs (x :: xs) ys ≤ lcs xs (y :: ys)
      · exact ⟨a, ha1.cons x, ha2, by rw [ha, max_eq_left h4]⟩
      · rw [not_le] at h4
        exact ⟨b, hb1, hb2.cons y, by rw [hb, max_eq_right h4.le]⟩
termination_by xs ys => xs.length + ys.length
-- @endregion

-- @region algorithm_design.lcs_example
-- @provenance independent
/-- The example from the lesson: `ABCBDAB` and `BDCABA` have a longest common subsequence of
length `4` (for instance `BCBA`). Lean's kernel evaluates the recursion (`decide +kernel`). -/
theorem lcs_example : lcs "ABCBDAB".toList "BDCABA".toList = 4 := by
  decide +kernel
-- @endregion

end LCS

-- @region algorithm_design.fib_pair
-- @provenance definition
/-- Dynamic programming in miniature: compute the pair `(Fₙ, Fₙ₊₁)` by remembering the two most
recent values, `n` additions in all, instead of the exponential naive recursion. -/
def fibPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)
-- @endregion

-- @region algorithm_design.fib_pair_eq
-- @provenance independent
/-- The remembered pair is correct: `fibPair n = (Fₙ, Fₙ₊₁)`, by induction on `n` using
`Fₙ₊₂ = Fₙ + Fₙ₊₁` (Mathlib's `Nat.fib_add_two`). -/
theorem fibPair_eq (n : ℕ) : fibPair n = (Nat.fib n, Nat.fib (n + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih => simp [fibPair, ih, Nat.fib_add_two]
-- @endregion

/-! ### Greedy algorithms -/

-- @region algorithm_design.greedy_coins
-- @provenance definition
/-- The greedy change-making algorithm, with the coin values listed from largest to smallest:
use as many of the largest coin as possible, then continue with the remainder. Returns the
number of coins used. -/
def greedyCoins : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, amount => amount / c + greedyCoins cs (amount % c)
-- @endregion

-- @region algorithm_design.greedy_not_optimal
-- @provenance independent
/-- **A greedy algorithm needs a proof.** With coins `4, 3, 1`, greedy pays `6` as `4 + 1 + 1`
(three coins), but `3 + 3` uses only two. (For coins `25, 10, 5, 1` greedy happens to be
optimal; that is a theorem about those particular values.) -/
theorem greedy_not_optimal :
    greedyCoins [4, 3, 1] 6 = 3 ∧
      ∃ l : List ℕ, (∀ c ∈ l, c ∈ [4, 3, 1]) ∧ l.sum = 6 ∧ l.length = 2 :=
  ⟨by decide, [3, 3], by decide, rfl, rfl⟩
-- @endregion

/-! ### Spanning trees -/

-- @region algorithm_design.maximal_acyclic_is_tree
-- @provenance library
/-- **What Kruskal's algorithm builds.** Kruskal adds edges of a connected graph `G` in order of
weight, skipping any edge that would close a cycle, so its output is a *maximal* acyclic
subgraph of `G`. Mathlib's `SimpleGraph.Connected.maximal_le_isAcyclic_iff_isTree` says that such
a subgraph is exactly a spanning tree. (That it has *minimum* weight is the cut-property proof
in the lesson, not formalised here.) -/
theorem maximal_acyclic_is_tree {V : Type*} {G T : SimpleGraph V} (hG : G.Connected)
    (hT : T ≤ G) : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) T ↔ T.IsTree :=
  hG.maximal_le_isAcyclic_iff_isTree hT
-- @endregion

-- @region algorithm_design.tree_edges
-- @provenance library
/-- A tree on `n` vertices has exactly `n − 1` edges (stated as `|E| + 1 = |V|`), so Kruskal's
algorithm adds exactly `n − 1` edges. This applies Mathlib's `SimpleGraph.IsTree.card_edgeFinset`. -/
theorem tree_edges {V : Type*} [Fintype V] {T : SimpleGraph V} [Fintype T.edgeSet]
    (hT : T.IsTree) : T.edgeFinset.card + 1 = Fintype.card V :=
  hT.card_edgeFinset
-- @endregion

end Lumenary.AlgorithmDesign
