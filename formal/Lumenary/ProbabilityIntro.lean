/-
The Lumenary — formal mathematics
Probability with equally likely outcomes: sample spaces, events, the complement and addition
rules, the product rule for two independent stages, and exact dice calculations.

A finite sample space of equally likely outcomes is modelled as a list `S`, and an event as a
yes/no test `A : α → Bool` (the event is the set of outcomes that pass the test). The
probability of `A` is the number of outcomes in `A` divided by the number of outcomes in `S`,
computed exactly in core Lean's rational numbers `Rat`. The general rules are proved here by
induction on the list of outcomes (`@provenance independent`); a few steps apply core library
lemmas about lists. The dice results are computed by Lean and checked by `decide`.
Mathlib analogue: `PMF.uniformOfFinset`, `ProbabilityTheory.uniformOn` (the uniform measure
on a finite set), `MeasureTheory.prob_compl_eq_one_sub`, and `Finset.card_product`.
-/

namespace Lumenary.ProbabilityIntro

variable {α β : Type}

/-! ### Counting and probability -/

-- @region probability_intro.count
-- @provenance definition
/-- The number of outcomes in the list `S` that belong to the event `A`. -/
def count (S : List α) (A : α → Bool) : Nat := (S.filter A).length
-- @endregion

-- @region probability_intro.prob
-- @provenance definition
/-- **Probability with equally likely outcomes:** `P(A) = |A| / |S|`, the number of favourable
outcomes divided by the number of possible outcomes. -/
def prob (S : List α) (A : α → Bool) : Rat := (count S A : Rat) / (S.length : Rat)
-- @endregion

-- @region probability_intro.count_le_length
-- @provenance library
/-- An event has at most as many outcomes as the whole sample space. This applies core Lean's
`List.length_filter_le`. -/
theorem count_le_length (S : List α) (A : α → Bool) : count S A ≤ S.length :=
  List.length_filter_le A S
-- @endregion

-- @region probability_intro.prob_nonneg
-- @provenance independent
/-- Probabilities are never negative: a count divided by a count. -/
theorem prob_nonneg (S : List α) (A : α → Bool) : 0 ≤ prob S A := by
  unfold prob
  rw [Rat.div_def]
  apply Rat.mul_nonneg (Rat.natCast_nonneg)
  by_cases h : (S.length : Rat) = 0
  · rw [h, Rat.inv_zero]
    exact Rat.le_refl
  · have hpos : (0 : Rat) < S.length := Rat.lt_of_le_of_ne Rat.natCast_nonneg (Ne.symm h)
    exact Rat.le_of_lt (Rat.inv_pos.mpr hpos)
-- @endregion

-- @region probability_intro.prob_le_one
-- @provenance independent
/-- Probabilities are at most `1`: the event has at most as many outcomes as `S`. -/
theorem prob_le_one (S : List α) (A : α → Bool) : prob S A ≤ 1 := by
  unfold prob
  have hle : (count S A : Rat) ≤ S.length := Rat.natCast_le_natCast.mpr (count_le_length S A)
  by_cases h : S.length = 0
  · rw [h]
    simp [Rat.div_def]
    decide
  · have hpos : (0 : Rat) < S.length := Rat.natCast_pos.mpr (Nat.pos_of_ne_zero h)
    -- `c / n ≤ 1` means "not `1 < c / n`", i.e. not `1 · n < c`.
    rw [← Rat.not_lt, Rat.lt_div_iff hpos]
    grind
-- @endregion

-- @region probability_intro.prob_certain
-- @provenance independent
/-- The certain event (every outcome) has probability `1`, when there is at least one outcome. -/
theorem prob_certain (S : List α) (hS : S ≠ []) : prob S (fun _ => true) = 1 := by
  unfold prob count
  simp only [List.filter_eq_self.mpr (fun _ _ => rfl)]
  have hpos : (S.length : Rat) ≠ 0 := by
    have : S.length ≠ 0 := by
      intro h0
      exact hS (List.eq_nil_of_length_eq_zero h0)
    simpa using this
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel _ hpos
-- @endregion

-- @region probability_intro.count_compl
-- @provenance independent
/-- Every outcome is either in `A` or in "not `A`", never both:
`|A| + |not A| = |S|`. Proof by induction on the list of outcomes. -/
theorem count_compl (S : List α) (A : α → Bool) :
    count S A + count S (fun x => !A x) = S.length := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    unfold count at ih ⊢
    cases h : A a <;> simp [h] <;> omega
-- @endregion

-- @region probability_intro.prob_compl
-- @provenance independent
/-- **The complement rule:** `P(not A) = 1 - P(A)` (for a non-empty sample space).
Divide `|A| + |not A| = |S|` by `|S|`. -/
theorem prob_compl (S : List α) (hS : S ≠ []) (A : α → Bool) :
    prob S (fun x => !A x) = 1 - prob S A := by
  have hlen : S.length ≠ 0 := by
    intro h0
    exact hS (List.eq_nil_of_length_eq_zero h0)
  have hne : (S.length : Rat) ≠ 0 := by simpa using hlen
  have hsum : (count S A : Rat) + (count S (fun x => !A x) : Rat) = S.length := by
    have := count_compl S A
    have hc := congrArg (fun n : Nat => (n : Rat)) this
    simpa using hc
  unfold prob
  grind
-- @endregion

-- @region probability_intro.count_union_inter
-- @provenance independent
/-- **Counting a union.** Outcomes in `A` or `B`, plus outcomes in both, equals outcomes in `A`
plus outcomes in `B`: `|A ∪ B| + |A ∩ B| = |A| + |B|`. Induction on the list, checking the
four cases for whether the first outcome is in `A` and in `B`. -/
theorem count_union_inter (S : List α) (A B : α → Bool) :
    count S (fun x => A x || B x) + count S (fun x => A x && B x) = count S A + count S B := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    unfold count at ih ⊢
    cases hA : A a <;> cases hB : B a <;> simp [hA, hB] <;> omega
-- @endregion

-- @region probability_intro.prob_union
-- @provenance independent
/-- **The addition rule:** `P(A or B) = P(A) + P(B) - P(A and B)`. Divide `count_union_inter`
by `|S|`. When `A` and `B` cannot happen together, this is `P(A) + P(B)`. -/
theorem prob_union (S : List α) (A B : α → Bool) :
    prob S (fun x => A x || B x) = prob S A + prob S B - prob S (fun x => A x && B x) := by
  have h := congrArg (fun n : Nat => (n : Rat)) (count_union_inter S A B)
  push_cast at h
  unfold prob
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  grind
-- @endregion

/-! ### Two independent stages: the product rule -/

-- @region probability_intro.pairs
-- @provenance definition
/-- All ordered pairs `(a, b)` with `a` from `S` and `b` from `T`: the sample space of a
two-stage experiment, as in a table or a tree diagram. -/
def pairs (S : List α) (T : List β) : List (α × β) := S.flatMap (fun a => T.map (fun b => (a, b)))
-- @endregion

-- @region probability_intro.length_pairs
-- @provenance independent
/-- A two-stage experiment with `|S|` and `|T|` outcomes has `|S| · |T|` outcomes. -/
theorem length_pairs (S : List α) (T : List β) : (pairs S T).length = S.length * T.length := by
  induction S with
  | nil => simp [pairs]
  | cons a S ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]
-- @endregion

-- @region probability_intro.count_pairs
-- @provenance independent
/-- The pairs with first outcome in `A` and second outcome in `B` number `|A| · |B|`. -/
theorem count_pairs (S : List α) (T : List β) (A : α → Bool) (B : β → Bool) :
    count (pairs S T) (fun p => A p.1 && B p.2) = count S A * count T B := by
  induction S with
  | nil => simp [pairs, count]
  | cons a S ih =>
    unfold count pairs at ih ⊢
    simp only [List.flatMap_cons, List.filter_append, List.length_append] at ih ⊢
    rw [ih]
    cases hA : A a
    · simp [hA, List.filter_map, Function.comp_def]
    · simp [hA, List.filter_map, Function.comp_def]
      rw [Nat.succ_mul, Nat.add_comm]
-- @endregion

-- @region probability_intro.prob_pairs
-- @provenance independent
/-- **The product rule for independent stages:** if the second stage does not depend on the
first, then `P(A at stage 1 and B at stage 2) = P(A) · P(B)` — multiply along the branches of
the tree. -/
theorem prob_pairs (S : List α) (T : List β) (A : α → Bool) (B : β → Bool) :
    prob (pairs S T) (fun p => A p.1 && B p.2) = prob S A * prob T B := by
  unfold prob
  rw [count_pairs, length_pairs]
  push_cast
  by_cases hS : (S.length : Rat) = 0
  · rw [hS]
    simp [Rat.div_def]
  · by_cases hT : (T.length : Rat) = 0
    · rw [hT]
      simp [Rat.div_def]
    · grind
-- @endregion

/-! ### Dice and coins, computed exactly -/

-- @region probability_intro.die
-- @provenance definition
/-- The six equally likely outcomes of a fair die. -/
def die : List Nat := [1, 2, 3, 4, 5, 6]
-- @endregion

-- @region probability_intro.two_dice
-- @provenance definition
/-- The 36 equally likely outcomes of rolling two dice (a red one and a blue one). -/
def twoDice : List (Nat × Nat) := pairs die die
-- @endregion

-- @region probability_intro.prob_sum_seven
-- @provenance independent
/-- With two dice, a sum of `7` has probability `6/36 = 1/6`. Computed by Lean. -/
theorem prob_sum_seven : prob twoDice (fun p => p.1 + p.2 == 7) = 1 / 6 := by
  decide +kernel
-- @endregion

-- @region probability_intro.sums_not_equally_likely
-- @provenance independent
/-- The eleven possible sums are **not** equally likely: a sum of `2` has probability `1/36`,
but a sum of `7` has probability `1/6`. -/
theorem sums_not_equally_likely :
    prob twoDice (fun p => p.1 + p.2 == 2) = 1 / 36 ∧
    prob twoDice (fun p => p.1 + p.2 == 2) ≠ prob twoDice (fun p => p.1 + p.2 == 7) := by
  decide +kernel
-- @endregion

-- @region probability_intro.three_dice
-- @provenance definition
/-- The 216 equally likely outcomes of rolling three dice. -/
def threeDice : List (Nat × Nat × Nat) := pairs die (pairs die die)
-- @endregion

-- @region probability_intro.galileo
-- @provenance independent
/-- **Galileo's dice problem.** With three dice, a sum of `10` can be made in `27` ways but a
sum of `9` in only `25`, although each sum has six partitions into three numbers from 1 to 6.
Counted by Lean over all 216 outcomes. -/
theorem galileo :
    count threeDice (fun t => t.1 + t.2.1 + t.2.2 == 9) = 25 ∧
    count threeDice (fun t => t.1 + t.2.1 + t.2.2 == 10) = 27 := by
  decide
-- @endregion

-- @region probability_intro.at_least_one_head
-- @provenance independent
/-- **d'Alembert's question.** Toss two coins (`true` = heads). The outcomes HH, HT, TH, TT
are equally likely, so "at least one head" has probability `3/4`, not `2/3`. -/
theorem at_least_one_head : prob (pairs [true, false] [true, false]) (fun p => p.1 || p.2) = 3 / 4 := by
  decide +kernel
-- @endregion

end Lumenary.ProbabilityIntro
