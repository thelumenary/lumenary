/-
The Lumenary — formal mathematics
Conditional probability and independence: the addition and multiplication rules, Bayes' theorem,
the law of total probability, and why "independent" and "mutually exclusive" are different.

We work with a *finite probability space*: finitely many outcomes, each with a rational
probability, the probabilities adding up to `1`. This covers every example in the lesson (dice,
cards, diagnostic tests) and keeps the arithmetic exact.

Proved here (`@provenance independent`): the complement and addition rules; the multiplication
rule `P(A ∩ B) = P(A | B) P(B)`; Bayes' theorem; the law of total probability for any finite
partition, and its two-case form; Bayes' theorem with a total-probability denominator, applied to
a diagnostic test with a 1% base rate; independence as "conditioning on `B` does not change the
probability of `A`"; that mutually exclusive events of positive probability are never
independent; that independence survives taking a complement; and two dice examples, one
independent and one not.

From Mathlib (`@provenance library`): Bayes' theorem `ProbabilityTheory.cond_eq_inv_mul_cond_mul`
and the two-case law of total probability `ProbabilityTheory.cond_add_cond_compl_eq`, stated for
arbitrary (measure-theoretic) probability measures, the setting of university probability.
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Lumenary.ProbabilityRules

open Finset

/-! ### Finite probability spaces -/

-- @region probability_rules.fin_prob
-- @provenance definition
/-- A **finite probability space** on a finite type of outcomes `Ω`: a probability `p ω ≥ 0`
for each outcome, adding up to `1`. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  /-- the probability of each single outcome -/
  p : Ω → ℚ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_eq_one : ∑ ω, p ω = 1
-- @endregion

-- @region probability_rules.prob
-- @provenance definition
/-- The **probability of an event** `A` (a set of outcomes): the sum of the probabilities of
its outcomes. -/
def FinProb.P {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (A : Finset Ω) : ℚ :=
  ∑ ω ∈ A, μ.p ω
-- @endregion

-- @region probability_rules.cond
-- @provenance definition
/-- **Conditional probability:** `P(A | B) = P(A ∩ B) / P(B)`, the probability of `A` when we
know that `B` happened. It is meant to be used only when `P(B) > 0`; Lean's convention `x / 0 = 0`
gives it the meaningless value `0` otherwise, and every theorem below that needs `P(B) ≠ 0`
assumes it. -/
def FinProb.cond {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A B : Finset Ω) : ℚ :=
  μ.P (A ∩ B) / μ.P B
-- @endregion

-- @region probability_rules.indep
-- @provenance definition
/-- Events `A` and `B` are **independent** when `P(A ∩ B) = P(A) P(B)`. -/
def FinProb.Indep {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A B : Finset Ω) :
    Prop :=
  μ.P (A ∩ B) = μ.P A * μ.P B
-- @endregion

namespace FinProb

/-! ### The basic rules -/

-- @region probability_rules.prob_compl
-- @provenance independent
/-- **Complement rule:** `P(Aᶜ) = 1 − P(A)`. The outcomes of `A` and of `Aᶜ` together are all
the outcomes, whose probabilities add up to `1`. -/
theorem prob_compl {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A : Finset Ω) :
    μ.P Aᶜ = 1 - μ.P A := by
  have h := sum_add_sum_compl A μ.p
  rw [μ.sum_eq_one] at h
  unfold P
  linarith
-- @endregion

-- @region probability_rules.prob_union
-- @provenance independent
/-- **Addition rule:** `P(A ∪ B) = P(A) + P(B) − P(A ∩ B)`: adding `P(A)` and `P(B)` counts the
outcomes of `A ∩ B` twice. -/
theorem prob_union {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A B : Finset Ω) :
    μ.P (A ∪ B) = μ.P A + μ.P B - μ.P (A ∩ B) := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := μ.p)
  unfold P
  linarith
-- @endregion

-- @region probability_rules.mul_rule
-- @provenance independent
/-- **Multiplication rule:** `P(A ∩ B) = P(A | B) · P(B)` whenever `P(B) ≠ 0` — "multiply along
the branches of the tree". It is the definition of `P(A | B)`, rearranged. -/
theorem mul_rule {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A B : Finset Ω)
    (hB : μ.P B ≠ 0) : μ.P (A ∩ B) = μ.cond A B * μ.P B := by
  rw [cond, div_mul_cancel₀ _ hB]
-- @endregion

/-! ### Bayes' theorem and total probability -/

-- @region probability_rules.bayes
-- @provenance independent
/-- **Bayes' theorem:** `P(A | B) = P(B | A) P(A) / P(B)` when `P(A) ≠ 0`. Both `P(A | B) P(B)`
and `P(B | A) P(A)` equal `P(A ∩ B)`: the same probability, computed along two different
trees. -/
theorem bayes {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A B : Finset Ω)
    (hA : μ.P A ≠ 0) : μ.cond A B = μ.cond B A * μ.P A / μ.P B := by
  rw [← mul_rule μ B A hA, inter_comm, cond]
-- @endregion

-- @region probability_rules.total_probability
-- @provenance independent
/-- **Law of total probability.** If the events `B i` (for `i ∈ s`) are pairwise disjoint,
cover every outcome, and each has positive probability, then `P(A) = Σᵢ P(A | Bᵢ) P(Bᵢ)`.
Proof: `A` is the disjoint union of the pieces `A ∩ Bᵢ`, so `P(A) = Σᵢ P(A ∩ Bᵢ)`, and each
piece is `P(A | Bᵢ) P(Bᵢ)` by the multiplication rule. -/
theorem total_probability {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω)
    (A : Finset Ω) (s : Finset ι) (B : ι → Finset Ω) (hdisj : (s : Set ι).PairwiseDisjoint B)
    (hcover : ∀ ω, ∃ i ∈ s, ω ∈ B i) (hpos : ∀ i ∈ s, μ.P (B i) ≠ 0) :
    μ.P A = ∑ i ∈ s, μ.cond A (B i) * μ.P (B i) := by
  -- `A` is the disjoint union of the pieces `A ∩ B i`
  have hA : A = s.biUnion fun i => A ∩ B i := by
    ext ω
    simp only [mem_biUnion, mem_inter]
    constructor
    · intro hω
      obtain ⟨i, hi, hωi⟩ := hcover ω
      exact ⟨i, hi, hω, hωi⟩
    · rintro ⟨i, -, hω, -⟩
      exact hω
  have hdisj' : (s : Set ι).PairwiseDisjoint fun i => A ∩ B i := by
    intro i hi j hj hij
    exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hi hj hij)
  calc μ.P A = ∑ ω ∈ s.biUnion (fun i => A ∩ B i), μ.p ω := by rw [← hA]; rfl
    _ = ∑ i ∈ s, μ.P (A ∩ B i) := sum_biUnion hdisj'
    _ = ∑ i ∈ s, μ.cond A (B i) * μ.P (B i) :=
      sum_congr rfl fun i hi => mul_rule μ A (B i) (hpos i hi)
-- @endregion

-- @region probability_rules.total_probability_two
-- @provenance independent
/-- **Total probability with two cases:** `P(A) = P(A | B) P(B) + P(A | Bᶜ) P(Bᶜ)` when
`0 < P(B) < 1`. Either `B` happens or it does not. -/
theorem total_probability_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω)
    (A B : Finset Ω) (hB : μ.P B ≠ 0) (hBc : μ.P Bᶜ ≠ 0) :
    μ.P A = μ.cond A B * μ.P B + μ.cond A Bᶜ * μ.P Bᶜ := by
  rw [← mul_rule μ A B hB, ← mul_rule μ A Bᶜ hBc]
  have h := sum_filter_add_sum_filter_not A (· ∈ B) μ.p
  have e1 : A.filter (· ∈ B) = A ∩ B := by ext; simp [mem_inter]
  have e2 : A.filter (· ∉ B) = A ∩ Bᶜ := by ext; simp [mem_inter]
  rw [e1, e2] at h
  unfold P
  linarith
-- @endregion

-- @region probability_rules.bayes_total
-- @provenance independent
/-- **Bayes' theorem for a test result.** With `D` = "has the condition" and `T` = "tests
positive",
`P(D | T) = P(T | D) P(D) / (P(T | D) P(D) + P(T | Dᶜ) P(Dᶜ))`:
Bayes' theorem with the denominator `P(T)` expanded by total probability. -/
theorem bayes_total {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (D T : Finset Ω)
    (hD : μ.P D ≠ 0) (hDc : μ.P Dᶜ ≠ 0) :
    μ.cond D T = μ.cond T D * μ.P D / (μ.cond T D * μ.P D + μ.cond T Dᶜ * μ.P Dᶜ) := by
  rw [bayes μ D T hD, ← total_probability_two μ T D hD hDc]
-- @endregion

-- @region probability_rules.base_rate_example
-- @provenance independent
/-- **A positive test is not a diagnosis.** Suppose `1%` of people have a condition, the test
detects it `95%` of the time (`P(T | D) = 0.95`), and it wrongly flags `5%` of healthy people
(`P(T | Dᶜ) = 0.05`). Then a positive result means only `P(D | T) = 19/118 ≈ 16%`. The base rate
`P(D) = 0.01` matters as much as the accuracy of the test. -/
theorem base_rate_example {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω)
    (D T : Finset Ω) (hD : μ.P D = 1 / 100) (hTD : μ.cond T D = 95 / 100)
    (hTDc : μ.cond T Dᶜ = 5 / 100) : μ.cond D T = 19 / 118 := by
  have hDc : μ.P Dᶜ = 99 / 100 := by rw [prob_compl, hD]; norm_num
  rw [bayes_total μ D T (by rw [hD]; norm_num) (by rw [hDc]; norm_num), hD, hDc, hTD, hTDc]
  norm_num
-- @endregion

/-! ### Independence -/

-- @region probability_rules.indep_iff_cond
-- @provenance independent
/-- **Independence means "knowing `B` tells us nothing about `A`":** when `P(B) ≠ 0`, `A` and
`B` are independent exactly when `P(A | B) = P(A)`. -/
theorem indep_iff_cond {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω)
    (A B : Finset Ω) (hB : μ.P B ≠ 0) : μ.Indep A B ↔ μ.cond A B = μ.P A := by
  rw [Indep, cond, div_eq_iff hB]
-- @endregion

-- @region probability_rules.exclusive_not_indep
-- @provenance independent
/-- **Mutually exclusive is the opposite of independent.** If `A` and `B` cannot both happen
and each has positive probability, they are *not* independent: `P(A ∩ B) = 0`, but
`P(A) P(B) > 0`. Learning that `B` happened tells us for certain that `A` did not. -/
theorem exclusive_not_indep {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω)
    (A B : Finset Ω) (hdisj : A ∩ B = ∅) (hA : μ.P A ≠ 0) (hB : μ.P B ≠ 0) :
    ¬ μ.Indep A B := by
  intro h
  rw [Indep, hdisj] at h
  have h0 : μ.P ∅ = 0 := sum_empty
  rw [h0] at h
  exact mul_ne_zero hA hB h.symm
-- @endregion

-- @region probability_rules.indep_compl
-- @provenance independent
/-- **Independence survives complements:** if `A` and `B` are independent, so are `A` and
`Bᶜ`. Proof: `P(A ∩ Bᶜ) = P(A) − P(A ∩ B) = P(A) − P(A) P(B) = P(A)(1 − P(B)) = P(A) P(Bᶜ)`. -/
theorem indep_compl {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FinProb Ω) (A B : Finset Ω)
    (h : μ.Indep A B) : μ.Indep A Bᶜ := by
  have hsplit := sum_filter_add_sum_filter_not A (· ∈ B) μ.p
  have e1 : A.filter (· ∈ B) = A ∩ B := by ext; simp [mem_inter]
  have e2 : A.filter (· ∉ B) = A ∩ Bᶜ := by ext; simp [mem_inter]
  rw [e1, e2] at hsplit
  have hc := prob_compl μ B
  unfold Indep at h ⊢
  rw [hc]
  unfold P at *
  rw [mul_sub, mul_one]
  linarith
-- @endregion

/-! ### Equally likely outcomes: two dice -/

-- @region probability_rules.uniform
-- @provenance definition
/-- **Equally likely outcomes:** each of the `|Ω|` outcomes has probability `1/|Ω|`. -/
def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinProb Ω where
  p _ := 1 / Fintype.card Ω
  nonneg _ := by positivity
  sum_eq_one := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    have : (Fintype.card Ω : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
-- @endregion

-- @region probability_rules.uniform_prob
-- @provenance independent
/-- With equally likely outcomes, `P(A) = |A| / |Ω|`: probability is counting, divided. -/
theorem uniform_P {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Finset Ω) :
    (uniform Ω).P A = #A / Fintype.card Ω := by
  simp only [P, uniform, sum_const, nsmul_eq_mul]
  ring
-- @endregion

-- @region probability_rules.uniform_indep_iff
-- @provenance independent
/-- With equally likely outcomes, independence is a statement about counting:
`A` and `B` are independent exactly when `|A ∩ B| · |Ω| = |A| · |B|`. -/
theorem uniform_indep_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A B : Finset Ω) : (uniform Ω).Indep A B ↔ #(A ∩ B) * Fintype.card Ω = #A * #B := by
  have hN : (Fintype.card Ω : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Indep, uniform_P, uniform_P, uniform_P, div_mul_div_comm,
    div_eq_div_iff hN (mul_ne_zero hN hN)]
  constructor
  · intro h
    have h' : ((#(A ∩ B) : ℚ) * Fintype.card Ω) * Fintype.card Ω =
        ((#A : ℚ) * #B) * Fintype.card Ω := by
      rw [mul_assoc]
      exact h
    exact_mod_cast mul_right_cancel₀ hN h'
  · intro h
    have h' : ((#(A ∩ B) : ℚ) * Fintype.card Ω) = (#A : ℚ) * #B := by exact_mod_cast h
    rw [← mul_assoc, h']
-- @endregion

-- @region probability_rules.dice_even_seven
-- @provenance independent
/-- **Two dice, independent events.** Roll two fair dice (outcome `(i, j)` means faces `i + 1`
and `j + 1`). "The first die is even" and "the total is 7" are independent:
`P(both) = 3/36 = 1/12 = (18/36)(6/36)`. Lean counts the outcomes: `3 · 36 = 18 · 6`. -/
theorem dice_even_seven :
    (uniform (Fin 6 × Fin 6)).Indep
      {ω | (ω.1.val + 1) % 2 = 0} {ω | ω.1.val + ω.2.val + 2 = 7} :=
  (uniform_indep_iff _ _).2 (by decide)
-- @endregion

-- @region probability_rules.dice_six_high
-- @provenance independent
/-- **Two dice, dependent events.** "The first die shows 6" and "the total is at least 10" are
*not* independent: `P(both) = 3/36 = 1/12`, but `P(first is 6) P(total ≥ 10) = (1/6)(1/6) = 1/36`.
Knowing that the first die is a 6 makes a high total three times as likely. Lean counts:
`3 · 36 ≠ 6 · 6`. -/
theorem dice_six_high :
    ¬ (uniform (Fin 6 × Fin 6)).Indep
      {ω | ω.1.val + 1 = 6} {ω | 10 ≤ ω.1.val + ω.2.val + 2} := by
  rw [uniform_indep_iff]
  decide
-- @endregion

end FinProb

/-! ### The same theorems in Mathlib's measure-theoretic probability -/

open MeasureTheory ProbabilityTheory

-- @region probability_rules.bayes_library
-- @provenance library
/-- **Bayes' theorem** for any finite measure (in particular any probability measure), with
`μ[t | s]` the conditional probability of `t` given `s`:
`P(t | s) = P(s)⁻¹ · P(s | t) · P(t)`. Probabilities here take values in `[0, ∞]`, so no
positivity hypothesis is needed: `0⁻¹ = ∞` and the conventions are arranged to make the identity
true. This applies Mathlib's `ProbabilityTheory.cond_eq_inv_mul_cond_mul`. -/
theorem bayes_library {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t :=
  cond_eq_inv_mul_cond_mul hs ht μ
-- @endregion

-- @region probability_rules.total_probability_library
-- @provenance library
/-- **Total probability with two cases**, for any finite measure:
`P(t | s) P(s) + P(t | sᶜ) P(sᶜ) = P(t)`. This applies Mathlib's
`ProbabilityTheory.cond_add_cond_compl_eq`. -/
theorem total_probability_library {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {s t : Set Ω} (hs : MeasurableSet s) :
    μ[t | s] * μ s + μ[t | sᶜ] * μ sᶜ = μ t :=
  cond_add_cond_compl_eq hs μ
-- @endregion

end Lumenary.ProbabilityRules
