/-
The Lumenary — formal mathematics
Research ethics and attribution: what a proof assistant can and cannot check about the record.

Ethics is not a formal subject, but several claims in the lesson are mathematical and can be
checked by machine. Formalised here: (1) a toy model of "several checkers agree", showing that when
the checkers' errors are correlated, no number of agreements pushes confidence in a proof past a
ceiling below certainty, whereas independent checkers would drive it to 1; (2) a famous published
error and its correction — the claim (Cauchy, 1821) that a pointwise limit of continuous functions
is continuous is false, and the corrected theorem with uniform convergence is Mathlib's
`TendstoUniformly.continuous`; (3) claims in the historical record that were wrong and were later
corrected by others, whose work deserves credit: Mersenne's list of primes `2^p − 1`, Euler's
conjecture on sums of like powers (refuted by Lander and Parkin, 1966) and Fermat's conjecture
that every number `2^(2^n) + 1` is prime (refuted by Euler, 1732); (4) the alphabetical convention
for author lists: the sorted list depends only on who the authors are. What a formal proof cannot
check — who had an idea first, who contributed what, whether a source was cited — is the subject of
the rest of the lesson.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Fermat
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Sort

namespace Lumenary.ResearchEthics

open Filter Topology

/-! ### Agreement among checkers -/

-- @region research_ethics.posterior
-- @provenance definition
/-- A toy model of `k` checkers (people, programs or AI systems) who all accept a proof.
A correct proof is always accepted. A flawed proof is accepted by each checker with probability
`q`; with probability `ρ` the checkers share a blind spot and give one common verdict, otherwise
they judge independently. So all `k` accept a flawed proof with probability `ρq + (1 − ρ)qᵏ`, and
by Bayes' rule the probability that the proof is correct, given `k` acceptances and prior
probability `prior`, is the value below. -/
noncomputable def posterior (prior q ρ : ℝ) (k : ℕ) : ℝ :=
  prior / (prior + (1 - prior) * (ρ * q + (1 - ρ) * q ^ k))
-- @endregion

-- @region research_ethics.posterior_le_ceiling
-- @provenance independent
/-- **Correlated agreement has a ceiling.** However many checkers agree, the posterior never
exceeds `prior / (prior + (1 − prior)ρq)`: the term `(1 − ρ)qᵏ` can only shrink to zero, while the
shared blind spot `ρq` remains. -/
theorem posterior_le_ceiling {prior q ρ : ℝ} (hp₀ : 0 < prior) (hp₁ : prior ≤ 1) (hq : 0 ≤ q)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (k : ℕ) :
    posterior prior q ρ k ≤ prior / (prior + (1 - prior) * (ρ * q)) := by
  unfold posterior
  have h1 : 0 ≤ 1 - prior := by linarith
  have h2 : 0 ≤ (1 - ρ) * q ^ k := mul_nonneg (by linarith) (pow_nonneg hq k)
  apply div_le_div_of_nonneg_left hp₀.le
  · have : 0 ≤ (1 - prior) * (ρ * q) := mul_nonneg h1 (mul_nonneg hρ₀ hq)
    linarith
  · have : (1 - prior) * (ρ * q) ≤ (1 - prior) * (ρ * q + (1 - ρ) * q ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h1
    linarith
-- @endregion

-- @region research_ethics.ceiling_lt_one
-- @provenance independent
/-- The ceiling is strictly below certainty as soon as the prior is below 1 and a shared blind
spot is possible (`ρq > 0`). -/
theorem ceiling_lt_one {prior q ρ : ℝ} (hp₀ : 0 < prior) (hp₁ : prior < 1) (hρq : 0 < ρ * q) :
    prior / (prior + (1 - prior) * (ρ * q)) < 1 := by
  have h : 0 < (1 - prior) * (ρ * q) := mul_pos (by linarith) hρq
  rw [div_lt_one (by linarith)]
  linarith
-- @endregion

-- @region research_ethics.independent_tendsto_one
-- @provenance independent
/-- By contrast, if the checkers err **independently** (`ρ = 0`) and each sometimes rejects a
flawed proof (`q < 1`), the posterior tends to `1` as the number of agreeing checkers grows,
because `qᵏ → 0`. Independence is exactly what cannot be assumed for systems with shared
training data or shared habits of thought. -/
theorem independent_tendsto_one {prior q : ℝ} (hp₀ : 0 < prior) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Tendsto (fun k : ℕ => posterior prior q 0 k) atTop (𝓝 1) := by
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  have hfun : (fun k : ℕ => posterior prior q 0 k) =
      fun k => prior / (prior + (1 - prior) * q ^ k) := by
    funext k
    simp [posterior]
  rw [hfun]
  have hden : Tendsto (fun k : ℕ => prior + (1 - prior) * q ^ k) atTop
      (𝓝 (prior + (1 - prior) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)
  rw [mul_zero, add_zero] at hden
  have hlim := (tendsto_const_nhds (x := prior)).div hden hp₀.ne'
  rw [div_self hp₀.ne'] at hlim
  exact hlim
-- @endregion

/-! ### A published error and its correction -/

-- @region research_ethics.cauchy_sum_theorem_false
-- @provenance independent
/-- **Cauchy's "sum theorem" is false as stated.** Cauchy's *Cours d'analyse* (1821) asserted that
a convergent series of continuous functions has a continuous sum; Abel (1826) pointed out an
exception. Here is a simple counterexample to the pointwise version: `fₙ(x) = c(x)ⁿ`, where
`c(x) = max 0 (min x 1)` clamps `x` to `[0, 1]`, is continuous for every `n`, but `fₙ(x)` tends to
`0` for `x < 1` and to `1` for `x ≥ 1`, a discontinuous limit (by the intermediate value
theorem, a continuous function on `ℝ` taking the values 0 and 1 also takes the value 1/2). -/
theorem cauchy_sum_theorem_false :
    ¬ ∀ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ), (∀ n, Continuous (f n)) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) → Continuous g := by
  intro H
  let c : ℝ → ℝ := fun x => max 0 (min x 1)
  let g : ℝ → ℝ := fun x => if 1 ≤ x then 1 else 0
  have hcont : Continuous g := by
    refine H (fun n x => c x ^ n) g (fun n => ?_) (fun x => ?_)
    · exact (continuous_const.max (continuous_id.min continuous_const)).pow n
    · by_cases hx : 1 ≤ x
      · have hc : c x = 1 := by simp [c, min_eq_right hx]
        simp only [hc, one_pow, g, ite_eq_left hx]
        exact tendsto_const_nhds
      · have hc₀ : 0 ≤ c x := le_max_left _ _
        have hc₁ : c x < 1 := max_lt one_pos (min_lt_iff.2 (Or.inl (not_le.1 hx)))
        simp only [g, ite_eq_right hx]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc₁
  -- A continuous `g` with `g 0 = 0` and `g 1 = 1` takes the value `1/2`.
  obtain ⟨x, hx⟩ := intermediate_value_univ 0 1 hcont
    (show (1 / 2 : ℝ) ∈ Set.Icc (g 0) (g 1) by norm_num [g])
  simp only [g] at hx
  split_ifs at hx <;> norm_num at hx
-- @endregion

-- @region research_ethics.uniform_limit_continuous
-- @provenance library
/-- **The corrected theorem.** A *uniform* limit of continuous functions is continuous — the
hypothesis that Seidel and Stokes (1847) identified and Weierstrass made central. This is
Mathlib's `TendstoUniformly.continuous`. -/
theorem uniform_limit_continuous {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, Continuous (f n))
    (hu : TendstoUniformly f g atTop) : Continuous g :=
  hu.continuous (Eventually.of_forall hf).frequently
-- @endregion

/-! ### Claims in the record, checked -/

-- @region research_ethics.mersenne_list_corrected
-- @provenance library
/-- **Mersenne's list, corrected.** In 1644 Mersenne claimed that, for `p ≤ 257`, `2^p − 1` is
prime exactly for `p = 2, 3, 5, 7, 13, 17, 19, 31, 67, 127, 257`. He was wrong about five
exponents: `2^61 − 1`, `2^89 − 1` and `2^107 − 1` are prime, and `2^67 − 1` and `2^257 − 1` are
not. Each fact is proved by applying Mathlib's Lucas–Lehmer theorem
(`lucas_lehmer_sufficiency`, `lucas_lehmer_necessity`), with `norm_num` running the test. -/
theorem mersenne_list_corrected :
    (mersenne 61).Prime ∧ ¬ (mersenne 67).Prime ∧ (mersenne 89).Prime ∧
      (mersenne 107).Prime ∧ ¬ (mersenne 257).Prime := by
  refine ⟨lucas_lehmer_sufficiency _ (by simp) (by norm_num), fun h => ?_,
    lucas_lehmer_sufficiency _ (by simp) (by norm_num),
    lucas_lehmer_sufficiency _ (by simp) (by norm_num), fun h => ?_⟩
  · have := lucas_lehmer_necessity 67 (by norm_num) h
    norm_num at this
  · have := lucas_lehmer_necessity 257 (by norm_num) h
    norm_num at this
-- @endregion

-- @region research_ethics.cole_factorisation
-- @provenance independent
/-- **Cole's factorisation (1903).** Frank Nelson Cole exhibited the factors of `2^67 − 1`,
showing directly that Mersenne's `67` was wrong: `2^67 − 1 = 193707721 · 761838257287`. -/
theorem cole_factorisation : mersenne 67 = 193707721 * 761838257287 := by
  norm_num [mersenne]
-- @endregion

-- @region research_ethics.euler_conjecture_false
-- @provenance independent
/-- **Euler's conjecture on sums of like powers is false** (Lander and Parkin, 1966, found by a
computer search): Euler conjectured (1769) that at least `k` positive `k`-th powers are needed to
sum to a `k`-th power, but `27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵`. -/
theorem euler_conjecture_false :
    ¬ ∀ a b c d e : ℕ, 0 < a → 0 < b → 0 < c → 0 < d → a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 ≠ e ^ 5 :=
  fun H => H 27 84 110 133 144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
-- @endregion

-- @region research_ethics.fermat_conjecture_false
-- @provenance independent
/-- **Fermat's conjecture on the numbers `Fₙ = 2^(2^n) + 1` is false** (Euler, 1732): Fermat
believed they are all prime, but `641` divides `F₅ = 2³² + 1 = 4294967297`. Uses Mathlib's
`Nat.fermatNumber`. -/
theorem fermat_conjecture_false : ¬ ∀ n : ℕ, (Nat.fermatNumber n).Prime := by
  intro H
  have h641 : 641 ∣ Nat.fermatNumber 5 := by norm_num [Nat.fermatNumber]
  rcases (H 5).eq_one_or_self_of_dvd 641 h641 with h | h
  · norm_num at h
  · norm_num [Nat.fermatNumber] at h
-- @endregion

/-! ### The alphabetical convention -/

-- @region research_ethics.author_order
-- @provenance definition
/-- The alphabetical convention for author lists, made precise: sort the names. Lean compares
strings by Unicode code points, which is *not* the order of any dictionary — see
`author_order_example`. -/
def authorOrder (authors : List String) : List String :=
  authors.mergeSort (· ≤ ·)
-- @endregion

-- @region research_ethics.author_order_eq_of_perm
-- @provenance independent
/-- An alphabetical author list depends only on who the authors are: any two orderings of the
same names sort to the same list. So the order carries no information about who did what — which
is the point of the convention. (Both sorted lists are permutations of each other and sorted, and
a sorted list is determined by its elements.) -/
theorem authorOrder_eq_of_perm {l₁ l₂ : List String} (h : l₁.Perm l₂) :
    authorOrder l₁ = authorOrder l₂ :=
  List.Perm.eq_of_sortedLE List.sortedLE_mergeSort List.sortedLE_mergeSort
    (((List.mergeSort_perm l₁ _).trans h).trans (List.mergeSort_perm l₂ _).symm)
-- @endregion

-- @region research_ethics.mem_author_order
-- @provenance library
/-- Sorting neither drops nor adds an author: `a` is in the sorted list exactly when `a` is in the
original list (core Lean's `List.mergeSort_perm`). -/
theorem mem_authorOrder {authors : List String} {a : String} :
    a ∈ authorOrder authors ↔ a ∈ authors :=
  (List.mergeSort_perm authors _).mem_iff
-- @endregion

-- @region research_ethics.author_order_example
-- @provenance independent
/-- Formalising forces a hidden convention into the open: in code-point order an accented capital
comes after `Z`, so "Álvarez" sorts after "Zhang", unlike in a Spanish or English dictionary. A
journal's "alphabetical" order is a choice of collation, which must be stated. -/
theorem author_order_example :
    authorOrder ["Zhang", "Álvarez", "Okafor", "Bose"] = ["Bose", "Okafor", "Zhang", "Álvarez"] := by
  simp [authorOrder, List.mergeSort]
-- @endregion

end Lumenary.ResearchEthics
