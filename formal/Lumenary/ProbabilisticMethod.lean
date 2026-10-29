/-
The Lumenary — formal mathematics
The probabilistic method: the union bound and averaging principles, Markov's inequality, and a
complete formal proof of Erdős's 1947 lower bound for diagonal Ramsey numbers.

What is proved here. Independently: the union bound in counting form ("if the bad sets are
small in total, a good point exists"); the averaging principle ("some value is at least the
mean"); Markov's inequality for counting measure; and **Erdős's theorem**: if `k ≥ 3` and
`n² ≤ 2ᵏ` (that is, `n ≤ 2^{k/2}`), then the edges of the complete graph `Kₙ` can be coloured red
and blue with no monochromatic `Kₖ`, so `R(k, k) > n`. The probability space is the uniform
distribution on the `2^{C(n,2)}` colourings, and every probability is written as a count of
colourings. We also check by computation that the pentagon colouring shows `R(3, 3) > 5`.

What Mathlib provides. Finite cardinalities (`Fintype.card`, `Finset.card_biUnion_le`,
`Fintype.card_finset_len`), binomial bounds, and the analytic inequality
`cosh x ≤ exp(x²/2)` (`Real.cosh_le_exp_half_sq`) at the heart of the Chernoff bound. Not
formalised here: the second-moment method, the Lovász local lemma and Chernoff bounds for random
variables (Mathlib has the measure-theoretic probability needed to state them, but we keep to
counting).
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace Lumenary.ProbabilisticMethod

open Finset

/-! ### Three counting principles -/

-- @region probabilistic_method.exists_avoiding
-- @provenance independent
/-- **The union bound (first-moment method, counting form).** Let `Ω` be a finite sample space and
`B i` (for `i ∈ S`) a family of "bad" events. If `∑ |B i| < |Ω|` — equivalently, if the bad events
have total probability `< 1` under the uniform distribution — then some outcome `ω` avoids every
bad event. Proof: `|⋃ B i| ≤ ∑ |B i| < |Ω|`, so the union is not everything. -/
theorem exists_avoiding {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] (S : Finset ι)
    (B : ι → Finset Ω) (h : ∑ i ∈ S, (B i).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i ∈ S, ω ∉ B i := by
  have hcard : (S.biUnion B).card < (univ : Finset Ω).card :=
    lt_of_le_of_lt card_biUnion_le (by simpa using h)
  obtain ⟨ω, -, hω⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨ω, fun i hi hωi => hω (mem_biUnion.mpr ⟨i, hi, hωi⟩)⟩
-- @endregion

-- @region probabilistic_method.exists_ge_average
-- @provenance independent
/-- **The averaging principle** (a random variable takes a value at least its mean). If
`f` has average at least `c` over a non-empty finite set `s`, then `f(ω) ≥ c` for some `ω ∈ s`.
Proof: otherwise `∑ f < ∑ c = |s| c`. -/
theorem exists_ge_average {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) (c : ℝ)
    (h : s.card * c ≤ ∑ ω ∈ s, f ω) : ∃ ω ∈ s, c ≤ f ω := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hlt : ∑ ω ∈ s, f ω < ∑ _ω ∈ s, c := sum_lt_sum_of_nonempty hs hcon
  rw [sum_const, nsmul_eq_mul] at hlt
  linarith
-- @endregion

-- @region probabilistic_method.markov_count
-- @provenance independent
/-- **Markov's inequality, counting form.** For a non-negative function `X` on a finite set and
`a > 0`, `a · #{ω : X ω ≥ a} ≤ ∑ X`; dividing by `|Ω|`, `P(X ≥ a) ≤ E[X]/a`. Proof: drop the
terms with `X < a` and bound each remaining term below by `a`. -/
theorem markov_count {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) :
    a * (univ.filter (fun ω => a ≤ X ω)).card ≤ ∑ ω, X ω := by
  classical
  calc a * (univ.filter (fun ω => a ≤ X ω)).card
      = ∑ _ω ∈ univ.filter (fun ω => a ≤ X ω), a := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ ω ∈ univ.filter (fun ω => a ≤ X ω), X ω := sum_le_sum fun ω hω => (mem_filter.mp hω).2
    _ ≤ ∑ ω, X ω := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ => hX ω
-- @endregion

/-! ### Colourings of the complete graph -/

-- @region probabilistic_method.edge
-- @provenance definition
/-- The edges of the complete graph `Kₙ`: the two-element subsets of `Fin n = {0, …, n − 1}`. -/
abbrev Edge (n : ℕ) := {e : Finset (Fin n) // e.card = 2}
-- @endregion

-- @region probabilistic_method.colouring
-- @provenance definition
/-- A red/blue colouring of the edges of `Kₙ` (`true` = red, `false` = blue). There are
`2^{C(n,2)}` of them; the uniform distribution on them is the random colouring of the lesson. -/
abbrev Colouring (n : ℕ) := Edge n → Bool
-- @endregion

-- @region probabilistic_method.monochromatic
-- @provenance definition
/-- A set `K` of vertices is **monochromatic** for `c` if all edges inside `K` have one colour. -/
def Monochromatic {n : ℕ} (c : Colouring n) (K : Finset (Fin n)) : Prop :=
  ∃ b : Bool, ∀ e : Edge n, e.1 ⊆ K → c e = b
-- @endregion

-- @region probabilistic_method.card_edge
-- @provenance library
/-- `Kₙ` has `C(n, 2)` edges. Mathlib: `Fintype.card_finset_len`. -/
theorem card_edge (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  simp [Edge, Fintype.card_finset_len]
-- @endregion

-- @region probabilistic_method.card_edges_inside
-- @provenance independent
/-- A set of `k` vertices spans (at least — in fact exactly) `C(k, 2)` edges: every two-element
subset of `K` is an edge inside `K`. -/
theorem card_edges_inside {n : ℕ} (K : Finset (Fin n)) :
    K.card.choose 2 ≤ Fintype.card {e : Edge n // e.1 ⊆ K} := by
  classical
  let f : (K.powersetCard 2) → {e : Edge n // e.1 ⊆ K} := fun s =>
    ⟨⟨s.1, (mem_powersetCard.mp s.2).2⟩, (mem_powersetCard.mp s.2).1⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun e : {e : Edge n // e.1 ⊆ K} => e.1.1) hst
  have h := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_coe, card_powersetCard] at h
-- @endregion

-- @region probabilistic_method.card_constant_on_le
-- @provenance independent
/-- **Forcing the colour of the edges inside `K`.** At most `2^{C(n,2) − C(k,2)}` colourings give
every edge inside a `k`-set `K` the colour `b`: such a colouring is determined by its values on
the remaining edges. (So the probability is at most `2^{−C(k,2)}`.) -/
theorem card_constant_on_le {n : ℕ} (K : Finset (Fin n)) (b : Bool) :
    (univ.filter (fun c : Colouring n => ∀ e : Edge n, e.1 ⊆ K → c e = b)).card
      ≤ 2 ^ (n.choose 2 - K.card.choose 2) := by
  classical
  -- restricting to the edges that are not inside `K` is injective
  let r : {c : Colouring n // ∀ e : Edge n, e.1 ⊆ K → c e = b} →
      ({e : Edge n // ¬ e.1 ⊆ K} → Bool) := fun c e => c.1 e.1
  have hr : Function.Injective r := by
    intro c d hcd
    apply Subtype.ext
    funext e
    by_cases he : e.1 ⊆ K
    · rw [c.2 e he, d.2 e he]
    · exact congrFun hcd ⟨e, he⟩
  have h1 := Fintype.card_le_of_injective r hr
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, card_edge,
    Fintype.card_subtype] at h1
  refine h1.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left ?_ _))
  exact card_edges_inside K
-- @endregion

-- @region probabilistic_method.card_monochromatic_le
-- @provenance independent
open scoped Classical in
/-- **A fixed `k`-set is monochromatic in at most `2 · 2^{C(n,2) − C(k,2)}` colourings** — all red or
all blue. In probability: `P(K monochromatic) ≤ 2^{1 − C(k,2)}`. -/
theorem card_monochromatic_le {n : ℕ} (K : Finset (Fin n)) :
    (univ.filter (fun c : Colouring n => Monochromatic c K)).card
      ≤ 2 * 2 ^ (n.choose 2 - K.card.choose 2) := by
  classical
  have hsub : univ.filter (fun c : Colouring n => Monochromatic c K) ⊆
      univ.filter (fun c : Colouring n => ∀ e : Edge n, e.1 ⊆ K → c e = true) ∪
      univ.filter (fun c : Colouring n => ∀ e : Edge n, e.1 ⊆ K → c e = false) := by
    intro c hc
    obtain ⟨b, hb⟩ := (mem_filter.mp hc).2
    cases b
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hb⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hb⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 2 ^ (n.choose 2 - K.card.choose 2) + 2 ^ (n.choose 2 - K.card.choose 2) :=
      add_le_add (card_constant_on_le K true) (card_constant_on_le K false)
    _ = 2 * 2 ^ (n.choose 2 - K.card.choose 2) := by ring
-- @endregion

/-! ### Erdős's lower bound -/

-- @region probabilistic_method.factorial_sq_gt
-- @provenance independent
/-- `(k!)² > 4 · 2ᵏ` for `k ≥ 3` (by induction: `36 > 32`, and each step multiplies the left side
by `(k + 1)² ≥ 16` and the right side by `2`). Equivalently `k! > 2^{1 + k/2}`. -/
theorem factorial_sq_gt {k : ℕ} (hk : 3 ≤ k) : 4 * 2 ^ k < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have h2 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith
-- @endregion

-- @region probabilistic_method.erdos_arithmetic
-- @provenance independent
/-- **Erdős's arithmetic**: if `k ≥ 3` and `n² ≤ 2ᵏ`, then `C(n, k) · 2^{1 − C(k,2)} < 1`, i.e.
`2 · C(n, k) < 2^{C(k,2)}`. Proof: `k! · C(n, k) ≤ nᵏ`, so
`(2 C(n,k))² · 2ᵏ = 4 C(n,k)² 2ᵏ < C(n,k)² (k!)² ≤ n^{2k} ≤ 2^{k²} = 2^{2 C(k,2)} · 2ᵏ`,
using `4 · 2ᵏ < (k!)²` and `k² = k(k − 1) + k = 2 C(k,2) + k`. -/
theorem erdos_arithmetic {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ k.choose 2 := by
  set C := n.choose k with hC
  set M := k.choose 2 with hM
  rcases Nat.eq_zero_or_pos C with h0 | hpos
  · rw [h0]; positivity
  -- `k! · C(n, k) ≤ nᵏ`
  have hfact : k.factorial * C ≤ n ^ k := by
    rw [hC, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  -- `2 C(k, 2) + k = k²`
  have hMk : 2 * M + k = k * k := by
    have hdiv : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
    have h2M : 2 * M = k * (k - 1) := by
      rw [hM, Nat.choose_two_right, Nat.mul_div_cancel' hdiv]
    rw [h2M]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h4 := factorial_sq_gt hk
  -- chain of inequalities, multiplied through by `2ᵏ`
  have hchain : (2 * C) ^ 2 * 2 ^ k < (2 ^ M) ^ 2 * 2 ^ k := by
    calc (2 * C) ^ 2 * 2 ^ k = C ^ 2 * (4 * 2 ^ k) := by ring
      _ < C ^ 2 * (k.factorial) ^ 2 := by
        apply Nat.mul_lt_mul_of_pos_left h4 (by positivity)
      _ = (k.factorial * C) ^ 2 := by ring
      _ ≤ (n ^ k) ^ 2 := Nat.pow_le_pow_left hfact 2
      _ = (n ^ 2) ^ k := by ring
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hn k
      _ = 2 ^ (2 * M + k) := by rw [hMk, ← pow_mul]
      _ = (2 ^ M) ^ 2 * 2 ^ k := by ring
  have hsq : (2 * C) ^ 2 < (2 ^ M) ^ 2 := Nat.lt_of_mul_lt_mul_right hchain
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
-- @endregion

-- @region probabilistic_method.erdos_ramsey_lower_bound
-- @provenance independent
/-- **Erdős's theorem (1947): `R(k, k) > 2^{k/2}`.** If `k ≥ 3` and `n² ≤ 2ᵏ`, some red/blue
colouring of the edges of `Kₙ` has no monochromatic `Kₖ`. Proof (the lesson's, as counting): there
are `C(n, k)` sets of `k` vertices, each monochromatic in at most `2 · 2^{C(n,2) − C(k,2)}` of the
`2^{C(n,2)}` colourings, and `C(n, k) · 2 · 2^{C(n,2) − C(k,2)} < 2^{C(n,2)}` by
`erdos_arithmetic`; the union bound gives a colouring avoiding them all. The proof does not say
which colouring works. -/
theorem erdos_ramsey_lower_bound {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ c : Colouring n, ∀ K : Finset (Fin n), K.card = k → ¬ Monochromatic c K := by
  classical
  set S := (univ : Finset (Fin n)).powersetCard k
  set B : Finset (Fin n) → Finset (Colouring n) := fun K =>
    univ.filter (fun c : Colouring n => Monochromatic c K)
  have hlt : n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) < 2 ^ n.choose 2 := by
    rcases le_or_gt k n with hkn | hkn
    · have hle : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
      have hsplit : 2 ^ n.choose 2 = 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [hsplit, ← mul_assoc]
      exact Nat.mul_lt_mul_of_pos_right (by linarith [erdos_arithmetic hk hn]) (by positivity)
    · rw [Nat.choose_eq_zero_of_lt hkn, zero_mul]
      positivity
  have hsum : ∑ K ∈ S, (B K).card < Fintype.card (Colouring n) := by
    calc ∑ K ∈ S, (B K).card ≤ ∑ _K ∈ S, 2 * 2 ^ (n.choose 2 - k.choose 2) := by
          apply sum_le_sum
          intro K hK
          have hKc : K.card = k := (mem_powersetCard.mp hK).2
          have := card_monochromatic_le K
          rwa [hKc] at this
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [sum_const, smul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin]
      _ < 2 ^ n.choose 2 := hlt
      _ = Fintype.card (Colouring n) := by
          rw [Fintype.card_fun, Fintype.card_bool, card_edge]
  obtain ⟨c, hc⟩ := exists_avoiding S B hsum
  refine ⟨c, fun K hK hmono => hc K ?_ ?_⟩
  · exact mem_powersetCard.mpr ⟨subset_univ K, hK⟩
  · exact mem_filter.mpr ⟨mem_univ c, hmono⟩
-- @endregion

-- @region probabilistic_method.pentagon_colouring
-- @provenance independent
/-- **An explicit colouring: `R(3, 3) > 5`.** Colour the edge `{i, j}` of `K₅` red when `i` and `j`
are neighbours on the pentagon (`j − i ≡ ±1 mod 5`) and blue otherwise. No three vertices
`a < b < c` span a monochromatic triangle: both colour classes are 5-cycles. Checked by `decide`
over all `C(5, 3) = 10` triangles. For larger `k` no explicit colouring anywhere near Erdős's
bound is known. -/
theorem pentagon_colouring :
    let red : Fin 5 → Fin 5 → Bool := fun i j => (j.val + 5 - i.val) % 5 == 1 ||
      (j.val + 5 - i.val) % 5 == 4
    ∀ a b c : Fin 5, a < b → b < c → ¬ (red a b = red b c ∧ red b c = red a c) := by
  decide
-- @endregion

/-! ### The analytic lemma behind Chernoff bounds -/

-- @region probabilistic_method.cosh_le_exp_half_sq
-- @provenance library
/-- **`cosh x ≤ e^{x²/2}`**, comparing the Taylor series term by term (`(2k)! ≥ 2ᵏ k!`). For a
uniform random sign `ε = ±1`, `E[e^{λε}] = cosh λ ≤ e^{λ²/2}`, which gives the Chernoff bound
`P(ε₁ + ⋯ + εₙ ≥ a) ≤ e^{−a²/(2n)}`. Mathlib: `Real.cosh_le_exp_half_sq`. -/
theorem cosh_le_exp_half_sq (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) :=
  Real.cosh_le_exp_half_sq x
-- @endregion

end Lumenary.ProbabilisticMethod
