/-
The Lumenary — formal mathematics
Information theory: entropy, relative entropy and Gibbs' inequality, the bounds
`0 ≤ H ≤ log |𝒳|`, Kraft's inequality for prefix codes, the source coding bounds, the
capacity of the binary symmetric channel, and the impossibility of compressing every file.

Lean and Mathlib use natural logarithms, so entropies here are in **nats**; dividing by
`log 2` converts to bits (`H₂ = H / log 2`). Mathlib provides `Real.negMulLog x = −x log x`,
the binary entropy `Real.binEntropy` with its maximum `log 2` at `1/2`, and
`Real.log_le_sub_one_of_pos`. Proved here (`@provenance independent`): non-negativity of
entropy, Gibbs' inequality, `H ≤ log |𝒳|`, Kraft's inequality for prefix-free sets of binary
words, the lower bound `L ≥ H` for prefix codes, the Shannon code lengths `⌈−log₂ p⌉` and the
upper bound `L < H + 1`, the capacity of the binary symmetric channel, and the counting
argument that no lossless compressor shortens every string.
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum

open Finset Real

namespace Lumenary.InformationTheory

variable {S : Type*} [Fintype S]

/-! ### Entropy and relative entropy -/

-- @region information_theory.entropy
-- @provenance definition
/-- The **Shannon entropy** of a distribution `p` on a finite set, in nats:
`H(p) = −∑ p(x) log p(x) = ∑ negMulLog (p x)`. (Lean's convention `log 0 = 0` gives the
usual `0 log 0 = 0`.) -/
noncomputable def entropy (p : S → ℝ) : ℝ := ∑ x, negMulLog (p x)
-- @endregion

-- @region information_theory.entropy_nonneg
-- @provenance independent
/-- **Entropy is non-negative**: each term `−p log p` is `≥ 0` for `0 ≤ p ≤ 1` (Mathlib's
`Real.negMulLog_nonneg`). It is `0` exactly for a point mass: no uncertainty. -/
theorem entropy_nonneg {p : S → ℝ} (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) :
    0 ≤ entropy p :=
  sum_nonneg fun x _ => negMulLog_nonneg (h0 x) (h1 x)
-- @endregion

-- @region information_theory.gibbs
-- @provenance independent
/-- **Gibbs' inequality.** If `p` is a distribution and `q > 0` with `∑ q ≤ 1`, then
`∑ p(x) log (q(x)/p(x)) ≤ 0`; equivalently the relative entropy
`D(p ‖ q) = ∑ p log (p/q)` is non-negative. Proof, as in the lesson: termwise
`p log (q/p) ≤ p (q/p − 1) = q − p` by `log t ≤ t − 1` (and `0 ≤ q` when `p = 0`); summing,
`∑ (q − p) = ∑ q − 1 ≤ 0`. -/
theorem gibbs {p q : S → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ x, 0 < q x)
    (hq1 : ∑ x, q x ≤ 1) : ∑ x, p x * log (q x / p x) ≤ 0 := by
  have hterm : ∀ x, p x * log (q x / p x) ≤ q x - p x := by
    intro x
    rcases (hp0 x).lt_or_eq with hpos | hzero
    · have := log_le_sub_one_of_pos (div_pos (hq x) hpos)
      calc p x * log (q x / p x) ≤ p x * (q x / p x - 1) :=
            mul_le_mul_of_nonneg_left this hpos.le
        _ = q x - p x := by field_simp
    · rw [← hzero]
      simp [(hq x).le]
  calc ∑ x, p x * log (q x / p x) ≤ ∑ x, (q x - p x) := sum_le_sum fun x _ => hterm x
    _ = ∑ x, q x - ∑ x, p x := sum_sub_distrib _ _
    _ ≤ 0 := by linarith
-- @endregion

-- @region information_theory.entropy_le_log_card
-- @provenance independent
/-- **Entropy is at most `log |𝒳|`**, with the uniform distribution as the extreme case.
Proof: Gibbs' inequality with `q` uniform, `q(x) = 1/|𝒳|`:
`0 ≥ ∑ p log (1/(|𝒳| p)) = H(p) − log |𝒳|`. -/
theorem entropy_le_log_card [Nonempty S] {p : S → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) : entropy p ≤ log (Fintype.card S) := by
  set n : ℝ := (Fintype.card S : ℝ)
  have hn : 0 < n := by
    simp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hq1 : ∑ _x : S, (1 / n) ≤ 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    simp only [n]
    field_simp
    exact le_refl _
  have hg := gibbs (q := fun _ => 1 / n) hp0 hp1 (fun _ => by positivity) hq1
  -- Each term splits: `p log (1/(n p)) = −p log p − p log n`.
  have hsplit : ∀ x, p x * log ((1 / n) / p x) = negMulLog (p x) - p x * log n := by
    intro x
    rcases (hp0 x).lt_or_eq with hpos | hzero
    · rw [negMulLog, div_div, one_div, log_inv, log_mul hn.ne' hpos.ne']
      ring
    · rw [← hzero]
      simp [negMulLog]
  simp only [hsplit, sum_sub_distrib, ← sum_mul, hp1, one_mul] at hg
  unfold entropy
  linarith
-- @endregion

-- @region information_theory.bin_entropy_le_log_two
-- @provenance library
/-- The binary entropy `h(p) = −p log p − (1 − p) log (1 − p)` is at most `log 2` (one bit).
This is Mathlib's `Real.binEntropy_le_log_two`. -/
theorem binEntropy_le_log_two' (p : ℝ) : binEntropy p ≤ log 2 :=
  binEntropy_le_log_two
-- @endregion

-- @region information_theory.bin_entropy_half
-- @provenance library
/-- …with equality exactly at `p = 1/2`: a fair coin carries one full bit. This is Mathlib's
`Real.binEntropy_eq_log_two`. -/
theorem binEntropy_eq_log_two_iff (p : ℝ) : binEntropy p = log 2 ↔ p = 2⁻¹ :=
  binEntropy_eq_log_two
-- @endregion

/-! ### The binary symmetric channel -/

-- @region information_theory.bsc_info
-- @provenance definition
/-- The mutual information `I(X; Y)` of a **binary symmetric channel** with crossover
probability `p`, when the input is `1` with probability `s`: the output is `1` with probability
`s(1 − p) + (1 − s)p`, so `H(Y) = h(s(1 − p) + (1 − s)p)`, while `H(Y | X) = h(p)` whatever
the input. Hence `I = H(Y) − H(Y | X)`. (This derivation is in the lesson; here it is the
definition.) -/
noncomputable def bscInfo (p s : ℝ) : ℝ := binEntropy (s * (1 - p) + (1 - s) * p) - binEntropy p
-- @endregion

-- @region information_theory.bsc_info_le
-- @provenance independent
/-- For every input distribution, `I(X; Y) ≤ log 2 − h(p)`, because `H(Y) ≤ log 2`. -/
theorem bsc_info_le (p s : ℝ) : bscInfo p s ≤ log 2 - binEntropy p := by
  unfold bscInfo
  linarith [binEntropy_le_log_two (p := s * (1 - p) + (1 - s) * p)]
-- @endregion

-- @region information_theory.bsc_capacity
-- @provenance independent
/-- **The capacity of the binary symmetric channel is `log 2 − h(p)` nats, i.e. `1 − H₂(p)`
bits**: the bound of `bsc_info_le` is attained by the uniform input `s = 1/2`, which makes the
output uniform too. -/
theorem bsc_capacity (p : ℝ) : bscInfo p (1 / 2) = log 2 - binEntropy p := by
  unfold bscInfo
  have : (1 / 2 : ℝ) * (1 - p) + (1 - 1 / 2) * p = 2⁻¹ := by ring
  rw [this, (binEntropy_eq_log_two).mpr rfl]
-- @endregion

/-! ### Prefix codes and Kraft's inequality -/

-- @region information_theory.prefix_free
-- @provenance definition
/-- A set of binary codewords is **prefix-free** if no codeword is a proper beginning of
another: `u <+: v` (`u` is a prefix of `v`) forces `u = v`. Such a code can be decoded on the
fly, without separators. -/
def PrefixFree (C : Finset (List Bool)) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u <+: v → u = v
-- @endregion

-- @region information_theory.kraft
-- @provenance independent
/-- **Kraft's inequality.** For every finite prefix-free set `C` of binary words,
`∑_{w ∈ C} 2^{−|w|} ≤ 1`. Proof by induction on the maximum length `L`: if the empty word is
in `C`, prefix-freeness forces `C = {[]}`; otherwise split `C` by first bit into `0·C₀` and
`1·C₁`, where `C₀, C₁` are prefix-free with words of length `≤ L − 1`, so
`∑_C 2^{−|w|} = ½ ∑_{C₀} + ½ ∑_{C₁} ≤ ½ + ½`. -/
theorem kraft : ∀ (L : ℕ) (C : Finset (List Bool)), (∀ w ∈ C, w.length ≤ L) → PrefixFree C →
    ∑ w ∈ C, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  intro L
  induction L with
  | zero =>
    intro C hlen _
    have hsub : C ⊆ {[]} := by
      intro w hw
      have := hlen w hw
      simp_all [List.length_eq_zero_iff]
    calc ∑ w ∈ C, (1 / 2 : ℝ) ^ w.length ≤ ∑ w ∈ ({[]} : Finset (List Bool)),
          (1 / 2 : ℝ) ^ w.length := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | succ L ih =>
    intro C hlen hpf
    by_cases hnil : [] ∈ C
    · -- The empty word is a prefix of everything, so `C = {[]}`.
      have hC : C = {[]} := by
        ext w
        simp only [mem_singleton]
        constructor
        · intro hw
          exact (hpf [] hnil w hw (List.nil_prefix)).symm
        · rintro rfl
          exact hnil
      simp [hC]
    · -- Split by the first bit.
      let part : Bool → Finset (List Bool) := fun b =>
        (C.filter (fun w => w.head? = some b)).image List.tail
      have hpart_len : ∀ b, ∀ t ∈ part b, t.length ≤ L := by
        intro b t ht
        simp only [part, mem_image, mem_filter] at ht
        obtain ⟨w, ⟨hw, _⟩, rfl⟩ := ht
        have := hlen w hw
        rw [List.length_tail]
        omega
      have hcons : ∀ b, ∀ w ∈ C.filter (fun w => w.head? = some b), w = b :: w.tail := by
        intro b w hw
        simp only [mem_filter] at hw
        cases w with
        | nil => simp at hw
        | cons a t =>
          simp only [List.head?_cons, Option.some.injEq] at hw
          rw [hw.2]
          rfl
      have hpart_pf : ∀ b, PrefixFree (part b) := by
        intro b u hu v hv huv
        simp only [part, mem_image] at hu hv
        obtain ⟨u', hu', rfl⟩ := hu
        obtain ⟨v', hv', rfl⟩ := hv
        have hu'' := hcons b u' hu'
        have hv'' := hcons b v' hv'
        have hpre : u' <+: v' := by
          rw [hu'', hv'']
          exact (List.prefix_cons_inj b).mpr huv
        have := hpf u' (mem_filter.mp hu').1 v' (mem_filter.mp hv').1 hpre
        rw [this]
      have hpart_sum : ∀ b, ∑ w ∈ C.filter (fun w => w.head? = some b), (1 / 2 : ℝ) ^ w.length =
          1 / 2 * ∑ t ∈ part b, (1 / 2 : ℝ) ^ t.length := by
        intro b
        rw [sum_image]
        · rw [mul_sum]
          refine sum_congr rfl fun w hw => ?_
          rw [hcons b w hw]
          simp [pow_succ]
          ring
        · intro x hx y hy hxy
          rw [hcons b x hx, hcons b y hy, hxy]
      -- Every word of `C` starts with `false` or `true`.
      have hsplit : ∑ w ∈ C, (1 / 2 : ℝ) ^ w.length =
          ∑ w ∈ C.filter (fun w => w.head? = some false), (1 / 2 : ℝ) ^ w.length +
          ∑ w ∈ C.filter (fun w => w.head? = some true), (1 / 2 : ℝ) ^ w.length := by
        rw [← sum_union]
        · congr 1
          ext w
          simp only [mem_union, mem_filter]
          constructor
          · intro hw
            cases w with
            | nil => exact absurd hw hnil
            | cons a t => cases a <;> simp [hw]
          · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
        · rw [disjoint_left]
          intro w h1 h2
          simp only [mem_filter] at h1 h2
          rw [h1.2] at h2
          simp at h2
      rw [hsplit, hpart_sum false, hpart_sum true]
      have h0 := ih (part false) (hpart_len false) (hpart_pf false)
      have h1 := ih (part true) (hpart_len true) (hpart_pf true)
      linarith
-- @endregion

/-! ### Source coding -/

-- @region information_theory.source_coding_lower
-- @provenance independent
/-- **No prefix code beats the entropy.** If codeword lengths `ℓ(x)` satisfy Kraft's
inequality `∑ 2^{−ℓ(x)} ≤ 1`, then the expected length is at least the entropy:
`H(p) ≤ (∑ p(x) ℓ(x)) · log 2` (in bits: `L ≥ H₂`). Proof: Gibbs' inequality with
`q(x) = 2^{−ℓ(x)}`. -/
theorem source_coding_lower {p : S → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ℓ : S → ℕ) (hkraft : ∑ x, (1 / 2 : ℝ) ^ ℓ x ≤ 1) :
    entropy p ≤ (∑ x, p x * ℓ x) * log 2 := by
  have hg := gibbs (q := fun x => (1 / 2 : ℝ) ^ ℓ x) hp0 hp1 (fun x => by positivity) hkraft
  have hsplit : ∀ x, p x * log ((1 / 2 : ℝ) ^ ℓ x / p x) =
      negMulLog (p x) - p x * ℓ x * log 2 := by
    intro x
    rcases (hp0 x).lt_or_eq with hpos | hzero
    · rw [log_div (by positivity) hpos.ne', log_pow, one_div, log_inv, negMulLog]
      ring
    · rw [← hzero]
      simp [negMulLog]
  simp only [hsplit, sum_sub_distrib] at hg
  unfold entropy
  rw [sum_mul]
  linarith
-- @endregion

-- @region information_theory.shannon_lengths_kraft
-- @provenance independent
/-- **Shannon's code lengths satisfy Kraft.** For a distribution with all `p(x) > 0`, the
lengths `ℓ(x) = ⌈−log₂ p(x)⌉` satisfy `2^{−ℓ(x)} ≤ p(x)`, hence `∑ 2^{−ℓ(x)} ≤ 1`, so (by
the converse of Kraft) a prefix code with these lengths exists. -/
theorem shannon_lengths_kraft {p : S → ℝ} (hp : ∀ x, 0 < p x) (hp1 : ∑ x, p x = 1) :
    ∑ x, (1 / 2 : ℝ) ^ ⌈-logb 2 (p x)⌉₊ ≤ 1 := by
  have hterm : ∀ x, (1 / 2 : ℝ) ^ ⌈-logb 2 (p x)⌉₊ ≤ p x := by
    intro x
    have hceil : -logb 2 (p x) ≤ ⌈-logb 2 (p x)⌉₊ := Nat.le_ceil _
    -- `(1/2)^ℓ = 2^(−ℓ) ≤ 2^(logb 2 p) = p`.
    have h2 : (1 / 2 : ℝ) ^ ⌈-logb 2 (p x)⌉₊ = (2 : ℝ) ^ (-(⌈-logb 2 (p x)⌉₊ : ℝ)) := by
      rw [rpow_neg (by norm_num), rpow_natCast, one_div, inv_pow]
    rw [h2]
    calc (2 : ℝ) ^ (-(⌈-logb 2 (p x)⌉₊ : ℝ)) ≤ (2 : ℝ) ^ (logb 2 (p x)) :=
          rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = p x := rpow_logb (by norm_num) (by norm_num) (hp x)
  calc ∑ x, (1 / 2 : ℝ) ^ ⌈-logb 2 (p x)⌉₊ ≤ ∑ x, p x := sum_le_sum fun x _ => hterm x
    _ = 1 := hp1
-- @endregion

-- @region information_theory.shannon_lengths_bound
-- @provenance independent
/-- **…and they are within one bit of the entropy**: `∑ p(x) ⌈−log₂ p(x)⌉ < H₂(p) + 1`,
where `H₂(p) = ∑ p(x)(−log₂ p(x))` is the entropy in bits (`S` non-empty). Proof:
`⌈t⌉ < t + 1` for `t = −log₂ p(x) ≥ 0`, then average. Together with `source_coding_lower`,
the optimal expected length `L*` satisfies `H₂ ≤ L* < H₂ + 1`. -/
theorem shannon_lengths_bound [Nonempty S] {p : S → ℝ} (hp : ∀ x, 0 < p x)
    (hp1 : ∑ x, p x = 1) :
    ∑ x, p x * ⌈-logb 2 (p x)⌉₊ < ∑ x, p x * (-logb 2 (p x)) + 1 := by
  have hle1 : ∀ x, p x ≤ 1 := fun x => by
    have := single_le_sum (fun y _ => (hp y).le) (mem_univ x)
    rw [hp1] at this
    exact this
  have hterm : ∀ x, p x * ⌈-logb 2 (p x)⌉₊ < p x * (-logb 2 (p x) + 1) := by
    intro x
    have hnn : 0 ≤ -logb 2 (p x) := by
      have := logb_nonpos (by norm_num : (1 : ℝ) < 2) (hp x).le (hle1 x)
      linarith
    exact mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one hnn) (hp x)
  calc ∑ x, p x * ⌈-logb 2 (p x)⌉₊ < ∑ x, p x * (-logb 2 (p x) + 1) :=
        sum_lt_sum_of_nonempty univ_nonempty fun x _ => hterm x
    _ = ∑ x, p x * (-logb 2 (p x)) + 1 := by
        simp only [mul_add, mul_one, sum_add_distrib, hp1]
-- @endregion

/-! ### No free compression -/

-- @region information_theory.no_universal_compression
-- @provenance independent
/-- **No lossless compressor shortens every file.** There is no injective map from the `2ⁿ`
binary strings of length `n` to binary strings of length less than `n` (a string of length
`k < n` is a pair `⟨k, f : Fin k → Bool⟩`). Proof: there are only
`2⁰ + 2¹ + ⋯ + 2ⁿ⁻¹ = 2ⁿ − 1` shorter strings — the pigeonhole principle. -/
theorem no_universal_compression (n : ℕ)
    (f : (Fin n → Bool) → (Σ k : Fin n, (Fin k → Bool))) : ¬ Function.Injective f := by
  intro hf
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  have hgeom : ∑ k : Fin n, 2 ^ (k : ℕ) = 2 ^ n - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) n, Nat.geomSum_eq (le_refl 2)]
    simp
  rw [hgeom] at hcard
  have : 0 < 2 ^ n := pow_pos (by norm_num) n
  omega
-- @endregion

end Lumenary.InformationTheory
