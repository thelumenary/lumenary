/-
The Lumenary — formal mathematics
Real analysis: ε–N limits, Cauchy sequences, monotone convergence, the intermediate value theorem
from completeness, uniform versus pointwise convergence, and the fundamental theorem of calculus.

What is proved here and what Mathlib provides. Mathlib phrases limits with filters
(`Filter.Tendsto a atTop (𝓝 L)`) and Cauchy sequences with uniformities (`CauchySeq`); we first
define the lesson's ε–N notions (`ConvergesTo`, `IsCauchy`, `UniformlyConvergesOn`) and prove they
agree with Mathlib's. The *independent* declarations re-prove lesson theorems from the
definitions, mirroring the human proofs: uniqueness of limits, convergent ⇒ Cauchy, Cauchy with a
convergent subsequence ⇒ convergent, monotone convergence from the supremum, the intermediate
value theorem from the supremum, the ε/3 proof that uniform limits of continuous functions are
continuous, the failure of uniform convergence for `xⁿ` on `[0, 1)`, the density facts behind
the non-integrability of the indicator function of `ℚ`, and the first fundamental theorem of
calculus by an integral estimate. The *library* declarations cite Mathlib's Bolzano–Weierstrass
theorem, completeness of `ℝ`, the extreme value theorem, the uniform limit theorem, the mean value
theorem and the second fundamental theorem of calculus. Mathlib's integral is the Lebesgue
(Bochner) integral; for continuous functions on intervals it agrees with the Riemann integral of
the lesson, but Mathlib has no separate theory of Riemann integrability on `ℝ`, so the statement
"the indicator of `ℚ` is not Riemann integrable" is not formalised here.
-/
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace Lumenary.RealAnalysis

open Filter Topology Set

/-! ### Sequences: the ε–N definitions -/

-- @region real_analysis.converges_to
-- @provenance definition
/-- `ConvergesTo a L`: the sequence `a` converges to `L` — for every `ε > 0` there is an index `N`
such that `|aₙ - L| < ε` for every `n ≥ N`. -/
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- @endregion

-- @region real_analysis.is_cauchy
-- @provenance definition
/-- `IsCauchy a`: the terms of `a` eventually stay close *to each other* — for every `ε > 0` there
is `N` with `|aₘ - aₙ| < ε` for all `m, n ≥ N`. No limit is mentioned. -/
def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε
-- @endregion

-- @region real_analysis.converges_to_iff_tendsto
-- @provenance library
/-- The lesson's ε–N definition agrees with Mathlib's filter definition of a limit. This applies
Mathlib's `Metric.tendsto_atTop` (and `Real.dist_eq : dist x y = |x - y|`). -/
theorem convergesTo_iff_tendsto (a : ℕ → ℝ) (L : ℝ) :
    ConvergesTo a L ↔ Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  simp only [ConvergesTo, Real.dist_eq]
-- @endregion

-- @region real_analysis.limit_unique
-- @provenance independent
/-- **Limits are unique.** If `aₙ → L` and `aₙ → M`, then `L = M`. Otherwise take
`ε = |L - M| / 2`: far enough along, `aₙ` is within `ε` of both, and the triangle inequality gives
`|L - M| ≤ |L - aₙ| + |aₙ - M| < 2ε = |L - M|`. -/
theorem limit_unique {a : ℕ → ℝ} {L M : ℝ} (hL : ConvergesTo a L) (hM : ConvergesTo a M) :
    L = M := by
  by_contra hne
  have hpos : 0 < |L - M| / 2 := by
    have : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨N₁, hN₁⟩ := hL _ hpos
  obtain ⟨N₂, hN₂⟩ := hM _ hpos
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  have htri : |L - M| ≤ |a (max N₁ N₂) - L| + |a (max N₁ N₂) - M| := by
    calc |L - M| = |(a (max N₁ N₂) - M) - (a (max N₁ N₂) - L)| := by ring_nf
      _ ≤ |a (max N₁ N₂) - M| + |a (max N₁ N₂) - L| := abs_sub _ _
      _ = |a (max N₁ N₂) - L| + |a (max N₁ N₂) - M| := add_comm _ _
  linarith
-- @endregion

-- @region real_analysis.cauchy_of_converges_to
-- @provenance independent
/-- **Every convergent sequence is Cauchy.** Given `ε`, choose `N` so that every term from `N` on
is within `ε/2` of the limit `L`; then `|aₘ - aₙ| ≤ |aₘ - L| + |L - aₙ| < ε/2 + ε/2 = ε`. -/
theorem cauchy_of_convergesTo {a : ℕ → ℝ} {L : ℝ} (h : ConvergesTo a L) : IsCauchy a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm' := hN m hm
  have hn' := hN n hn
  calc |a m - a n| = |(a m - L) - (a n - L)| := by ring_nf
    _ ≤ |a m - L| + |a n - L| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hm' hn'
    _ = ε := by ring
-- @endregion

-- @region real_analysis.converges_to_of_cauchy_of_subseq
-- @provenance independent
/-- **A Cauchy sequence with a convergent subsequence converges** (to the same limit). This is
the heart of "Cauchy ⇒ convergent": Bolzano–Weierstrass supplies the subsequence. Given `ε`, take
`N` from the Cauchy condition for `ε/2` and `K` so that `a (φ k)` is within `ε/2` of `L` for
`k ≥ K`. For `n ≥ N` pick `k = max K n`; since `φ` is strictly increasing, `φ k ≥ k ≥ n ≥ N`,
so `|aₙ - L| ≤ |aₙ - a (φ k)| + |a (φ k) - L| < ε`. -/
theorem convergesTo_of_cauchy_of_subseq {a : ℕ → ℝ} {L : ℝ} {φ : ℕ → ℕ} (ha : IsCauchy a)
    (hφ : StrictMono φ) (hsub : ConvergesTo (a ∘ φ) L) : ConvergesTo a L := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε / 2) (by linarith)
  obtain ⟨K, hK⟩ := hsub (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hk : n ≤ φ (max K n) := le_trans (le_max_right K n) (hφ.id_le _)
  have h1 : |a n - a (φ (max K n))| < ε / 2 := hN n hn _ (le_trans hn hk)
  have h2 : |a (φ (max K n)) - L| < ε / 2 := hK (max K n) (le_max_left _ _)
  calc |a n - L| = |(a n - a (φ (max K n))) + (a (φ (max K n)) - L)| := by ring_nf
    _ ≤ |a n - a (φ (max K n))| + |a (φ (max K n)) - L| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring
-- @endregion

-- @region real_analysis.bolzano_weierstrass
-- @provenance library
/-- **Bolzano–Weierstrass.** Every bounded sequence of real numbers has a convergent subsequence.
This applies Mathlib's `tendsto_subseq_of_bounded`, which holds in every proper metric space
(closed balls are compact), here the closed interval `[-M, M]`. -/
theorem bolzano_weierstrass (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, |a n| ≤ M) :
    ∃ L : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 L) := by
  obtain ⟨L, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc (-M) M) (fun n => abs_le.mp (hM n))
  exact ⟨L, φ, hφ, hlim⟩
-- @endregion

-- @region real_analysis.cauchy_iff_converges
-- @provenance library
/-- **In `ℝ`, a sequence is Cauchy if and only if it converges.** The forward direction is the
completeness of `ℝ` (Mathlib's `cauchySeq_tendsto_of_complete`); the backward direction is
`cauchy_of_convergesTo`. Mathlib's `CauchySeq` is unfolded to ε–N form by `Metric.cauchySeq_iff`. -/
theorem cauchy_iff_converges (a : ℕ → ℝ) : IsCauchy a ↔ ∃ L, ConvergesTo a L := by
  constructor
  · intro h
    have hc : CauchySeq a := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn⟩
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨L, (convergesTo_iff_tendsto a L).mpr hL⟩
  · rintro ⟨L, hL⟩
    exact cauchy_of_convergesTo hL
-- @endregion

-- @region real_analysis.monotone_converges
-- @provenance independent
/-- **Monotone convergence theorem.** An increasing sequence that is bounded above converges, to
the supremum `s` of its terms. Given `ε`, the number `s - ε` is not an upper bound, so some
`a_N > s - ε`; for `n ≥ N`, monotonicity gives `s - ε < a_N ≤ aₙ ≤ s`. This is exactly where the
completeness axiom (existence of `sSup`) enters. -/
theorem monotone_converges {a : ℕ → ℝ} (hmono : Monotone a) (hbdd : BddAbove (range a)) :
    ConvergesTo a (sSup (range a)) := by
  intro ε hε
  have hlt : sSup (range a) - ε < sSup (range a) := by linarith
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (range_nonempty a) hlt
  refine ⟨N, fun n hn => ?_⟩
  have hle : a n ≤ sSup (range a) := le_csSup hbdd (mem_range_self n)
  have hge : a N ≤ a n := hmono hn
  rw [abs_lt]
  constructor <;> linarith
-- @endregion

/-! ### Continuity on intervals -/

-- @region real_analysis.ivt_from_completeness
-- @provenance independent
/-- **Intermediate value theorem, proved from completeness.** If `f` is continuous, `a ≤ b`,
`f a ≤ 0 ≤ f b`, then `f c = 0` for some `c ∈ [a, b]`. Let `S = {x ∈ [a, b] | f x ≤ 0}` and
`c = sup S`. If `f c > 0`, continuity gives a whole interval `(c - δ, c + δ)` where `f > 0`, so
`c - δ` would be an upper bound of `S` — impossible. If `f c < 0`, then `c < b` and `f < 0` a
little to the right of `c`, producing points of `S` larger than `c` — impossible. -/
theorem ivt_from_completeness {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (ha : f a ≤ 0) (hb : 0 ≤ f b) : ∃ c ∈ Icc a b, f c = 0 := by
  set S : Set ℝ := {x | a ≤ x ∧ x ≤ b ∧ f x ≤ 0} with hS
  have hne : S.Nonempty := ⟨a, le_rfl, hab, ha⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.2.1⟩
  set c := sSup S with hc
  have hac : a ≤ c := le_csSup hbdd ⟨le_rfl, hab, ha⟩
  have hcb : c ≤ b := csSup_le hne fun x hx => hx.2.1
  refine ⟨c, ⟨hac, hcb⟩, le_antisymm (not_lt.mp fun hpos => ?_) (not_lt.mp fun hneg => ?_)⟩
  · -- `f c ≤ 0`: otherwise `f > 0` near `c`, and `c` would not be the least upper bound.
    obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.mp hf c (f c) hpos
    obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup hne (show c - δ < c by linarith)
    have hsc : s ≤ c := le_csSup hbdd hsS
    have hdist : dist s c < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hfδ s hdist
    rw [Real.dist_eq, abs_lt] at this
    linarith [hsS.2.2]
  · -- `0 ≤ f c`: otherwise `f < 0` just to the right of `c`, giving points of `S` beyond `c`.
    have hcb' : c < b := lt_of_le_of_ne hcb (fun h => by rw [h] at hneg; linarith)
    obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.mp hf c (-f c) (by linarith)
    set x := min (c + δ / 2) b with hx
    have hcx : c < x := lt_min (by linarith) hcb'
    have hdist : dist x c < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith
      · have : x ≤ c + δ / 2 := min_le_left _ _
        linarith
    have hfx := hfδ x hdist
    rw [Real.dist_eq, abs_lt] at hfx
    have hxS : x ∈ S := ⟨by linarith, min_le_right _ _, by linarith⟩
    have : x ≤ c := le_csSup hbdd hxS
    linarith
-- @endregion

-- @region real_analysis.ivt_library
-- @provenance library
/-- The intermediate value theorem in Mathlib's general form: a function continuous on `[a, b]`
takes every value between `f a` and `f b`. This applies Mathlib's `intermediate_value_Icc`, which
holds for any connected interval in a densely ordered conditionally complete order. -/
theorem ivt_library {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf
-- @endregion

-- @region real_analysis.extreme_value
-- @provenance library
/-- **Extreme value theorem.** A function continuous on `[a, b]` (with `a ≤ b`) attains a maximum
there. This applies Mathlib's `IsCompact.exists_isMaxOn` to the compact interval `[a, b]`
(`isCompact_Icc`, Heine–Borel). -/
theorem extreme_value {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f c := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf
  exact ⟨c, hc, fun x hx => hmax hx⟩
-- @endregion

/-! ### Pointwise and uniform convergence -/

-- @region real_analysis.uniformly_converges_on
-- @provenance definition
/-- `UniformlyConvergesOn f g S`: the functions `fₙ` converge to `g` *uniformly* on `S` — one `N`
works for every `x ∈ S` at once. Compare pointwise convergence, where `N` may depend on `x`. -/
def UniformlyConvergesOn (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ S, |f n x - g x| < ε
-- @endregion

-- @region real_analysis.uniform_limit_continuous
-- @provenance independent
/-- **Uniform limits of continuous functions are continuous** (the ε/3 argument). Fix `x` and
`ε`. Choose `N` with `|f_N - g| < ε/3` everywhere, then `δ` with `|f_N y - f_N x| < ε/3` when
`|y - x| < δ`. Then
`|g y - g x| ≤ |g y - f_N y| + |f_N y - f_N x| + |f_N x - g x| < ε/3 + ε/3 + ε/3 = ε`. -/
theorem uniform_limit_continuous {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, Continuous (f n))
    (hu : UniformlyConvergesOn f g univ) : Continuous g := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨N, hN⟩ := hu (ε / 3) (by linarith)
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.mp (hf N) x (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h1 : |f N y - g y| < ε / 3 := hN N le_rfl y (mem_univ y)
  have h2 : |f N y - f N x| < ε / 3 := by simpa [Real.dist_eq] using hfδ y hy
  have h3 : |f N x - g x| < ε / 3 := hN N le_rfl x (mem_univ x)
  rw [Real.dist_eq]
  calc |g y - g x| = |(f N y - f N x) - (f N y - g y) + (f N x - g x)| := by ring_nf
    _ ≤ |(f N y - f N x) - (f N y - g y)| + |f N x - g x| := abs_add_le _ _
    _ ≤ |f N y - f N x| + |f N y - g y| + |f N x - g x| := by
        gcongr; exact abs_sub _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring
-- @endregion

-- @region real_analysis.uniform_limit_continuous_library
-- @provenance library
/-- Mathlib's uniform limit theorem: if `Fₙ → f` uniformly (along any filter, here `n → ∞`) and
the `Fₙ` are continuous, then `f` is continuous. This applies `TendstoUniformly.continuous`; its
proof passes through *locally* uniform convergence, which is all continuity needs. -/
theorem uniform_limit_continuous_library {X : Type*} [TopologicalSpace X] {F : ℕ → X → ℝ}
    {f : X → ℝ} (h : TendstoUniformly F f atTop) (hc : ∀ n, Continuous (F n)) : Continuous f :=
  h.continuous (Frequently.of_forall hc)
-- @endregion

-- @region real_analysis.pow_pointwise
-- @provenance library
/-- **Pointwise convergence of `xⁿ`.** For `0 ≤ x < 1`, `xⁿ → 0`. This applies Mathlib's
`tendsto_pow_atTop_nhds_zero_of_lt_one`. (At `x = 1` every term is `1`.) So on `[0, 1]` the
pointwise limit of the continuous functions `xⁿ` is `0` for `x < 1` and `1` at `x = 1`: it jumps. -/
theorem pow_pointwise {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    ConvergesTo (fun n => x ^ n) 0 :=
  (convergesTo_iff_tendsto _ 0).mpr (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)
-- @endregion

-- @region real_analysis.pow_not_uniform
-- @provenance independent
/-- **`xⁿ → 0` is not uniform on `[0, 1)`.** Take `ε = 1/2`. Whatever `N` is proposed, let
`n = N + 1` and `x = 1 - 1/(2n)`. Bernoulli's inequality `(1 + t)ⁿ ≥ 1 + n t` (for `t ≥ -2`)
gives `xⁿ ≥ 1 - n/(2n) = 1/2`, so `|xⁿ - 0| < 1/2` fails. -/
theorem pow_not_uniform : ¬ UniformlyConvergesOn (fun n x => x ^ n) (fun _ => 0) (Ico 0 1) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  set n : ℕ := N + 1 with hn
  have hnpos : (0 : ℝ) < n := by positivity
  set x : ℝ := 1 - 1 / (2 * n) with hx
  have hx0 : 0 ≤ x := by
    rw [hx, sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ n := by rw [hn]; push_cast; linarith [N.cast_nonneg (α := ℝ)]
    linarith
  have hx1 : x < 1 := by
    have : 0 < 1 / (2 * (n : ℝ)) := by positivity
    rw [hx]; linarith
  have hbern : 1 + (n : ℝ) * (-(1 / (2 * n))) ≤ (1 + -(1 / (2 * n))) ^ n := by
    apply one_add_mul_le_pow
    have : 1 / (2 * (n : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ n := by rw [hn]; push_cast; linarith [N.cast_nonneg (α := ℝ)]
      linarith
    linarith
  have hhalf : (1 : ℝ) / 2 ≤ x ^ n := by
    have e1 : 1 + (n : ℝ) * (-(1 / (2 * n))) = 1 / 2 := by field_simp; ring
    have e2 : (1 + -(1 / (2 * (n : ℝ)))) = x := by rw [hx]; ring
    rw [e1, e2] at hbern
    exact hbern
  have := hN n (by omega) x ⟨hx0, hx1⟩
  simp only [sub_zero] at this
  rw [abs_of_nonneg (pow_nonneg hx0 n)] at this
  linarith
-- @endregion

/-! ### Integration -/

-- @region real_analysis.rationals_and_irrationals_dense
-- @provenance library
/-- **Every interval contains both rationals and irrationals.** This is why the indicator function
of `ℚ` (Dirichlet's function) is not Riemann integrable on `[0, 1]`: on every subinterval of every
partition its supremum is `1` and its infimum is `0`, so every upper sum is `1` and every lower sum
is `0`. Assembled from Mathlib's `exists_rat_btwn` (Archimedean property) and
`exists_irrational_btwn`. -/
theorem rationals_and_irrationals_dense {x y : ℝ} (h : x < y) :
    (∃ q : ℚ, x < q ∧ (q : ℝ) < y) ∧ (∃ r : ℝ, Irrational r ∧ x < r ∧ r < y) :=
  ⟨exists_rat_btwn h, exists_irrational_btwn h⟩
-- @endregion

-- @region real_analysis.ftc_one
-- @provenance independent
/-- **Fundamental theorem of calculus, part 1.** If `f` is continuous, then `F(u) = ∫ₐᵘ f` is
differentiable with `F' = f`. Proof by an estimate, as in the lesson: given `c > 0`, continuity at
`x` gives `δ` with `|f t - f x| < c` for `|t - x| < δ`. For `|h| < δ`,
`F(x + h) - F(x) - h·f(x) = ∫ₓ^{x+h} (f t - f x) dt`, whose absolute value is at most `c·|h|`.
That is exactly the little-o condition defining the derivative. -/
theorem ftc_one {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.mp hf x c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have hint : ∀ p q : ℝ, IntervalIntegrable f MeasureTheory.volume p q :=
    fun p q => hf.intervalIntegrable p q
  have key : (∫ t in a..x + h, f t) - (∫ t in a..x, f t) - h • f x
      = ∫ t in x..x + h, (f t - f x) := by
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _),
      intervalIntegral.integral_sub (hint _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
    ring
  rw [key]
  have hh' : |h| < δ := by simpa [Real.dist_eq] using hh
  have hbound : ∀ t ∈ Set.uIoc x (x + h), ‖f t - f x‖ ≤ c := by
    intro t ht
    have htx : |t - x| ≤ |h| := by
      rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; linarith
    have : dist t x < δ := by rw [Real.dist_eq]; linarith
    have := hfδ t this
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  calc ‖∫ t in x..x + h, (f t - f x)‖ ≤ c * |x + h - x| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = c * ‖h‖ := by rw [Real.norm_eq_abs]; ring_nf
-- @endregion

-- @region real_analysis.ftc_one_library
-- @provenance library
/-- The same statement as `ftc_one`, from Mathlib: `Continuous.integral_hasStrictDerivAt` gives
even *strict* differentiability of `u ↦ ∫ₐᵘ f`. -/
theorem ftc_one_library {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x :=
  (hf.integral_hasStrictDerivAt a x).hasDerivAt
-- @endregion

-- @region real_analysis.ftc_two
-- @provenance library
/-- **Fundamental theorem of calculus, part 2.** If `F` has derivative `f` at every point of
`[a, b]` and `f` is integrable there, then `∫ₐᵇ f = F b - F a`. This applies Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem ftc_two {F f : ℝ → ℝ} {a b : ℝ} (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hint : IntervalIntegrable f MeasureTheory.volume a b) : ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
-- @endregion

-- @region real_analysis.mean_value
-- @provenance library
/-- **Mean value theorem.** If `f` is continuous on `[a, b]` and has derivative `f'` on `(a, b)`,
then `f' c = (f b - f a)/(b - a)` for some `c ∈ (a, b)`. This applies Mathlib's
`exists_hasDerivAt_eq_slope`, proved there from Rolle's theorem. -/
theorem mean_value {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hfc hff'
-- @endregion

-- @region real_analysis.converges_to_add
-- @provenance independent
/-- **The limit of a sum is the sum of the limits.** If `aₙ → A` and `bₙ → B` then
`aₙ + bₙ → A + B`: take `N` large enough that both are within `ε/2`, and use the triangle
inequality. (Solution to the Lean exercise.) -/
theorem convergesTo_add {a b : ℕ → ℝ} {A B : ℝ} (ha : ConvergesTo a A) (hb : ConvergesTo b B) :
    ConvergesTo (fun n => a n + b n) (A + B) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  calc |a n + b n - (A + B)| = |(a n - A) + (b n - B)| := by ring_nf
    _ ≤ |a n - A| + |b n - B| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring
-- @endregion

end Lumenary.RealAnalysis
