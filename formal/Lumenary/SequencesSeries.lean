/-
The Lumenary — formal mathematics
Sequences and series: arithmetic and geometric sums, recursive sequences, infinite geometric
series (including 0.999… = 1), the term test, and the divergence of the harmonic series.

Proved here (`@provenance independent`): the sum of an arithmetic progression; the finite
geometric sum `a(1 − rⁿ)/(1 − r)` by the "multiply by `r` and subtract" telescoping; a closed
form for the Tower of Hanoi recursion; that the partial sums of `Σ arᵏ` tend to `a/(1 − r)` when
`|r| < 1`; that `0.999… = 1`; that `Σ rⁿ` diverges when `|r| ≥ 1` (by the term test); Oresme's
estimate `1 + 1/2 + ⋯ + 1/2ⁿ ≥ 1 + n/2`, hence that the harmonic series diverges although its
terms tend to `0`.

From Mathlib (`@provenance library`): `geom_sum_eq`, `hasSum_geometric_of_abs_lt_one`,
`hasSum_geometric_two` (`1 + 1/2 + 1/4 + ⋯ = 2`), the term test `Summable.tendsto_atTop_zero`,
and `Real.not_summable_one_div_natCast`.

Note: in Mathlib a sequence is a function `ℕ → ℝ`, `∑ k ∈ range n, f k` is the finite sum
`f 0 + ⋯ + f (n − 1)`, and `HasSum f S` says that the series `Σ f k` converges to `S`. (For
series with terms of both signs, `HasSum` asks for *unconditional* convergence; for the series
here, with terms of one sign or geometric terms, this agrees with the school definition.)
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries

namespace Lumenary.SequencesSeries

open Filter Topology Finset

/-! ### Arithmetic and geometric sums -/

-- @region sequences_series.arith_sum
-- @provenance independent
/-- **Sum of an arithmetic progression.** The first `n` terms of `a, a + d, a + 2d, …` add up to
`n(2a + (n − 1)d)/2`: "number of terms times the average of the first and last". Proved by
induction on `n`. -/
theorem arith_sum (a d : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (a + k * d) = n * (2 * a + (n - 1) * d) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
-- @endregion

-- @region sequences_series.geom_telescope
-- @provenance independent
/-- **The telescoping step.** `(1 − r)(1 + r + ⋯ + rⁿ⁻¹) = 1 − rⁿ`: multiplying by `1 − r`
makes every middle term cancel. Proved by induction on `n`. -/
theorem geom_telescope (r : ℝ) (n : ℕ) : (1 - r) * ∑ k ∈ range n, r ^ k = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    ring
-- @endregion

-- @region sequences_series.geom_sum
-- @provenance independent
/-- **Finite geometric sum.** For `r ≠ 1`, `a + ar + ⋯ + arⁿ⁻¹ = a(1 − rⁿ)/(1 − r)`:
divide the telescoping identity by `1 − r ≠ 0`. -/
theorem geom_sum (a r : ℝ) (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, a * r ^ k = a * (1 - r ^ n) / (1 - r) := by
  have h1 : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  rw [← mul_sum, ← geom_telescope r n]
  field_simp
-- @endregion

-- @region sequences_series.geom_sum_library
-- @provenance library
/-- The same sum in Mathlib's form `(rⁿ − 1)/(r − 1)`, from `geom_sum_eq`, which holds in every
division ring. -/
theorem geom_sum_library (r : ℝ) (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, r ^ k = (r ^ n - 1) / (r - 1) :=
  geom_sum_eq hr n
-- @endregion

/-! ### A recursive sequence -/

-- @region sequences_series.hanoi
-- @provenance definition
/-- The **Tower of Hanoi numbers**, defined recursively: no moves for `0` discs, and to move
`n + 1` discs, move `n` discs aside, move the largest disc, and move the `n` discs back on top:
`h(n + 1) = 2 h(n) + 1`. -/
def hanoi : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * hanoi n + 1
-- @endregion

-- @region sequences_series.hanoi_formula
-- @provenance independent
/-- **A closed form for the recursion:** `h(n) + 1 = 2ⁿ`, i.e. `h(n) = 2ⁿ − 1`. Induction:
`h(n + 1) + 1 = 2h(n) + 2 = 2(h(n) + 1) = 2 · 2ⁿ`. (Stated with `+ 1` to avoid natural-number
subtraction.) -/
theorem hanoi_formula (n : ℕ) : hanoi n + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [hanoi, pow_succ, ← ih]
    ring
-- @endregion

/-! ### Infinite geometric series -/

-- @region sequences_series.geom_series_tendsto
-- @provenance independent
/-- **Infinite geometric series.** If `|r| < 1`, the partial sums of `a + ar + ar² + ⋯` tend to
`a/(1 − r)`. The partial sum is `a(1 − rⁿ)/(1 − r)` (`geom_sum`), and `rⁿ → 0` when `|r| < 1`
(Mathlib's `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`), so the partial sums tend to
`a(1 − 0)/(1 − r)`. -/
theorem geom_series_tendsto (a r : ℝ) (hr : |r| < 1) :
    Tendsto (fun n => ∑ k ∈ range n, a * r ^ k) atTop (𝓝 (a / (1 - r))) := by
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, abs_one] at hr
    exact lt_irrefl 1 hr
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hlim : Tendsto (fun n => a * (1 - r ^ n) / (1 - r)) atTop (𝓝 (a * (1 - 0) / (1 - r))) :=
    ((tendsto_const_nhds.sub hpow).const_mul a).div_const (1 - r)
  rw [sub_zero, mul_one] at hlim
  refine hlim.congr (fun n => ?_)
  exact (geom_sum a r hr1 n).symm
-- @endregion

-- @region sequences_series.geom_series_has_sum
-- @provenance library
/-- The same result as a statement about the series: `Σ a rᵏ = a/(1 − r)` for `|r| < 1`. This
applies Mathlib's `hasSum_geometric_of_abs_lt_one` (the case `a = 1`) and multiplies by `a`. -/
theorem geom_series_hasSum (a r : ℝ) (hr : |r| < 1) :
    HasSum (fun n => a * r ^ n) (a / (1 - r)) := by
  rw [div_eq_mul_inv]
  exact (hasSum_geometric_of_abs_lt_one hr).mul_left a
-- @endregion

-- @region sequences_series.halves
-- @provenance library
/-- **`1 + 1/2 + 1/4 + 1/8 + ⋯ = 2`.** This applies Mathlib's `hasSum_geometric_two`. -/
theorem halves : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := hasSum_geometric_two
-- @endregion

-- @region sequences_series.point_nine_recurring
-- @provenance independent
/-- **`0.999… = 1`.** The decimal `0.999…` *means* the series `9/10 + 9/100 + 9/1000 + ⋯`, a
geometric series with first term `9/10` and ratio `1/10`. Its terms are positive, so it converges
to `S` exactly when its partial sums tend to `S`; and by `geom_series_tendsto` they tend to
`(9/10)/(1 − 1/10) = 1`. -/
theorem point_nine_recurring : HasSum (fun n : ℕ => (9 : ℝ) / 10 ^ (n + 1)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have h := geom_series_tendsto (9 / 10) (1 / 10) (by rw [abs_of_pos (by norm_num)]; norm_num)
  norm_num at h
  refine h.congr (fun n => sum_congr rfl (fun k _ => ?_))
  rw [pow_succ, div_pow, one_pow]
  field_simp
-- @endregion

/-! ### Divergence -/

-- @region sequences_series.term_test
-- @provenance library
/-- **The term test.** If `Σ aₙ` converges, then `aₙ → 0`. Equivalently: if the terms do *not*
tend to `0`, the series diverges. This applies Mathlib's `Summable.tendsto_atTop_zero`. The
converse is false — see `harmonic_terms_tend_to_zero_but_diverges`. -/
theorem term_test {f : ℕ → ℝ} (h : Summable f) : Tendsto f atTop (𝓝 0) :=
  h.tendsto_atTop_zero
-- @endregion

-- @region sequences_series.geom_diverges
-- @provenance independent
/-- **If `|r| ≥ 1`, then `Σ rⁿ` diverges.** Its terms satisfy `|rⁿ| = |r|ⁿ ≥ 1`, so they do not
tend to `0`, and the term test rules out convergence. (Mathlib:
`summable_geometric_iff_norm_lt_one`.) -/
theorem geom_diverges (r : ℝ) (hr : 1 ≤ |r|) : ¬ Summable (fun n : ℕ => r ^ n) := by
  intro hs
  have h0 : Tendsto (fun n : ℕ => |r ^ n|) atTop (𝓝 0) := by
    simpa using (term_test hs).abs
  -- Eventually `|rⁿ| < 1`, but every `|rⁿ| = |r|ⁿ ≥ 1`.
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds zero_lt_one))
  have hlt := hN N le_rfl
  rw [abs_pow] at hlt
  exact absurd (one_le_pow₀ hr) (not_le.mpr hlt)
-- @endregion

-- @region sequences_series.harmonic_two_pow
-- @provenance independent
/-- **Oresme's estimate (c. 1350).** `1 + 1/2 + ⋯ + 1/2ⁿ ≥ 1 + n/2`. Group the terms:
the block `1/(2ᵐ + 1) + ⋯ + 1/2ᵐ⁺¹` has `2ᵐ` terms, each at least `1/2ᵐ⁺¹`, so it adds at least
`1/2`. Induction on `n` adds one block at a time. -/
theorem harmonic_two_pow (n : ℕ) :
    1 + (n : ℝ) / 2 ≤ ∑ k ∈ range (2 ^ n), (1 : ℝ) / (k + 1) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ, mul_two, sum_range_add]
    -- The new block: `2ᵐ` terms, each `≥ 1/2ᵐ⁺¹`.
    have hblock : (1 : ℝ) / 2 ≤ ∑ x ∈ range (2 ^ m), (1 : ℝ) / ((2 ^ m + x : ℕ) + 1) := by
      have hterm : ∀ x ∈ range (2 ^ m),
          (1 : ℝ) / (2 ^ (m + 1)) ≤ (1 : ℝ) / ((2 ^ m + x : ℕ) + 1) := by
        intro x hx
        have hx' : x < 2 ^ m := mem_range.mp hx
        apply one_div_le_one_div_of_le (by positivity)
        have : (2 ^ m + x + 1 : ℕ) ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
        exact_mod_cast this
      calc (1 : ℝ) / 2 = ∑ _x ∈ range (2 ^ m), (1 : ℝ) / (2 ^ (m + 1)) := by
            rw [sum_const, card_range, nsmul_eq_mul, pow_succ]
            push_cast
            field_simp
        _ ≤ _ := sum_le_sum hterm
    push_cast at hblock ih ⊢
    linarith
-- @endregion

-- @region sequences_series.harmonic_tendsto_at_top
-- @provenance independent
/-- **The harmonic partial sums grow without bound.** `Hₙ = 1 + 1/2 + ⋯ + 1/n` increases with
`n`, and `H_{2ᵐ} ≥ 1 + m/2` exceeds any given bound for large `m`. An increasing sequence that is
not bounded above tends to infinity. (Mathlib: `Real.tendsto_sum_range_one_div_nat_succ_atTop`.) -/
theorem harmonic_tendsto_atTop :
    Tendsto (fun n => ∑ k ∈ range n, (1 : ℝ) / (k + 1)) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · intro m n hmn
    exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun _ _ _ => by positivity)
  · intro b
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * b)
    refine ⟨2 ^ m, le_trans ?_ (harmonic_two_pow m)⟩
    linarith
-- @endregion

-- @region sequences_series.harmonic_terms_tend_to_zero_but_diverges
-- @provenance independent
/-- **Terms tending to `0` do not guarantee convergence.** The terms `1/(n + 1)` of the harmonic
series tend to `0`, yet the series diverges: if it converged, its partial sums would tend to a
finite limit, but they tend to infinity (`harmonic_tendsto_atTop`). -/
theorem harmonic_terms_tend_to_zero_but_diverges :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) ∧
      ¬ Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
  constructor
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro hs
    exact not_tendsto_nhds_of_tendsto_atTop harmonic_tendsto_atTop _ hs.hasSum.tendsto_sum_nat
-- @endregion

-- @region sequences_series.harmonic_not_summable_library
-- @provenance library
/-- The divergence of the harmonic series in Mathlib's form, `Real.not_summable_one_div_natCast`
(the `n = 0` term is `1/0 = 0` in Lean, which does not affect convergence). -/
theorem harmonic_not_summable_library : ¬ Summable (fun n : ℕ => (1 : ℝ) / n) :=
  Real.not_summable_one_div_natCast
-- @endregion

end Lumenary.SequencesSeries
