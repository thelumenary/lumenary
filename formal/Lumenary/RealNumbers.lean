/-
The Lumenary — formal mathematics
Real numbers and irrationality: √2 is irrational, rational + irrational is irrational, the
triangle inequality, and why the rational numbers are not complete.

Proved here (`@provenance independent`): there are no natural numbers with `p² = 2q²` and
`q ≠ 0` (infinite descent), hence `√2` is irrational; a rational plus an irrational is
irrational; the product of two irrationals can be rational (`√2 · √2 = 2`); the triangle
inequality `|x + y| ≤ |x| + |y|`; and that the set `{q ∈ ℚ | q² < 2}` has no least upper bound
in `ℚ`, using the single rational map `p ↦ (2p + 2)/(p + 2)` that pushes every rational
towards `√2`.

From Mathlib (`@provenance library`): `irrational_sqrt_two`, `irrational_sqrt_natCast_iff`
(`√n` is irrational exactly when `n` is not a perfect square), `abs_add_le`, the completeness of
`ℝ` (`Real.exists_isLUB`) and the density of `ℚ` in `ℝ` (`exists_rat_btwn`).

Note: Mathlib *constructs* `ℝ` from Cauchy sequences of rationals, and `Irrational x` is
*defined* as `x ∉ Set.range ((↑) : ℚ → ℝ)`.
-/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Lumenary.RealNumbers

open Real

/-! ### √2 is irrational -/

-- @region real_numbers.no_nat_sq_eq_two_mul_sq
-- @provenance independent
/-- **Infinite descent.** If `p² = 2q²` for natural numbers `p, q`, then `q = 0`.
Proof by strong induction on `q`: `p²` is even, so `p = 2k`; then `4k² = 2q²`, i.e.
`q² = 2k²`, a *new* solution `(q, k)` with `k < q` (if `q > 0`). The induction hypothesis
gives `k = 0`, so `q² = 0` and `q = 0` after all. -/
theorem no_nat_sq_eq_two_mul_sq : ∀ q p : ℕ, p ^ 2 = 2 * q ^ 2 → q = 0 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p h
    -- `p²` is even, hence `p` is even: `p = k + k`.
    have hp : Even p := (Nat.even_pow.mp (h ▸ even_two_mul (q ^ 2))).1
    obtain ⟨k, rfl⟩ := hp
    -- Dividing by 2: `q² = 2k²`.
    have h2 : q ^ 2 = 2 * k ^ 2 := by nlinarith
    by_contra hq
    -- The new solution is smaller: `k < q`, because `k² < 2k² = q²`.
    have hk : k < q := by
      have hq0 : 0 < q := Nat.pos_of_ne_zero hq
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at h2; omega
        · exact h0
      have : k ^ 2 < q ^ 2 := by nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le q) this
    have hk0 : k = 0 := ih k hk q h2
    subst hk0
    simp at h2
    exact hq h2
-- @endregion

-- @region real_numbers.sqrt_two_irrational
-- @provenance independent
/-- **√2 is irrational**, proved from `no_nat_sq_eq_two_mul_sq`.
Suppose `√2 = r` with `r` rational, and write `r = a/b` in lowest terms (`a = r.num`,
`b = r.den > 0`). Squaring, `a² = 2b²`; taking absolute values gives a solution in natural
numbers with `b ≠ 0`, which infinite descent forbids. -/
theorem sqrt_two_irrational : Irrational (√2) := by
  rintro ⟨r, hr⟩
  -- `r² = 2` in `ℚ`.
  have hr2 : r ^ 2 = 2 := by
    have : ((r ^ 2 : ℚ) : ℝ) = 2 := by
      push_cast
      rw [hr]
      exact Real.sq_sqrt (by norm_num)
    exact_mod_cast this
  -- `a² = 2 b²` in `ℤ`, where `r = a / b`.
  have hint : r.num ^ 2 = 2 * (r.den : ℤ) ^ 2 := by
    have h := Rat.mul_den_eq_num r
    have : ((r.num : ℚ)) ^ 2 = 2 * ((r.den : ℚ)) ^ 2 := by
      rw [← h, mul_pow, hr2]
    exact_mod_cast this
  -- Pass to natural numbers with absolute values.
  have hnat : r.num.natAbs ^ 2 = 2 * r.den ^ 2 := by
    have := congrArg Int.natAbs hint
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  exact r.den_nz (no_nat_sq_eq_two_mul_sq r.den r.num.natAbs hnat)
-- @endregion

-- @region real_numbers.sqrt_two_irrational_library
-- @provenance library
/-- The same theorem from Mathlib: `irrational_sqrt_two`. (Mathlib's proof goes through the
general criterion `irrational_sqrt_natCast_iff` below.) -/
theorem sqrt_two_irrational_library : Irrational (√2) := irrational_sqrt_two
-- @endregion

-- @region real_numbers.sqrt_irrational_iff_not_square
-- @provenance library
/-- **√n for every non-square n.** For a natural number `n`, `√n` is irrational if and only if
`n` is not a perfect square. This applies Mathlib's `irrational_sqrt_natCast_iff`. -/
theorem sqrt_irrational_iff_not_square (n : ℕ) : Irrational (√(n : ℝ)) ↔ ¬ IsSquare n :=
  irrational_sqrt_natCast_iff
-- @endregion

-- @region real_numbers.sqrt_three_irrational
-- @provenance library
/-- An instance of the criterion: `√3` is irrational, since `3` is not a perfect square
(if `3 = r · r` then `r ≤ 2`, and checking `r = 0, 1, 2` finds no square root). -/
theorem sqrt_three_irrational : Irrational (√(3 : ℝ)) := by
  have h : ¬ IsSquare 3 := by
    rintro ⟨r, hr⟩
    have : r ≤ 2 := by nlinarith
    interval_cases r <;> omega
  exact_mod_cast (sqrt_irrational_iff_not_square 3).mpr h
-- @endregion

/-! ### Rational and irrational numbers together -/

-- @region real_numbers.rat_add_irrational
-- @provenance independent
/-- **Rational + irrational = irrational.** If `q + x` were a rational number `r`, then
`x = r - q` would be rational too. (Mathlib: `Irrational.ratCast_add`.) -/
theorem rat_add_irrational (q : ℚ) {x : ℝ} (hx : Irrational x) : Irrational (q + x) := by
  rintro ⟨r, hr⟩
  apply hx
  refine ⟨r - q, ?_⟩
  push_cast
  rw [hr]
  ring
-- @endregion

-- @region real_numbers.irrational_mul_irrational_can_be_rational
-- @provenance independent
/-- **Irrational × irrational can be rational:** `√2` is irrational, yet `√2 · √2 = 2`. -/
theorem irrational_mul_irrational_can_be_rational :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ ¬ Irrational (x * y) := by
  refine ⟨√2, √2, sqrt_two_irrational, sqrt_two_irrational, ?_⟩
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  intro h
  exact h ⟨2, by norm_num⟩
-- @endregion

/-! ### Absolute value -/

-- @region real_numbers.triangle_inequality
-- @provenance independent
/-- **Triangle inequality** `|x + y| ≤ |x| + |y|`. Since `-|x| ≤ x ≤ |x|` and
`-|y| ≤ y ≤ |y|`, adding gives `-(|x| + |y|) ≤ x + y ≤ |x| + |y|`, which says exactly that
`|x + y| ≤ |x| + |y|`. (Mathlib: `abs_add_le`.) -/
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have hx1 := neg_abs_le x
  have hx2 := le_abs_self x
  have hy1 := neg_abs_le y
  have hy2 := le_abs_self y
  rw [abs_le]
  constructor <;> linarith
-- @endregion

-- @region real_numbers.triangle_inequality_library
-- @provenance library
/-- The triangle inequality from Mathlib, `abs_add_le`, which holds in every lattice-ordered
additive commutative group, not only in `ℝ`. -/
theorem triangle_inequality_library (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y
-- @endregion

/-! ### Completeness: ℝ has it, ℚ does not -/

-- @region real_numbers.exists_lub
-- @provenance library
/-- **Completeness of ℝ.** Every non-empty set of real numbers that is bounded above has a least
upper bound. In Mathlib this is a *theorem* about its construction of `ℝ` (`Real.exists_isLUB`);
in many textbooks it is taken as an axiom. -/
theorem exists_lub (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ b, IsLUB S b :=
  Real.exists_isLUB hne hbdd
-- @endregion

-- @region real_numbers.rat_btwn
-- @provenance library
/-- **ℚ is dense in ℝ.** Between any two different real numbers there is a rational number.
This applies Mathlib's `exists_rat_btwn` (it holds in every Archimedean ordered field). -/
theorem rat_btwn {x y : ℝ} (h : x < y) : ∃ q : ℚ, x < q ∧ (q : ℝ) < y :=
  exists_rat_btwn h
-- @endregion

-- @region real_numbers.rat_sq_ne_two
-- @provenance independent
/-- No rational number squares to `2`: if `q² = 2` then `√2 = |q|` would be rational. -/
theorem rat_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro hq
  apply sqrt_two_irrational
  refine ⟨|q|, ?_⟩
  have hq' : ((q : ℝ)) ^ 2 = 2 := by exact_mod_cast hq
  rw [← hq', Real.sqrt_sq_eq_abs]
  push_cast
  rfl
-- @endregion

-- @region real_numbers.push_toward_sqrt_two
-- @provenance independent
/-- The key identity behind the next theorem. For `p > 0` put `p' = (2p + 2)/(p + 2)`. Then
`p' - p = (2 - p²)/(p + 2)` and `p'² - 2 = 2(p² - 2)/(p + 2)²`. So if `p² < 2` then `p'` is
*bigger* than `p` but still has `p'² < 2`; if `p² > 2` then `p'` is *smaller* than `p` but still
has `p'² > 2`. -/
theorem push_toward_sqrt_two (p : ℚ) (hp : 0 < p) :
    (2 * p + 2) / (p + 2) - p = (2 - p ^ 2) / (p + 2) ∧
      ((2 * p + 2) / (p + 2)) ^ 2 - 2 = 2 * (p ^ 2 - 2) / (p + 2) ^ 2 := by
  have h : p + 2 ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  · field_simp
    ring
-- @endregion

-- @region real_numbers.no_rat_lub
-- @provenance independent
/-- **ℚ is not complete.** The set `S = {q ∈ ℚ | q² < 2}` is non-empty (`0 ∈ S`) and bounded
above (by `2`), but it has **no least upper bound in ℚ**.
Suppose `b` were one. Then `b ≥ 1 > 0` because `1 ∈ S`, and `b² ≠ 2` (`rat_sq_ne_two`).
Let `b' = (2b + 2)/(b + 2)`.
* If `b² < 2`, then `b' > b` and `b'² < 2`, so `b' ∈ S` is bigger than the upper bound `b`.
* If `b² > 2`, then `b' < b` and `b'² > 2`, so `b'` is a smaller upper bound than `b`. -/
theorem no_rat_lub : ¬ ∃ b : ℚ, IsLUB {q : ℚ | q ^ 2 < 2} b := by
  rintro ⟨b, hub, hleast⟩
  have hb1 : 1 ≤ b := hub (show (1 : ℚ) ^ 2 < 2 by norm_num)
  have hb : 0 < b := by linarith
  obtain ⟨h1, h2⟩ := push_toward_sqrt_two b hb
  have hden : 0 < b + 2 := by linarith
  set b' := (2 * b + 2) / (b + 2) with hb'
  rcases lt_trichotomy (b ^ 2) 2 with hlt | heq | hgt
  · -- `b' ∈ S` and `b' > b`: `b` is not an upper bound.
    have hbig : b < b' := by
      have : 0 < (2 - b ^ 2) / (b + 2) := div_pos (by linarith) hden
      linarith
    have hin : b' ^ 2 < 2 := by
      have : 2 * (b ^ 2 - 2) / (b + 2) ^ 2 < 0 :=
        div_neg_of_neg_of_pos (by linarith) (by positivity)
      linarith
    exact absurd (hub hin) (not_le.mpr hbig)
  · exact rat_sq_ne_two b heq
  · -- `b'` is a smaller upper bound: `b` is not the least one.
    have hsmall : b' < b := by
      have : (2 - b ^ 2) / (b + 2) < 0 := div_neg_of_neg_of_pos (by linarith) hden
      linarith
    have hpos : 0 < b' := by rw [hb']; positivity
    have hsq : 2 < b' ^ 2 := by
      have : 0 < 2 * (b ^ 2 - 2) / (b + 2) ^ 2 := div_pos (by linarith) (by positivity)
      linarith
    have hupper : b' ∈ upperBounds {q : ℚ | q ^ 2 < 2} := by
      intro s hs
      -- If `s > b' > 0` then `s² > b'² > 2`, so `s ∉ S`.
      by_contra hcon
      have hlt : b' < s := lt_of_not_ge hcon
      have : b' ^ 2 < s ^ 2 := by nlinarith
      have hs' : s ^ 2 < 2 := hs
      linarith
    exact absurd (hleast hupper) (not_le.mpr hsmall)
-- @endregion

-- @region real_numbers.sqrt_two_is_lub_in_reals
-- @provenance independent
/-- In `ℝ` the same set does have a least upper bound, namely `√2`: the gap in `ℚ` is filled.
Every `q ∈ S` has `q ≤ |q| = √(q²) < √2`; and if `c < √2` is any real number, density gives a
rational `q` with `max c 0 < q < √2`, so `q² < 2` and `q > c`: `c` is not an upper bound. -/
theorem sqrt_two_is_lub_in_reals :
    IsLUB {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ q ^ 2 < 2} (√2) := by
  constructor
  · rintro x ⟨q, rfl, hq⟩
    have hq' : ((q : ℝ)) ^ 2 < 2 := by exact_mod_cast hq
    calc (q : ℝ) ≤ |(q : ℝ)| := le_abs_self _
      _ = √((q : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √2 := Real.sqrt_le_sqrt hq'.le
  · intro c hc
    by_contra hlt
    push Not at hlt
    have h0 : max c 0 < √2 := max_lt hlt (by positivity)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h0
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right c 0) hq1
    have hsq : ((q : ℝ)) ^ 2 < 2 := by
      have := pow_lt_pow_left₀ hq2 hqpos.le (two_ne_zero)
      rwa [Real.sq_sqrt (by norm_num)] at this
    have hmem : (q : ℝ) ∈ {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ q ^ 2 < 2} :=
      ⟨q, rfl, by exact_mod_cast hsq⟩
    have := hc hmem
    linarith [le_max_left c 0]
-- @endregion

end Lumenary.RealNumbers
