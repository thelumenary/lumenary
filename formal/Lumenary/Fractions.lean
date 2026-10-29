/-
The Lumenary — formal mathematics
Fractions and decimals: equivalent fractions, comparing, adding, decimals, and why 1/3 has
no finite decimal.

Core Lean 4 only (no Mathlib). We build a small model of fractions by hand: a fraction is a
pair of whole numbers `num / den` with `den > 0`, and two fractions are *equivalent* when
they pass the cross-multiplication test `a × d = c × b`. Everything the lesson proves about
equivalent fractions, comparison and addition is then proved for this model. Core Lean also
has a real number type of fractions, `Rat` (Mathlib uses the same type and calls it `ℚ`);
a few facts at the end are checked there, and `Rat.divInt_eq_divInt_iff` is core's version of
the cross-multiplication test.
-/

namespace Lumenary.Fractions

/-! ### A fraction, and when two fractions are equal -/

-- @region fractions.frac
-- @provenance definition
/-- A fraction `num / den` of whole numbers. The denominator must not be `0`: it says how
many equal parts the whole is cut into. -/
structure Frac where
  /-- The numerator: how many parts we take. -/
  num : Nat
  /-- The denominator: how many equal parts make one whole. -/
  den : Nat
  /-- A whole cannot be cut into `0` parts. -/
  den_pos : 0 < den
-- @endregion

-- @region fractions.mk_frac
-- @provenance definition
/-- `frac a b` is the fraction `a / b`. When `b` is a numeral, Lean checks `0 < b` by itself. -/
def frac (a b : Nat) (h : 0 < b := by decide) : Frac := ⟨a, b, h⟩
-- @endregion

-- @region fractions.equiv
-- @provenance definition
/-- `a / b` and `c / d` are **equivalent** (they are the same number) when `a × d = c × b`:
written over the common denominator `b × d`, they have the same numerator. -/
def Frac.Equiv (x y : Frac) : Prop := x.num * y.den = y.num * x.den
-- @endregion

-- @region fractions.inst_has_equiv
-- @provenance definition
/-- Lets us write `x ≈ y` for "`x` and `y` are equivalent fractions". -/
instance instHasEquiv : HasEquiv Frac := ⟨Frac.Equiv⟩
-- @endregion

-- @region fractions.inst_decidable_equiv
-- @provenance definition
/-- Equivalence of two particular fractions can be decided by multiplying, so `decide` can
check statements such as `frac 2 4 ≈ frac 1 2`. -/
instance instDecidableEquiv (x y : Frac) : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (x.num * y.den = y.num * x.den))
-- @endregion

-- @region fractions.scale_equiv
-- @provenance independent
/-- Multiplying the numerator and the denominator by the same `n > 0` gives an equivalent
fraction: `(n × a) / (n × b) = a / b`. Cutting every part into `n` smaller parts makes `n`
times as many parts, each `n` times smaller. -/
theorem scale_equiv (a b n : Nat) (hb : 0 < b) (hn : 0 < n) :
    frac (n * a) (n * b) (Nat.mul_pos hn hb) ≈ frac a b hb := by
  -- Unfolded, the claim is `(n × a) × b = a × (n × b)`: reorder the product.
  change n * a * b = a * (n * b)
  rw [Nat.mul_comm n a, Nat.mul_assoc]
-- @endregion

-- @region fractions.equiv_refl
-- @provenance independent
/-- Every fraction is equivalent to itself. -/
theorem equiv_refl (x : Frac) : x ≈ x := rfl
-- @endregion

-- @region fractions.equiv_symm
-- @provenance independent
/-- If `x` is equivalent to `y`, then `y` is equivalent to `x`. -/
theorem equiv_symm {x y : Frac} (h : x ≈ y) : y ≈ x := h.symm
-- @endregion

-- @region fractions.equiv_trans
-- @provenance independent
/-- If `a/b ≈ c/d` and `c/d ≈ e/f`, then `a/b ≈ e/f`. We multiply out, use both facts, and
cancel the factor `d`, which is allowed because `d > 0` (`Nat.eq_of_mul_eq_mul_right`).
`ac_rfl` reorders a product; multiplication is commutative and associative. -/
theorem equiv_trans {x y z : Frac} (h1 : x ≈ y) (h2 : y ≈ z) : x ≈ z := by
  obtain ⟨a, b, _⟩ := x
  obtain ⟨c, d, hd⟩ := y
  obtain ⟨e, f, _⟩ := z
  change a * d = c * b at h1
  change c * f = e * d at h2
  change a * f = e * b
  apply Nat.eq_of_mul_eq_mul_right hd
  calc a * f * d = (a * d) * f := by ac_rfl
    _ = (c * b) * f := by rw [h1]
    _ = (c * f) * b := by ac_rfl
    _ = (e * d) * b := by rw [h2]
    _ = e * b * d := by ac_rfl
-- @endregion

-- @region fractions.two_quarters
-- @provenance independent
/-- `2/4`, `3/6` and `50/100` are all equivalent to `1/2`. -/
theorem two_quarters : frac 2 4 ≈ frac 1 2 ∧ frac 3 6 ≈ frac 1 2 ∧ frac 50 100 ≈ frac 1 2 := by
  decide
-- @endregion

/-! ### Comparing fractions -/

-- @region fractions.lt
-- @provenance definition
/-- `a / b < c / d` when `a × d < c × b`: over the common denominator `b × d`, the first
numerator is smaller. -/
def Frac.Lt (x y : Frac) : Prop := x.num * y.den < y.num * x.den
-- @endregion

-- @region fractions.inst_lt
-- @provenance definition
/-- Lets us write `x < y` for fractions. -/
instance instLT : LT Frac := ⟨Frac.Lt⟩
-- @endregion

-- @region fractions.inst_decidable_lt
-- @provenance definition
/-- Comparing two particular fractions is a calculation, so `decide` can do it. -/
instance instDecidableLt (x y : Frac) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.num * y.den < y.num * x.den))
-- @endregion

-- @region fractions.same_den_lt
-- @provenance independent
/-- With the same denominator, the fraction with the bigger numerator is bigger:
`a / b < c / b` exactly when `a < c` (same-sized pieces, so compare how many). -/
theorem same_den_lt (a c b : Nat) (hb : 0 < b) : frac a b hb < frac c b hb ↔ a < c := by
  change a * b < c * b ↔ a < c
  exact Nat.mul_lt_mul_right hb
-- @endregion

-- @region fractions.bigger_den_smaller_piece
-- @provenance independent
/-- A bigger denominator means a *smaller* piece: if `b < d` then `1/d < 1/b`.
Cutting the whole into more parts makes each part smaller. -/
theorem bigger_den_smaller_piece (b d : Nat) (hb : 0 < b) (hd : 0 < d) (h : b < d) :
    frac 1 d hd < frac 1 b hb := by
  change 1 * b < 1 * d
  rw [Nat.one_mul, Nat.one_mul]
  exact h
-- @endregion

-- @region fractions.three_quarters_gt_two_thirds
-- @provenance independent
/-- `2/3 < 3/4`, because over the common denominator `12` they are `8/12` and `9/12`. -/
theorem three_quarters_gt_two_thirds : frac 2 3 < frac 3 4 := by decide
-- @endregion

/-! ### Adding fractions -/

-- @region fractions.add
-- @provenance definition
/-- `a/b + c/d = (a × d + c × b) / (b × d)`: rewrite both fractions over the common
denominator `b × d`, then add the numerators. -/
def Frac.add (x y : Frac) : Frac :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩
-- @endregion

-- @region fractions.half_plus_third
-- @provenance independent
/-- `1/2 + 1/3 = 5/6`. The rule gives `(1 × 3 + 1 × 2) / (2 × 3) = 5/6`. -/
theorem half_plus_third : (frac 1 2).add (frac 1 3) ≈ frac 5 6 := by decide
-- @endregion

-- @region fractions.half_plus_third_not_two_fifths
-- @provenance independent
/-- Adding tops and bottoms is wrong: `1/2 + 1/3` is **not** `2/5`. In fact `2/5` is smaller
than `1/2`, and a sum of two positive fractions must be bigger than each of them. -/
theorem half_plus_third_not_two_fifths :
    ¬ ((frac 1 2).add (frac 1 3) ≈ frac 2 5) ∧ frac 2 5 < frac 1 2 := by decide
-- @endregion

-- @region fractions.add_respects_equiv
-- @provenance independent
/-- The answer to an addition does not depend on which equivalent fractions we use:
if `x ≈ x'` and `y ≈ y'` then `x + y ≈ x' + y'`. So adding `2/4 + 1/3` gives the same number
as `1/2 + 1/3`. The proof multiplies out and uses the two cross-multiplication facts. -/
theorem add_respects_equiv {x x' y y' : Frac} (hx : x ≈ x') (hy : y ≈ y') :
    x.add y ≈ x'.add y' := by
  obtain ⟨a, b, _⟩ := x
  obtain ⟨a', b', _⟩ := x'
  obtain ⟨c, d, _⟩ := y
  obtain ⟨c', d', _⟩ := y'
  change a * b' = a' * b at hx
  change c * d' = c' * d at hy
  change (a * d + c * b) * (b' * d') = (a' * d' + c' * b') * (b * d)
  calc (a * d + c * b) * (b' * d') = (a * b') * (d * d') + (c * d') * (b * b') := by
          rw [Nat.add_mul]; ac_rfl
    _ = (a' * b) * (d * d') + (c' * d) * (b * b') := by rw [hx, hy]
    _ = (a' * d' + c' * b') * (b * d) := by rw [Nat.add_mul]; ac_rfl
-- @endregion

-- @region fractions.nat_mul
-- @provenance definition
/-- A whole number times a fraction: `n × (a / b) = (n × a) / b`, that is, `n` groups of
`a` pieces of size `1/b`. -/
def Frac.natMul (n : Nat) (x : Frac) : Frac := ⟨n * x.num, x.den, x.den_pos⟩
-- @endregion

-- @region fractions.four_times_two_thirds
-- @provenance independent
/-- `4 × 2/3 = 8/3`, which is `2 2/3`: eight thirds, or two wholes and two thirds. -/
theorem four_times_two_thirds : (frac 2 3).natMul 4 ≈ frac 8 3 := by decide
-- @endregion

/-! ### Decimals -/

-- @region fractions.decimals_compare
-- @provenance independent
/-- `0.25 < 0.3`: as fractions, `25/100 < 3/10`, because `3/10 = 30/100`. -/
theorem decimals_compare : frac 25 100 < frac 3 10 ∧ frac 3 10 ≈ frac 30 100 := by decide
-- @endregion

-- @region fractions.eighth_as_decimal
-- @provenance independent
/-- `1/8 = 125/1000 = 0.125` and `3/8 = 375/1000 = 0.375`: since `8 × 125 = 1000`,
eighths can be written as thousandths. -/
theorem eighth_as_decimal : frac 1 8 ≈ frac 125 1000 ∧ frac 3 8 ≈ frac 375 1000 := by decide
-- @endregion

-- @region fractions.ten_pow_mod_three
-- @provenance independent
/-- Every power of ten leaves remainder `1` when divided by `3`: `10 = 9 + 1`,
`100 = 99 + 1`, `1000 = 999 + 1`, … Proved by induction, using that the remainder of a
product depends only on the remainders of the factors (`Nat.mul_mod`). -/
theorem ten_pow_mod_three (k : Nat) : 10 ^ k % 3 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
-- @endregion

-- @region fractions.third_not_terminating
-- @provenance independent
/-- `1/3` has no finite decimal: there are no `m` and `k` with `1/3 = m / 10^k`.
By cross-multiplication that would mean `10^k = 3 × m`, a multiple of `3`, but every power
of ten leaves remainder `1` when divided by `3`. -/
theorem third_not_terminating (m k : Nat) :
    ¬ (frac 1 3 ≈ frac m (10 ^ k) (Nat.pow_pos (by decide))) := by
  intro h
  change 1 * 10 ^ k = m * 3 at h
  have hrem : 10 ^ k % 3 = m * 3 % 3 := by rw [← h, Nat.one_mul]
  rw [ten_pow_mod_three, Nat.mul_mod_left] at hrem
  -- `hrem : 1 = 0`, which is false.
  exact absurd hrem (by decide)
-- @endregion

/-! ### Lean's built-in fractions -/

-- @region fractions.rat_cross_mul
-- @provenance library
/-- In Lean's own type of fractions `Rat`, `a/b = c/d` exactly when `a × d = c × b`
(for nonzero `b`, `d`). This applies core Lean's theorem `Rat.divInt_eq_divInt_iff`. -/
theorem rat_cross_mul {a b c d : Int} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : Rat) / b = c / d ↔ a * d = c * b := by
  rw [← Rat.divInt_eq_div, ← Rat.divInt_eq_div]
  exact Rat.divInt_eq_divInt_iff hb hd
-- @endregion

-- @region fractions.rat_examples
-- @provenance independent
/-- The lesson's examples in Lean's `Rat`: `1/2 + 1/3 = 5/6`, `1/2 + 1/3 ≠ 2/5`,
`0.25 < 0.3` and `0.125 = 1/8`. The kernel evaluates both sides exactly. -/
theorem rat_examples :
    (1 : Rat) / 2 + 1 / 3 = 5 / 6 ∧ (1 : Rat) / 2 + 1 / 3 ≠ 2 / 5 ∧
      (0.25 : Rat) < 0.3 ∧ (0.125 : Rat) = 1 / 8 := by
  decide +kernel
-- @endregion

end Lumenary.Fractions
