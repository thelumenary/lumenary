/-
The Lumenary — formal mathematics
Rational numbers: quotients of integers, closure, reciprocals, density, decimal expansions,
and a number that is not rational.

Core Lean 4 already contains the rational numbers as the type `Rat` (written `ℚ` in Mathlib).
A value of `Rat` is stored as a fraction in lowest terms: an integer numerator `num`, a positive
natural-number denominator `den`, and a proof that they have no common factor. Core Lean also
proves the field laws for `Rat` (`Rat.mul_inv_cancel`, `Rat.add_comm`, …).

Here we prove the lesson's results: every sum, product and quotient of fractions of integers is
again such a fraction (`@provenance independent`), every non-zero rational has a reciprocal
(both an independent and a `library` version), the average of two rationals lies strictly
between them, the remainders in long division must eventually repeat (so every decimal
expansion of a fraction is eventually periodic), a repeating decimal is a fraction, and there
is no rational number whose square is 2. Several algebraic steps are closed by `grind`, core
Lean's automatic prover, which knows the field axioms for `Rat`.
Mathlib analogues: `Rat`, `Rat.num_div_den`, `mul_inv_cancel₀`, `exists_between`,
`irrational_sqrt_two`.
-/

namespace Lumenary.RationalNumbers

/-! ### Rational numbers are quotients of integers -/

-- @region rational_numbers.is_quotient
-- @provenance definition
/-- A number `x` is a *quotient of integers* if `x = m / n` for some integers `m` and `n`
with `n ≠ 0`. This is the lesson's definition of a rational number. -/
def IsQuotient (x : Rat) : Prop := ∃ m n : Int, n ≠ 0 ∧ x = (m : Rat) / (n : Rat)
-- @endregion

-- @region rational_numbers.int_cast_ne_zero
-- @provenance library
/-- A non-zero integer stays non-zero when viewed as a rational number.
This applies core Lean's simp lemma `Rat.intCast_eq_zero_iff`. -/
theorem int_cast_ne_zero {n : Int} (h : n ≠ 0) : (n : Rat) ≠ 0 := by
  simpa using h
-- @endregion

-- @region rational_numbers.every_rat_is_quotient
-- @provenance library
/-- Every value of Lean's type `Rat` is a quotient of integers: `q = q.num / q.den`.
So Lean's `Rat` really is the set of fractions of the lesson. This applies the core lemmas
`Rat.num_divInt_den` and `Rat.divInt_eq_div`. -/
theorem every_rat_is_quotient (q : Rat) : IsQuotient q := by
  refine ⟨q.num, (q.den : Int), ?_, ?_⟩
  · exact Int.ofNat_ne_zero.mpr q.den_nz
  · rw [← Rat.divInt_eq_div]
    exact (Rat.num_divInt_den q).symm
-- @endregion

-- @region rational_numbers.add_formula
-- @provenance independent
/-- The rule for adding fractions: `a/b + c/d = (a·d + b·c)/(b·d)` when `b, d ≠ 0`.
Rewrite both fractions over the common denominator `b·d`, then add the numerators. -/
theorem add_formula (a b c d : Int) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : Rat) / b + (c : Rat) / d = ((a * d + b * c : Int) : Rat) / ((b * d : Int) : Rat) := by
  have hb' := int_cast_ne_zero hb
  have hd' := int_cast_ne_zero hd
  push_cast
  calc (a : Rat) / b + (c : Rat) / d
      = (a * d) / (b * d) + (b * c) / (b * d) := by grind
    _ = (a * d + b * c) / (b * d) := by grind
-- @endregion

-- @region rational_numbers.closed_add
-- @provenance independent
/-- **Closure under addition.** The sum of two quotients of integers is a quotient of
integers: the witness is the numerator `a·d + b·c` over the denominator `b·d` from
`add_formula`, and `b·d ≠ 0` because neither factor is zero. -/
theorem closed_add {x y : Rat} (hx : IsQuotient x) (hy : IsQuotient y) :
    IsQuotient (x + y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  exact ⟨a * d + b * c, b * d, Int.mul_ne_zero hb hd, add_formula a b c d hb hd⟩
-- @endregion

-- @region rational_numbers.closed_mul
-- @provenance independent
/-- **Closure under multiplication.** `(a/b)·(c/d) = (a·c)/(b·d)`, again a quotient of
integers with non-zero denominator. -/
theorem closed_mul {x y : Rat} (hx : IsQuotient x) (hy : IsQuotient y) :
    IsQuotient (x * y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  have hb' := int_cast_ne_zero hb
  have hd' := int_cast_ne_zero hd
  refine ⟨a * c, b * d, Int.mul_ne_zero hb hd, ?_⟩
  push_cast
  grind
-- @endregion

-- @region rational_numbers.closed_div
-- @provenance independent
/-- **Closure under division by a non-zero number.** If `y = c/d ≠ 0` then `c ≠ 0`, and
`(a/b) ÷ (c/d) = (a/b)·(d/c) = (a·d)/(b·c)`: divide by multiplying by the reciprocal. -/
theorem closed_div {x y : Rat} (hx : IsQuotient x) (hy : IsQuotient y) (hy0 : y ≠ 0) :
    IsQuotient (x / y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  have hb' := int_cast_ne_zero hb
  have hd' := int_cast_ne_zero hd
  have hc : c ≠ 0 := by
    intro hc
    apply hy0
    subst hc
    simp [Rat.div_def]
  have hc' := int_cast_ne_zero hc
  refine ⟨a * d, b * c, Int.mul_ne_zero hb hc, ?_⟩
  push_cast
  grind
-- @endregion

/-! ### Reciprocals -/

-- @region rational_numbers.mul_reciprocal
-- @provenance independent
/-- The reciprocal of `a/b` is `b/a`: if `a, b ≠ 0` then `(a/b)·(b/a) = (a·b)/(b·a) = 1`. -/
theorem mul_reciprocal (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((a : Rat) / b) * ((b : Rat) / a) = 1 := by
  have ha' := int_cast_ne_zero ha
  have hb' := int_cast_ne_zero hb
  calc ((a : Rat) / b) * ((b : Rat) / a)
      = ((a : Rat) * b) / ((b : Rat) * a) := by grind
    _ = 1 := by grind
-- @endregion

-- @region rational_numbers.reciprocal_exists
-- @provenance library
/-- Every non-zero rational number has a multiplicative inverse in `Rat`, unlike in `Int`
(where only `1` and `-1` do). This applies core Lean's `Rat.mul_inv_cancel`. -/
theorem reciprocal_exists (q : Rat) (hq : q ≠ 0) : ∃ r : Rat, q * r = 1 :=
  ⟨q⁻¹, Rat.mul_inv_cancel q hq⟩
-- @endregion

-- @region rational_numbers.zero_no_reciprocal
-- @provenance independent
/-- Zero has no reciprocal: `0 · r = 0 ≠ 1` for every `r`. -/
theorem zero_no_reciprocal : ¬ ∃ r : Rat, 0 * r = 1 := by
  intro ⟨r, h⟩
  rw [Rat.zero_mul] at h
  exact absurd h (by decide)
-- @endregion

-- @region rational_numbers.div_half
-- @provenance independent
/-- Dividing by `1/2` doubles: `x ÷ (1/2) = 2x`. Division is multiplication by the reciprocal,
and the reciprocal of `1/2` is `2`. -/
theorem div_half (x : Rat) : x / (1 / 2) = 2 * x := by
  grind
-- @endregion

/-! ### Density: there is no "next" rational number -/

-- @region rational_numbers.average_between
-- @provenance independent
/-- If `a < b` then the average `(a + b)/2` lies strictly between them:
`a = (a + a)/2 < (a + b)/2 < (b + b)/2 = b`. -/
theorem average_between {a b : Rat} (h : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b := by
  have two_pos : (0 : Rat) < 2 := by decide
  constructor
  · -- `a < (a + b)/2` is the same as `a · 2 < a + b`, i.e. `a + a < a + b`.
    rw [Rat.lt_div_iff two_pos]
    have : a + a < a + b := Rat.add_lt_add_left.mpr h
    grind
  · -- `(a + b)/2 < b` is the same as `a + b < b · 2`, i.e. `a + b < b + b`.
    rw [Rat.div_lt_iff two_pos]
    have : a + b < b + b := Rat.add_lt_add_right.mpr h
    grind
-- @endregion

-- @region rational_numbers.exists_between
-- @provenance independent
/-- **Density of the rationals.** Between any two different rationals there is a third, so no
rational number has a "next" one. The witness is the average (`average_between`). -/
theorem exists_between {a b : Rat} (h : a < b) : ∃ c : Rat, a < c ∧ c < b :=
  ⟨(a + b) / 2, average_between h⟩
-- @endregion

/-! ### Decimal expansions by long division -/

-- @region rational_numbers.rem
-- @provenance definition
/-- The remainders in the long division of `a` by `b`. Start with `a % b`; at each step
"bring down a zero": multiply the remainder by `10` and take the remainder on division by `b`. -/
def rem (a b : Nat) : Nat → Nat
  | 0 => a % b
  | k + 1 => (10 * rem a b k) % b
-- @endregion

-- @region rational_numbers.digit
-- @provenance definition
/-- The digit produced at step `k + 1` of the long division of `a` by `b`: how many times `b`
goes into ten times the current remainder. `digit a b 0` is the first digit after the point. -/
def digit (a b k : Nat) : Nat := (10 * rem a b k) / b
-- @endregion

-- @region rational_numbers.rem_eq
-- @provenance independent
/-- The `k`-th remainder is the remainder of `a · 10^k` on division by `b`: long division
really is computing `a · 10^k` modulo `b`. Proof by induction, using `(x % b) · 10 ≡ x · 10`. -/
theorem rem_eq (a b k : Nat) : rem a b k = a * 10 ^ k % b := by
  induction k with
  | zero => simp [rem]
  | succ k ih =>
    rw [rem, ih, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]
    congr 1
    rw [Nat.mul_comm 10, Nat.mul_assoc]
-- @endregion

-- @region rational_numbers.rem_lt
-- @provenance library
/-- Every remainder is less than `b`, so there are only `b` possible remainders.
This applies core Lean's `Nat.mod_lt`. -/
theorem rem_lt (a b k : Nat) (hb : 0 < b) : rem a b k < b := by
  cases k <;> exact Nat.mod_lt _ hb
-- @endregion

-- @region rational_numbers.digit_lt_ten
-- @provenance independent
/-- Each digit really is a digit, `0`–`9`: the remainder `r` is less than `b`, so
`10 · r < 10 · b` and `(10 · r) / b < 10`. -/
theorem digit_lt_ten (a b k : Nat) (hb : 0 < b) : digit a b k < 10 := by
  have hr := rem_lt a b k hb
  unfold digit
  rw [Nat.div_lt_iff_lt_mul hb]
  omega
-- @endregion

-- @region rational_numbers.rem_periodic
-- @provenance independent
/-- Once a remainder repeats, everything after it repeats: each remainder is computed from the
one before, so if `rem i = rem j` then `rem (i + n) = rem (j + n)` for every `n`. -/
theorem rem_periodic (a b : Nat) {i j : Nat} (h : rem a b i = rem a b j) :
    ∀ n, rem a b (i + n) = rem a b (j + n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [← Nat.add_assoc, ← Nat.add_assoc, rem, rem, ih]
-- @endregion

-- @region rational_numbers.pigeonhole
-- @provenance independent
/-- **The pigeonhole principle** for the values `f 0, f 1, …, f b`: if all `b + 1` of them are
less than `b`, two of them are equal. Proof by induction on `b`: either `f (b + 1)` already
appeared, or we relabel the value `b` as `f (b + 1)` and use the induction hypothesis. -/
theorem pigeonhole : ∀ (b : Nat) (f : Nat → Nat), (∀ k, k ≤ b → f k < b) →
    ∃ i j, i < j ∧ j ≤ b ∧ f i = f j := by
  intro b
  induction b with
  | zero =>
    intro f hf
    exact absurd (hf 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | succ b ih =>
    intro f hf
    by_cases hrep : ∃ k, k ≤ b ∧ f k = f (b + 1)
    · obtain ⟨k, hk, hfk⟩ := hrep
      exact ⟨k, b + 1, by omega, Nat.le_refl _, hfk⟩
    · -- `f (b + 1)` is new. Replace the value `b` (if it occurs) by `f (b + 1)`.
      have hnew : ∀ k, k ≤ b → f k ≠ f (b + 1) := fun k hk h => hrep ⟨k, hk, h⟩
      let g : Nat → Nat := fun k => if f k = b then f (b + 1) else f k
      have hg : ∀ k, k ≤ b → g k < b := by
        intro k hk
        have h1 := hf k (by omega)
        have h2 := hf (b + 1) (Nat.le_refl _)
        have h3 := hnew k hk
        simp only [g]
        split <;> omega
      obtain ⟨i, j, hij, hjb, hgij⟩ := ih g hg
      refine ⟨i, j, hij, by omega, ?_⟩
      have hi := hnew i (by omega)
      have hj := hnew j hjb
      simp only [g] at hgij
      split at hgij <;> split at hgij <;> omega
-- @endregion

-- @region rational_numbers.remainder_repeats
-- @provenance independent
/-- In the long division of `a` by `b > 0`, some remainder repeats within the first `b + 1`
steps: the remainders take at most `b` values (`rem_lt`), so `pigeonhole` applies. -/
theorem remainder_repeats (a b : Nat) (hb : 0 < b) :
    ∃ i j, i < j ∧ j ≤ b ∧ rem a b i = rem a b j :=
  pigeonhole b (rem a b) (fun k _ => rem_lt a b k hb)
-- @endregion

-- @region rational_numbers.decimal_eventually_periodic
-- @provenance independent
/-- **The decimal expansion of `a/b` is eventually periodic.** There is a starting place `i`
and a period `p` with `1 ≤ p ≤ b` such that the digits repeat with period `p` from place `i`
on. (A terminating decimal is the case where the repeating block is `0`.) -/
theorem decimal_eventually_periodic (a b : Nat) (hb : 0 < b) :
    ∃ i p, 0 < p ∧ p ≤ b ∧ ∀ n, digit a b (i + p + n) = digit a b (i + n) := by
  obtain ⟨i, j, hij, hjb, h⟩ := remainder_repeats a b hb
  refine ⟨i, j - i, by omega, by omega, ?_⟩
  intro n
  have hji : i + (j - i) = j := by omega
  unfold digit
  rw [hji, rem_periodic a b h.symm n]
-- @endregion

-- @region rational_numbers.one_seventh_digits
-- @provenance independent
/-- The first twelve digits of `1/7 = 0.142857142857…`, computed by the long-division
definitions above and checked by evaluation. -/
theorem one_seventh_digits :
    (List.range 12).map (digit 1 7) = [1, 4, 2, 8, 5, 7, 1, 4, 2, 8, 5, 7] := by
  decide
-- @endregion

/-! ### From a repeating decimal back to a fraction -/

-- @region rational_numbers.repeating_to_fraction
-- @provenance independent
/-- If shifting the decimal point `k ≥ 1` places gives the repeating block `D` plus the
number itself, `10^k · x = D + x`, then `x = D / (10^k - 1)`. For `x = 0.272727…`,
`100x = 27 + x`, so `x = 27/99`. -/
theorem repeating_to_fraction (x D : Rat) (k : Nat) (hk : 1 ≤ k) (h : 10 ^ k * x = D + x) :
    x = D / (10 ^ k - 1) := by
  have hpow : (10 : Rat) ≤ 10 ^ k := by
    have h10 : (10 : Nat) ≤ 10 ^ k := by
      calc 10 = 10 ^ 1 := rfl
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
    have := Rat.natCast_le_natCast.mpr h10
    simpa using this
  have hne : (10 : Rat) ^ k - 1 ≠ 0 := by
    intro h0
    have : (10 : Rat) ^ k = 1 := by grind
    rw [this] at hpow
    exact absurd hpow (by decide)
  grind
-- @endregion

-- @region rational_numbers.point_27_repeating
-- @provenance independent
/-- `0.272727… = 3/11`: from `100x = 27 + x` we get `99x = 27`, so `x = 27/99 = 3/11`. -/
theorem point_27_repeating (x : Rat) (h : 100 * x = 27 + x) : x = 3 / 11 := by
  grind
-- @endregion

-- @region rational_numbers.nines_gap
-- @provenance independent
/-- The number `0.99…9` with `n` nines is `1 - 1/10^n`: its gap below `1` is exactly
`1/10^n`. As `n` grows, this gap becomes smaller than any positive number. -/
theorem nines_gap (n : Nat) : 1 - ((10 : Rat) ^ n - 1) / 10 ^ n = 1 / 10 ^ n := by
  have hpos : (0 : Rat) < 10 ^ n := Rat.pow_pos (by decide)
  have hne : (10 : Rat) ^ n ≠ 0 := Rat.ne_of_gt hpos
  grind
-- @endregion

-- @region rational_numbers.gap_lt_every_positive
-- @provenance independent
/-- For every positive rational `ε` there is an `n` with `1/10^n < ε`. Together with `nines_gap`
this is why `0.999… = 1`: the distance from `0.999…` up to `1` is below every positive
number, so it is `0`. Proof: take `n = ⌈1/ε⌉`; then `1/ε ≤ n < 10^n`. -/
theorem gap_lt_every_positive (ε : Rat) (hε : 0 < ε) : ∃ n : Nat, 1 / (10 : Rat) ^ n < ε := by
  refine ⟨(1 / ε).ceil.toNat, ?_⟩
  have hinvpos : 0 < 1 / ε := by
    rw [Rat.lt_div_iff hε]
    simpa using (show (0 : Rat) < 1 by decide)
  have hceil : 1 / ε ≤ ((1 / ε).ceil : Rat) := Rat.le_ceil
  have hceil_nonneg : 0 ≤ (1 / ε).ceil := by
    have : (0 : Rat) ≤ ((1 / ε).ceil : Rat) := Rat.le_trans (Rat.le_of_lt hinvpos) hceil
    exact Rat.intCast_nonneg.mp this
  have hcast : (((1 / ε).ceil.toNat : Nat) : Rat) = ((1 / ε).ceil : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hceil_nonneg]
  have hpow : ((1 / ε).ceil.toNat : Rat) < (10 : Rat) ^ (1 / ε).ceil.toNat := by
    have := Rat.natCast_lt_natCast.mpr
      (Nat.lt_pow_self (n := (1 / ε).ceil.toNat) (a := 10) (by decide))
    simpa using this
  have hlt : 1 / ε < (10 : Rat) ^ (1 / ε).ceil.toNat := by
    rw [hcast] at hpow
    grind
  have h10pos : (0 : Rat) < 10 ^ (1 / ε).ceil.toNat := Rat.pow_pos (by decide)
  rw [Rat.div_lt_iff h10pos]
  rw [Rat.div_lt_iff hε] at hlt
  grind
-- @endregion

/-! ### A gap in the rational line: no rational squares to 2 -/

-- @region rational_numbers.even_of_sq_even
-- @provenance independent
/-- If `a · a` is even then `a` is even: an odd number times an odd number is odd. -/
theorem even_of_sq_even (a : Nat) (h : a * a % 2 = 0) : a % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
  · exact h0
  · rw [Nat.mul_mod, h1] at h
    exact absurd h (by decide)
-- @endregion

-- @region rational_numbers.sq_two_descent
-- @provenance independent
/-- **No whole-number solution to `a² = 2b²` except `b = 0`** (Fermat's infinite descent).
If `a² = 2b²` with `b > 0`, then `a` is even, `a = 2c`, so `b² = 2c²`: a smaller solution
`(b, c)`, since `b < a`. Smaller and smaller solutions cannot go on for ever. -/
theorem sq_two_descent : ∀ a b : Nat, a * a = 2 * (b * b) → b = 0 := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b hab
    -- `a` is even.
    have heven : a % 2 = 0 := by
      apply even_of_sq_even
      rw [hab, Nat.mul_mod_right]
    obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
    -- Cancel a factor 2: `b * b = 2 * (c * c)`.
    have hbc : b * b = 2 * (c * c) := by
      have h4 : 2 * (2 * (c * c)) = 2 * (b * b) := by
        rw [← hab]; grind
      omega
    by_cases hb : b = 0
    · exact hb
    · -- `b < 2c`, because `b ≥ 2c` would give `b² ≥ 4c² > 2c²`.
      have hlt : b < 2 * c := by
        apply Nat.lt_of_not_le
        intro hle
        have hsq : (2 * c) * (2 * c) ≤ b * b := Nat.mul_le_mul hle hle
        have hbpos : 0 < b * b := Nat.mul_pos (by omega) (by omega)
        omega
      have hc : c = 0 := ih b hlt c hbc
      subst hc
      simp at hbc
      exact (Nat.mul_eq_zero.mp hbc).elim id id
-- @endregion

-- @region rational_numbers.no_rat_sq_two
-- @provenance independent
/-- **There is no rational number whose square is 2.** Writing `q = num/den`, `q² = 2` gives
`num² = 2 · den²`; taking absolute values gives whole numbers `a, b` with `a² = 2b²` and
`b = den ≠ 0`, which `sq_two_descent` rules out. So the rational number line has a gap
where `√2` should be. -/
theorem no_rat_sq_two : ¬ ∃ q : Rat, q * q = 2 := by
  intro ⟨q, hq⟩
  have hsq : q ^ 2 = 2 := by rw [← hq]; grind
  -- Compare numerators and denominators: `num(q²) · den(2) = num(2) · den(q²)`.
  have hcross := Rat.eq_iff_mul_eq_mul.mp hsq
  rw [Rat.num_pow, Rat.den_pow] at hcross
  have hint : q.num * q.num = 2 * ((q.den : Int) * (q.den : Int)) := by
    have h2n : (2 : Rat).num = 2 := rfl
    have h2d : (2 : Rat).den = 1 := rfl
    rw [h2n, h2d] at hcross
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.natCast_pow] at hcross
    grind
  have hnat : q.num.natAbs * q.num.natAbs = 2 * (q.den * q.den) := by
    have := congrArg Int.natAbs hint
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul] at this
    simpa using this
  exact q.den_nz (sq_two_descent _ _ hnat)
-- @endregion

end Lumenary.RationalNumbers
