/-
The Lumenary — formal mathematics
Integers: additive inverses, why "negative times negative is positive", and which integers
have multiplicative inverses.

Core Lean 4's `Int` comes with the ring laws already proved (`Int.mul_add`, `Int.add_assoc`,
…). Some results below simply *apply* such a library theorem (`@provenance library`); others
re-derive a familiar rule from the ring axioms, mirroring the proof a student would write
(`@provenance independent`). Mathlib analogue: the same facts hold in every ring
(`add_neg_cancel`, `mul_zero`, `neg_mul`, `neg_mul_neg`), and `Int.isUnit_iff` for units.
-/

namespace Lumenary.Integers

/-! ### Additive inverses -/

-- @region integers.add_neg_cancel
-- @provenance library
/-- Every integer cancels with its negative: `a + (-a) = 0`.
This applies core Lean's `Int.add_right_neg`. -/
theorem add_neg_cancel (a : Int) : a + -a = 0 := Int.add_right_neg a
-- @endregion

-- @region integers.add_inverse_exists
-- @provenance independent
/-- In the integers, every number has an additive inverse: some `b` with `a + b = 0`.
The witness is `-a`. -/
theorem add_inverse_exists : ∀ a : Int, ∃ b, a + b = 0 := by
  intro a
  exact ⟨-a, add_neg_cancel a⟩
-- @endregion

-- @region integers.nat_no_additive_inverse
-- @provenance independent
/-- In the natural numbers there is no additive inverse of `1`: no `n` with `1 + n = 0`.
This is why we extend the natural numbers to the integers. -/
theorem nat_no_additive_inverse : ¬ ∃ n : Nat, 1 + n = 0 := by
  intro ⟨n, h⟩
  -- `1 + n` is the successor `n + 1`, and a successor is never `0`.
  rw [Nat.add_comm] at h
  exact Nat.succ_ne_zero n h
-- @endregion

/-! ### Rules of signs, derived from the ring axioms -/

-- @region integers.eq_neg_of_add_eq_zero
-- @provenance independent
/-- If `x + y = 0` then `x = -y`: an additive inverse is unique. Uses only `add_zero`,
associativity, `y + (-y) = 0` and `zero_add`. -/
theorem eq_neg_of_add_eq_zero {x y : Int} (h : x + y = 0) : x = -y :=
  calc x = x + 0 := (Int.add_zero x).symm
    _ = x + (y + -y) := by rw [Int.add_right_neg]
    _ = (x + y) + -y := (Int.add_assoc x y (-y)).symm
    _ = 0 + -y := by rw [h]
    _ = -y := Int.zero_add (-y)
-- @endregion

-- @region integers.eq_of_add_neg_eq_zero
-- @provenance independent
/-- If `x + (-y) = 0` then `x = y`. Same idea as `eq_neg_of_add_eq_zero`, using `-y + y = 0`. -/
theorem eq_of_add_neg_eq_zero {x y : Int} (h : x + -y = 0) : x = y :=
  calc x = x + 0 := (Int.add_zero x).symm
    _ = x + (-y + y) := by rw [Int.add_left_neg]
    _ = (x + -y) + y := (Int.add_assoc x (-y) y).symm
    _ = 0 + y := by rw [h]
    _ = y := Int.zero_add y
-- @endregion

-- @region integers.mul_zero_from_distrib
-- @provenance independent
/-- `a · 0 = 0`, derived from distributivity and cancellation:
`a·0 + a·0 = a·(0 + 0) = a·0 = a·0 + 0`, and cancelling `a·0` leaves `a·0 = 0`. -/
theorem mul_zero_from_distrib (a : Int) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 :=
    calc a * 0 + a * 0 = a * (0 + 0) := (Int.mul_add a 0 0).symm
      _ = a * 0 := by rw [Int.add_zero]
      _ = a * 0 + 0 := (Int.add_zero (a * 0)).symm
  exact Int.add_left_cancel h
-- @endregion

-- @region integers.neg_mul_from_distrib
-- @provenance independent
/-- `(-a) · b = -(a · b)`, from distributivity:
`(-a)·b + a·b = (-a + a)·b = 0·b = 0`, so `(-a)·b` is the additive inverse of `a·b`. -/
theorem neg_mul_from_distrib (a b : Int) : -a * b = -(a * b) := by
  have h : -a * b + a * b = 0 :=
    calc -a * b + a * b = (-a + a) * b := (Int.add_mul (-a) a b).symm
      _ = 0 * b := by rw [Int.add_left_neg]
      _ = b * 0 := Int.mul_comm 0 b
      _ = 0 := mul_zero_from_distrib b
  exact eq_neg_of_add_eq_zero h
-- @endregion

-- @region integers.neg_mul_neg_library
-- @provenance library
/-- "Negative times negative is positive": `(-a) · (-b) = a · b`.
This version just applies core Lean's theorem `Int.neg_mul_neg`. Compare
`neg_mul_neg_from_axioms`, which proves the same statement from the ring axioms. -/
theorem neg_mul_neg_library (a b : Int) : -a * -b = a * b := Int.neg_mul_neg a b
-- @endregion

-- @region integers.neg_mul_neg_from_axioms
-- @provenance independent
/-- "Negative times negative is positive", proved the way a student would:
1. `(-a)(-b) + (-a)b = (-a)(-b + b) = (-a)·0 = 0`  (distributivity, then `-b + b = 0`);
2. `(-a)b = -(ab)`  (`neg_mul_from_distrib`);
3. so `(-a)(-b) + -(ab) = 0`, which forces `(-a)(-b) = ab`. -/
theorem neg_mul_neg_from_axioms (a b : Int) : -a * -b = a * b := by
  -- Step 1.
  have step1 : -a * -b + -a * b = 0 :=
    calc -a * -b + -a * b = -a * (-b + b) := (Int.mul_add (-a) (-b) b).symm
      _ = -a * 0 := by rw [Int.add_left_neg]
      _ = 0 := mul_zero_from_distrib (-a)
  -- Step 2.
  have step2 : -a * b = -(a * b) := neg_mul_from_distrib a b
  -- Step 3: substitute step 2 into step 1, then cancel.
  rw [step2] at step1
  exact eq_of_add_neg_eq_zero step1
-- @endregion

/-! ### Multiplicative inverses (mostly missing) -/

-- @region integers.no_int_half
-- @provenance independent
/-- There is no integer `x` with `2 · x = 1`, so `2` has no multiplicative inverse in `Int`.
Reason: `2 · x` always leaves remainder `0` when divided by `2`, but `1` leaves remainder `1`. -/
theorem no_int_half : ¬ ∃ x : Int, 2 * x = 1 := by
  intro ⟨x, h⟩
  have hrem : (2 * x) % 2 = 1 % 2 := by rw [h]
  rw [Int.mul_emod_right] at hrem
  -- `hrem : 0 = 1 % 2`, i.e. `0 = 1`, which is false.
  exact absurd hrem (by decide)
-- @endregion

-- @region integers.no_int_third
-- @provenance independent
/-- There is no integer `x` with `3 · x = 1`. Same argument as `no_int_half`, using
remainders on division by `3`. -/
theorem no_int_third : ¬ ∃ x : Int, 3 * x = 1 := by
  intro ⟨x, h⟩
  have hrem : (3 * x) % 3 = 1 % 3 := by rw [h]
  rw [Int.mul_emod_right] at hrem
  exact absurd hrem (by decide)
-- @endregion

-- @region integers.int_units
-- @provenance independent
/-- The only integers with a multiplicative inverse are `1` and `-1`:
if `a · b = 1` then `a = 1` or `a = -1`.
Proof: take absolute values. `|a| · |b| = |a · b| = 1` in the natural numbers, which forces
`|a| = 1`; an integer with absolute value `1` is `1` or `-1`. -/
theorem int_units (a b : Int) (h : a * b = 1) : a = 1 ∨ a = -1 := by
  have habs : a.natAbs * b.natAbs = 1 := by
    rw [← Int.natAbs_mul, h]
    rfl
  have ha : a.natAbs = 1 := Nat.eq_one_of_mul_eq_one_right habs
  -- Every integer is `+|a|` or `-|a|`.
  cases Int.natAbs_eq a with
  | inl hpos => left; rw [hpos, ha]; rfl
  | inr hneg => right; rw [hneg, ha]; rfl
-- @endregion

end Lumenary.Integers
