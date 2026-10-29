/-
The Lumenary — formal mathematics
Addition, subtraction and place value to 100 ("for grown-ups" companion to the K–2 lesson).

In core Lean the natural numbers are built from `0` by repeatedly taking "the next number", and
addition is defined by counting on: `a + (b + 1) = (a + b) + 1`. From that one rule we prove,
by induction, the laws children use every day — adding zero, the turn-around rule
`a + b = b + a`, regrouping `(a + b) + c = a + (b + c)` (which is what "making ten" uses), and
that taking away `b` undoes adding `b`. We also show why `3 − 5` has no answer among the
counting numbers, and formalise place value: every number is `10 × tens + ones`, and comparing
tens first, then ones, compares the numbers.

Core Lean 4 only. Library versions: `Nat.add_comm`, `Nat.add_assoc`, `Nat.add_sub_cancel`,
`Nat.div_add_mod`; Mathlib states the same laws for every commutative monoid (`add_comm`, …).
-/

namespace Lumenary.AdditionSubtraction

/-! ### The equals sign means "has the same value as" -/

-- @region addition_subtraction.seven_eq_three_add_four
-- @provenance independent
/-- `7 = 3 + 4` is a true statement: the two sides have the same value. The answer does not
have to come after the equals sign. -/
theorem seven_eq_three_add_four : 7 = 3 + 4 := rfl
-- @endregion

-- @region addition_subtraction.three_add_four_eq_four_add_three
-- @provenance independent
/-- `3 + 4 = 4 + 3` is also true, although neither side is "the answer": both sides are 7. -/
theorem three_add_four_eq_four_add_three : 3 + 4 = 4 + 3 := rfl
-- @endregion

/-! ### Laws of addition, proved from counting on -/

-- @region addition_subtraction.count_on
-- @provenance independent
/-- Counting on one more: adding `b + 1` is adding `b` and then one more. In Lean this is how
addition is *defined*, so `rfl` proves it. Everything below is built on this rule. -/
theorem count_on (a b : Nat) : a + (b + 1) = (a + b) + 1 := rfl
-- @endregion

-- @region addition_subtraction.add_zero_eq
-- @provenance independent
/-- Adding zero changes nothing: `a + 0 = a` (also true by definition). -/
theorem add_zero_eq (a : Nat) : a + 0 = a := rfl
-- @endregion

-- @region addition_subtraction.zero_add_eq
-- @provenance independent
/-- Zero added to a number also changes nothing: `0 + a = a`. This is *not* true by
definition, so we prove it by induction on `a`, counting on one step at a time. -/
theorem zero_add_eq (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ k ih =>
    calc 0 + (k + 1) = (0 + k) + 1 := count_on 0 k
      _ = k + 1 := by rw [ih]
-- @endregion

-- @region addition_subtraction.succ_add_eq
-- @provenance independent
/-- One more, then add `b`, is the same as add `b`, then one more: `(a + 1) + b = (a + b) + 1`.
A helper for the turn-around rule, proved by induction on `b`. -/
theorem succ_add_eq (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ k ih =>
    calc (a + 1) + (k + 1) = ((a + 1) + k) + 1 := count_on (a + 1) k
      _ = ((a + k) + 1) + 1 := by rw [ih]
      _ = (a + (k + 1)) + 1 := rfl
-- @endregion

-- @region addition_subtraction.add_comm_from_counting
-- @provenance independent
/-- **The turn-around rule** `a + b = b + a`, proved by induction on `b` from counting on.
Compare `add_comm_library`, which applies the theorem already in core Lean. -/
theorem add_comm_from_counting (a b : Nat) : a + b = b + a := by
  induction b with
  | zero => exact (zero_add_eq a).symm
  | succ k ih =>
    calc a + (k + 1) = (a + k) + 1 := count_on a k
      _ = (k + a) + 1 := by rw [ih]
      _ = (k + 1) + a := (succ_add_eq k a).symm
-- @endregion

-- @region addition_subtraction.add_comm_library
-- @provenance library
/-- The turn-around rule again, this time by applying core Lean's `Nat.add_comm`. -/
theorem add_comm_library (a b : Nat) : a + b = b + a := Nat.add_comm a b
-- @endregion

-- @region addition_subtraction.add_assoc_from_counting
-- @provenance independent
/-- **Regrouping** `(a + b) + c = a + (b + c)`: when adding three numbers, it does not matter
which two we add first. Proved by induction on `c` (core Lean: `Nat.add_assoc`). -/
theorem add_assoc_from_counting (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ k ih =>
    calc (a + b) + (k + 1) = ((a + b) + k) + 1 := count_on (a + b) k
      _ = (a + (b + k)) + 1 := by rw [ih]
      _ = a + (b + (k + 1)) := rfl
-- @endregion

-- @region addition_subtraction.make_ten
-- @provenance independent
/-- **Making ten**: `8 + 5 = 10 + 3`. Split 5 into 2 and 3, give the 2 to the 8 to make ten,
and 3 is left. The middle step is regrouping (`add_assoc_from_counting`). -/
theorem make_ten : 8 + 5 = 10 + 3 :=
  calc 8 + 5 = 8 + (2 + 3) := rfl
    _ = (8 + 2) + 3 := (add_assoc_from_counting 8 2 3).symm
    _ = 10 + 3 := rfl
-- @endregion

/-! ### Subtraction -/

-- @region addition_subtraction.sub_undoes_add
-- @provenance independent
/-- **Taking away undoes adding**: `(a + b) − b = a`. Proved by induction on `b`: taking away
one more from one more leaves the same as before (core Lean's `Nat.add_sub_add_right`). -/
theorem sub_undoes_add (a b : Nat) : (a + b) - b = a := by
  induction b with
  | zero => rfl
  | succ k ih =>
    calc (a + (k + 1)) - (k + 1) = ((a + k) + 1) - (k + 1) := rfl
      _ = (a + k) - k := Nat.add_sub_add_right (a + k) 1 k
      _ = a := ih
-- @endregion

-- @region addition_subtraction.sub_undoes_add_library
-- @provenance library
/-- Taking away undoes adding, by applying core Lean's `Nat.add_sub_cancel`. -/
theorem sub_undoes_add_library (a b : Nat) : (a + b) - b = a := Nat.add_sub_cancel a b
-- @endregion

-- @region addition_subtraction.fact_family
-- @provenance independent
/-- A fact family: the numbers 3, 4 and 7 give two addition facts and two subtraction facts.
`decide` asks Lean to check all four. -/
theorem fact_family : 3 + 4 = 7 ∧ 4 + 3 = 7 ∧ 7 - 4 = 3 ∧ 7 - 3 = 4 := by decide
-- @endregion

-- @region addition_subtraction.cannot_take_five_from_three
-- @provenance independent
/-- We cannot take 5 away from 3 and land on a counting number: no `n` satisfies `n + 5 = 3`.
So `5 − 3 = 2`, but `3 − 5` has no answer among the counting numbers — subtraction does not
turn around. (Lean's built-in `3 - 5` returns `0` by convention, "take away as many as you
can"; that is why we state the fact this way.) -/
theorem cannot_take_five_from_three : ¬ ∃ n : Nat, n + 5 = 3 := by
  intro ⟨n, h⟩
  -- `n + 5 = 3` would need `n + 5` to be at most 3, but it is at least 5.
  omega
-- @endregion

/-! ### Place value: tens and ones -/

-- @region addition_subtraction.tens
-- @provenance definition
/-- The number of whole tens in `n` (the left digit of a two-digit number). -/
def tens (n : Nat) : Nat := n / 10
-- @endregion

-- @region addition_subtraction.ones
-- @provenance definition
/-- The ones left over after taking out the tens (the right digit). -/
def ones (n : Nat) : Nat := n % 10
-- @endregion

-- @region addition_subtraction.fifty_two
-- @provenance independent
/-- 52 is five tens and two ones — not "five and two". -/
theorem fifty_two : tens 52 = 5 ∧ ones 52 = 2 := ⟨rfl, rfl⟩
-- @endregion

-- @region addition_subtraction.tens_and_ones
-- @provenance library
/-- Every number is made of its tens and ones: `10 × tens + ones = n`.
This applies core Lean's `Nat.div_add_mod`. -/
theorem tens_and_ones (n : Nat) : 10 * tens n + ones n = n := Nat.div_add_mod n 10
-- @endregion

-- @region addition_subtraction.tens_ones_unique
-- @provenance independent
/-- There is only one way to write a number as tens and ones with fewer than ten ones:
`10 × t + o` (with `o < 10`) has exactly `t` tens and `o` ones. The `omega` tactic decides
facts like this about whole numbers, including division and remainder by a fixed number. -/
theorem tens_ones_unique (t o : Nat) (ho : o < 10) :
    tens (10 * t + o) = t ∧ ones (10 * t + o) = o := by
  unfold tens ones
  omega
-- @endregion

-- @region addition_subtraction.more_tens_bigger
-- @provenance independent
/-- **More tens means bigger**, whatever the ones are: if `a` has fewer tens than `b`, then
`a < b`. Even with 9 ones, `a` stays below the next ten, and that ten is at most `b`
(e.g. `47 < 50 ≤ 52`). -/
theorem more_tens_bigger (a b : Nat) (h : tens a < tens b) : a < b :=
  calc a = 10 * tens a + ones a := (tens_and_ones a).symm
    _ < 10 * tens a + 10 := Nat.add_lt_add_left (Nat.mod_lt a (by decide)) _
    _ = 10 * (tens a + 1) := (Nat.mul_succ 10 (tens a)).symm
    _ ≤ 10 * tens b := Nat.mul_le_mul_left 10 h
    _ ≤ 10 * tens b + ones b := Nat.le_add_right _ _
    _ = b := tens_and_ones b
-- @endregion

-- @region addition_subtraction.same_tens_more_ones
-- @provenance independent
/-- **Same tens, then compare the ones**: if `a` and `b` have the same tens and `a` has fewer
ones, then `a < b` (e.g. `63 < 68`). -/
theorem same_tens_more_ones (a b : Nat) (ht : tens a = tens b) (ho : ones a < ones b) :
    a < b :=
  calc a = 10 * tens a + ones a := (tens_and_ones a).symm
    _ = 10 * tens b + ones a := by rw [ht]
    _ < 10 * tens b + ones b := Nat.add_lt_add_left ho _
    _ = b := tens_and_ones b
-- @endregion

-- @region addition_subtraction.compare_47_52
-- @provenance independent
/-- 47 is less than 52, because 4 tens are fewer than 5 tens. -/
theorem compare_47_52 : 47 < 52 := more_tens_bigger 47 52 (by decide)
-- @endregion

end Lumenary.AdditionSubtraction
