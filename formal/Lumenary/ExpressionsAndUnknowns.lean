/-
The Lumenary — formal mathematics
Expressions, unknowns and rules ("for grown-ups" companion to the Grades 3–5 lesson).

Lean reads `2 + 3 * 4` with the same convention as the lesson: brackets first, then
multiplication and division, then addition and subtraction, and operations of the same kind from
left to right. We check the lesson's calculations; prove that subtracting undoes adding and
dividing undoes multiplying by a non-zero number; solve the lesson's equations, proving not only
that the answer works but that it is the *only* answer (with `calc` blocks that follow the
human "undo it" reasoning); show that some equations have no whole-number answer and that
multiplying by 0 cannot be undone; and describe input–output rules as Lean functions.

Core Lean 4 only, with whole numbers (`Nat`). In `Nat`, subtraction stops at 0 and division
rounds down, so `n + b - b = n` and `a * n / a = n` (for `a > 0`) are exactly the facts that
say these operations undo each other.
-/

namespace Lumenary.ExpressionsAndUnknowns

/-! ### The order of operations -/

-- @region expressions_and_unknowns.order_of_operations
-- @provenance independent
/-- Without brackets, multiplication comes before addition: `2 + 3 * 4` is `2 + 12 = 14`.
Brackets change the grouping: `(2 + 3) * 4` is `5 * 4 = 20`. Lean follows the same convention
as the lesson. -/
theorem order_of_operations : 2 + 3 * 4 = 14 ∧ (2 + 3) * 4 = 20 := by
  decide
-- @endregion

-- @region expressions_and_unknowns.left_to_right
-- @provenance independent
/-- Operations of the same kind are done from left to right: `18 / 3 * 2` is `6 * 2 = 12`
(not `18 / 6 = 3`), and `10 - 4 - 3` is `6 - 3 = 3` (not `10 - 1 = 9`). And `20 - 8 / 4` is
`20 - 2 = 18`, because division comes before subtraction. -/
theorem left_to_right : 18 / 3 * 2 = 12 ∧ 10 - 4 - 3 = 3 ∧ 20 - 8 / 4 = 18 := by
  decide
-- @endregion

/-! ### Inverse operations -/

-- @region expressions_and_unknowns.sub_undoes_add
-- @provenance library
/-- Subtracting `b` undoes adding `b`: whatever number `n` you start with, add `b` and then take
`b` away, and you are back at `n`. This is core Lean's `Nat.add_sub_cancel`. -/
theorem sub_undoes_add (n b : Nat) : n + b - b = n :=
  Nat.add_sub_cancel n b
-- @endregion

-- @region expressions_and_unknowns.div_undoes_mul
-- @provenance library
/-- Dividing by `a` undoes multiplying by `a`, as long as `a` is not 0. This is core Lean's
`Nat.mul_div_cancel_left`. -/
theorem div_undoes_mul (n a : Nat) (ha : 0 < a) : a * n / a = n :=
  Nat.mul_div_cancel_left n ha
-- @endregion

-- @region expressions_and_unknowns.zero_cannot_be_undone
-- @provenance independent
/-- Multiplying by 0 **cannot** be undone: it sends 3 and 7 (and every other number) to the same
answer, 0, so nothing can tell us afterwards which number we started with. -/
theorem zero_cannot_be_undone : 0 * 3 = 0 * 7 ∧ 3 ≠ 7 := by
  decide
-- @endregion

/-! ### Finding unknowns -/

-- @region expressions_and_unknowns.add_unknown
-- @provenance independent
/-- **□ + 17 = 40 exactly when □ = 23.** If □ + 17 = 40, then taking 17 away from both sides
gives □ = 40 − 17 = 23 — so 23 is the only possible answer. And 23 really works. -/
theorem add_unknown (x : Nat) : x + 17 = 40 ↔ x = 23 := by
  constructor
  · intro h
    calc x = x + 17 - 17 := (Nat.add_sub_cancel x 17).symm
      _ = 40 - 17 := by rw [h]
      _ = 23 := by decide
  · intro h
    rw [h]
-- @endregion

-- @region expressions_and_unknowns.add_solution
-- @provenance independent
/-- The same reasoning for **any** numbers: when `b ≤ c`, the equation □ + b = c has exactly one
whole-number answer, □ = c − b. -/
theorem add_solution (b c x : Nat) (h : b ≤ c) : x + b = c ↔ x = c - b := by
  omega
-- @endregion

-- @region expressions_and_unknowns.mul_unknown
-- @provenance independent
/-- **3 × □ = 24 exactly when □ = 8.** If 3 × □ = 24, dividing both sides by 3 gives
□ = 24 ÷ 3 = 8. And 8 really works. -/
theorem mul_unknown (x : Nat) : 3 * x = 24 ↔ x = 8 := by
  constructor
  · intro h
    calc x = 3 * x / 3 := (Nat.mul_div_cancel_left x (by decide)).symm
      _ = 24 / 3 := by rw [h]
      _ = 8 := by decide
  · intro h
    rw [h]
-- @endregion

-- @region expressions_and_unknowns.unknown_on_left
-- @provenance independent
/-- The equals sign means "has the same value as", so an equation can be written either way
round: 24 = 3 × □ is the same equation as 3 × □ = 24, with the same answer. -/
theorem unknown_on_left (x : Nat) : 24 = 3 * x ↔ x = 8 := by
  constructor
  · intro h
    exact (mul_unknown x).mp h.symm
  · intro h
    exact ((mul_unknown x).mpr h).symm
-- @endregion

-- @region expressions_and_unknowns.think_of_a_number
-- @provenance independent
/-- **Two steps.** "Multiply by 3, then add 1" gives 22 exactly when the number was 7. To find
it, undo the steps in reverse order: take away 1, then divide by 3. -/
theorem think_of_a_number (x : Nat) : 3 * x + 1 = 22 ↔ x = 7 := by
  constructor
  · intro h
    calc x = (3 * x + 1 - 1) / 3 := by
          rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left x (by decide)]
      _ = (22 - 1) / 3 := by rw [h]
      _ = 7 := by decide
  · intro h
    rw [h]
-- @endregion

-- @region expressions_and_unknowns.no_whole_answer
-- @provenance independent
/-- Some equations have **no** whole-number answer: 3 × □ = 25 has none, because 25 is not a
multiple of 3 (`3 × 8 = 24` is too small and `3 × 9 = 27` too big). The answer is the fraction
25/3, which lives outside the whole numbers. -/
theorem no_whole_answer : ¬ ∃ x : Nat, 3 * x = 25 := by
  omega
-- @endregion

-- @region expressions_and_unknowns.zero_times_unknown
-- @provenance independent
/-- Why "multiplying by a **non-zero** number" matters: 0 × □ = 5 has no answer at all, and
0 × □ = 0 is true for every number, so it does not pin down □. -/
theorem zero_times_unknown : (∀ x : Nat, 0 * x ≠ 5) ∧ (∀ x : Nat, 0 * x = 0) :=
  ⟨fun x => by rw [Nat.zero_mul]; decide, fun x => Nat.zero_mul x⟩
-- @endregion

/-! ### Input–output rules -/

-- @region expressions_and_unknowns.double_add_one
-- @provenance definition
/-- The rule "double, then add 1", written as an expression in `n`: `2 * n + 1`. -/
def doubleAddOne (n : Nat) : Nat := 2 * n + 1
-- @endregion

-- @region expressions_and_unknowns.double_add_one_table
-- @provenance independent
/-- Completing the table for the rule: the inputs 1, 2, 3 and 10 give 3, 5, 7 and 21. -/
theorem doubleAddOne_table : [1, 2, 3, 10].map doubleAddOne = [3, 5, 7, 21] := by
  decide
-- @endregion

-- @region expressions_and_unknowns.double_add_one_backwards
-- @provenance independent
/-- Working backwards: the rule gives 15 only for the input 7 (undo: take away 1, then
halve). -/
theorem doubleAddOne_backwards (n : Nat) : doubleAddOne n = 15 ↔ n = 7 := by
  unfold doubleAddOne
  omega
-- @endregion

-- @region expressions_and_unknowns.three_n_plus_one
-- @provenance definition
/-- The rule found from the table 1 → 4, 2 → 7, 3 → 10, 4 → 13: "multiply by 3, then add 1". -/
def threeNPlusOne (n : Nat) : Nat := 3 * n + 1
-- @endregion

-- @region expressions_and_unknowns.three_n_plus_one_table
-- @provenance independent
/-- The rule fits every row of the table. -/
theorem threeNPlusOne_table : [1, 2, 3, 4].map threeNPlusOne = [4, 7, 10, 13] := by
  decide
-- @endregion

-- @region expressions_and_unknowns.three_n_plus_one_step
-- @provenance independent
/-- Why the multiplier is 3: for **every** input, going up by 1 makes the output go up by 3. -/
theorem threeNPlusOne_step (n : Nat) : threeNPlusOne (n + 1) = threeNPlusOne n + 3 := by
  unfold threeNPlusOne
  omega
-- @endregion

end Lumenary.ExpressionsAndUnknowns
