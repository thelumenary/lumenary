/-
The Lumenary — formal mathematics
Whole-number arithmetic: the laws of multiplication, why the written methods work, and
division with remainder.

Core Lean 4 only (no Mathlib), so the file can be pasted into the web editor. Lean's natural
numbers `Nat` come with multiplication defined as repeated addition: `a * (b + 1) = a * b + a`,
so `a * b` is `b` copies of `a`. From that definition alone we prove that the order of the
factors does not matter (`mul_comm_from_definition`). Other results re-derive a familiar fact
the way a learner would (`@provenance independent`) or simply apply a theorem from Lean's
library (`@provenance library`). Mathlib analogue: the same laws hold in every commutative
semiring (`mul_comm`, `mul_assoc`, `mul_add`), and `Nat.div_add_mod`, `Nat.mod_lt` and
`Nat.div_mod_unique` describe division with remainder.
-/

namespace Lumenary.WholeNumberArithmetic

/-! ### Calculating flexibly with the laws -/

-- @region whole_number_arithmetic.times_ninety_eight
-- @provenance independent
/-- `a × 98 = a × 100 − a × 2` for every whole number `a`: since `100 = 98 + 2`, the
distributive law gives `a × 100 = a × 98 + a × 2`, and taking away `a × 2` leaves `a × 98`.
So `7 × 98 = 700 − 14 = 686`. -/
theorem times_ninety_eight (a : Nat) : a * 98 = a * 100 - a * 2 := by
  have h : a * 100 = a * 98 + a * 2 :=
    calc a * 100 = a * (98 + 2) := rfl
      _ = a * 98 + a * 2 := Nat.mul_add a 98 2
  rw [h, Nat.add_sub_cancel]
-- @endregion

-- @region whole_number_arithmetic.seven_times_ninety_eight
-- @provenance independent
/-- The worked example: `7 × 98 = 7 × 100 − 7 × 2 = 686`. Lean evaluates both sides. -/
theorem seven_times_ninety_eight : 7 * 98 = 7 * 100 - 7 * 2 ∧ 7 * 98 = 686 := by decide
-- @endregion

-- @region whole_number_arithmetic.twenty_five_times_thirty_six
-- @provenance independent
/-- `25 × 36 = 900`, by regrouping: `36 = 4 × 9`, and the associative law lets us multiply
`25 × 4 = 100` first. Each line of the `calc` block is one step of the mental calculation. -/
theorem twenty_five_times_thirty_six : 25 * 36 = 900 :=
  calc 25 * 36 = 25 * (4 * 9) := rfl
    _ = (25 * 4) * 9 := (Nat.mul_assoc 25 4 9).symm
    _ = 100 * 9 := rfl
    _ = 900 := rfl
-- @endregion

-- @region whole_number_arithmetic.distrib_library
-- @provenance library
/-- The distributive law `a × (b + c) = a × b + a × c`. This applies core Lean's
theorem `Nat.mul_add`. -/
theorem distrib_library (a b c : Nat) : a * (b + c) = a * b + a * c := Nat.mul_add a b c
-- @endregion

/-! ### Why the order of the factors does not matter -/

-- @region whole_number_arithmetic.zero_mul_from_definition
-- @provenance independent
/-- `0 × a = 0`: any number of copies of `0` add up to `0`. Proved by induction on `a`, using
only Lean's definition `n * (m + 1) = n * m + n`. -/
theorem zero_mul_from_definition (a : Nat) : 0 * a = 0 := by
  induction a with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, ih]
-- @endregion

-- @region whole_number_arithmetic.succ_mul_from_definition
-- @provenance independent
/-- `(a + 1) × b = a × b + b`: making every one of the `b` copies one bigger adds `b` in all.
Proved by induction on `b` from the definition of multiplication. -/
theorem succ_mul_from_definition (a b : Nat) : (a + 1) * b = a * b + b := by
  induction b with
  | zero => rfl
  | succ n ih =>
    calc (a + 1) * (n + 1) = (a + 1) * n + (a + 1) := Nat.mul_succ (a + 1) n
      _ = a * n + n + (a + 1) := by rw [ih]
      _ = (a * n + a) + (n + 1) := by omega
      _ = a * (n + 1) + (n + 1) := by rw [Nat.mul_succ]
-- @endregion

-- @region whole_number_arithmetic.mul_comm_from_definition
-- @provenance independent
/-- The commutative law `a × b = b × a`, proved from the definition of multiplication as
repeated addition (by induction on `b`, with the two lemmas above). Lean's `a * b` means
"`b` copies of `a`", the opposite reading from "`a` groups of `b`"; this theorem is exactly why
the choice does not matter. -/
theorem mul_comm_from_definition (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => rw [Nat.mul_zero, zero_mul_from_definition]
  | succ n ih => rw [Nat.mul_succ, ih, succ_mul_from_definition]
-- @endregion

-- @region whole_number_arithmetic.mul_comm_library
-- @provenance library
/-- The commutative law again, this time by applying core Lean's theorem `Nat.mul_comm`. -/
theorem mul_comm_library (a b : Nat) : a * b = b * a := Nat.mul_comm a b
-- @endregion

/-! ### Why the written multiplication method works -/

-- @region whole_number_arithmetic.area_model
-- @provenance independent
/-- The area model: `(a + b) × (c + d)` is the sum of the four partial products. Split the
first factor (distributive law on the right), then split each part again (on the left). -/
theorem area_model (a b c d : Nat) :
    (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc (a + b) * (c + d) = a * (c + d) + b * (c + d) := Nat.add_mul a b (c + d)
    _ = (a * c + a * d) + (b * c + b * d) := by rw [Nat.mul_add a c d, Nat.mul_add b c d]
    _ = a * c + a * d + b * c + b * d := (Nat.add_assoc (a * c + a * d) (b * c) (b * d)).symm
-- @endregion

-- @region whole_number_arithmetic.twenty_three_times_forty_seven
-- @provenance independent
/-- `23 × 47 = 1081`, as four partial products: `20 × 40 + 20 × 7 + 3 × 40 + 3 × 7`
`= 800 + 140 + 120 + 21`. The first step is `area_model` with `23 = 20 + 3` and `47 = 40 + 7`. -/
theorem twenty_three_times_forty_seven :
    23 * 47 = 20 * 40 + 20 * 7 + 3 * 40 + 3 * 7 ∧ 23 * 47 = 1081 :=
  ⟨area_model 20 3 40 7, rfl⟩
-- @endregion

/-! ### Division with remainder -/

-- @region whole_number_arithmetic.eggs_in_trays
-- @provenance independent
/-- 347 eggs fill 11 trays of 30, with 17 eggs left over: `347 = 11 × 30 + 17` and `17 < 30`.
Lean's `/` and `%` compute the same quotient and remainder. -/
theorem eggs_in_trays : 347 = 11 * 30 + 17 ∧ 17 < 30 ∧ 347 / 30 = 11 ∧ 347 % 30 = 17 := by
  decide
-- @endregion

-- @region whole_number_arithmetic.div_mod_exists
-- @provenance independent
/-- Division with remainder always works: for `b > 0`, every `a` can be written as
`a = q × b + r` with `r < b`. The proof adds eggs one at a time (induction on `a`). Each new
egg either goes into the unfinished tray, or it completes that tray and the leftover pile
starts again at `0`. -/
theorem div_mod_exists (a b : Nat) (hb : 0 < b) : ∃ q r, a = q * b + r ∧ r < b := by
  induction a with
  | zero => exact ⟨0, 0, by rw [Nat.zero_mul], hb⟩
  | succ n ih =>
    obtain ⟨q, r, h, _hr⟩ := ih
    by_cases hfit : r + 1 < b
    · -- The new egg fits in the unfinished tray: the remainder grows by one.
      exact ⟨q, r + 1, by omega, hfit⟩
    · -- The new egg completes the tray (`r + 1 = b`): one more full tray, nothing left over.
      have hrb : r + 1 = b := by omega
      refine ⟨q + 1, 0, ?_, hb⟩
      calc n + 1 = q * b + (r + 1) := by omega
        _ = q * b + b := by rw [hrb]
        _ = (q + 1) * b + 0 := by rw [Nat.succ_mul, Nat.add_zero]
-- @endregion

-- @region whole_number_arithmetic.div_mod_unique
-- @provenance independent
/-- The quotient and remainder are unique. If `q × b + r = q' × b + r'` with both remainders
less than `b`, then `q = q'` and `r = r'`. If `q` were smaller than `q'`, the right side
would be at least `(q + 1) × b = q × b + b`, which is more than `q × b + r`. -/
theorem div_mod_unique {b q r q' r' : Nat} (h : q * b + r = q' * b + r')
    (hr : r < b) (hr' : r' < b) : q = q' ∧ r = r' := by
  have hq : q = q' := by
    rcases Nat.lt_trichotomy q q' with hlt | heq | hgt
    · have hle : (q + 1) * b ≤ q' * b := Nat.mul_le_mul_right b hlt
      rw [Nat.succ_mul] at hle
      omega
    · exact heq
    · have hle : (q' + 1) * b ≤ q * b := Nat.mul_le_mul_right b hgt
      rw [Nat.succ_mul] at hle
      omega
  subst hq
  exact ⟨rfl, by omega⟩
-- @endregion

-- @region whole_number_arithmetic.div_mod_library
-- @provenance library
/-- Lean's own quotient `a / b` and remainder `a % b` satisfy `a = (a / b) × b + a % b` with
`a % b < b`. This applies the core theorems `Nat.div_add_mod'` and `Nat.mod_lt`. -/
theorem div_mod_library (a b : Nat) (hb : 0 < b) : a = a / b * b + a % b ∧ a % b < b :=
  ⟨(Nat.div_add_mod' a b).symm, Nat.mod_lt a hb⟩
-- @endregion

-- @region whole_number_arithmetic.long_division_953
-- @provenance independent
/-- The long division in the lesson: `953 ÷ 4` is `238` remainder `1`. -/
theorem long_division_953 : 953 = 238 * 4 + 1 ∧ 1 < 4 := by decide
-- @endregion

/-! ### Dividing by zero, and multiplication that does not make bigger -/

-- @region whole_number_arithmetic.no_division_by_zero
-- @provenance independent
/-- There is no answer to `5 ÷ 0`: no number `q` has `q × 0 = 5`, because `q × 0 = 0`. -/
theorem no_division_by_zero : ¬ ∃ q : Nat, q * 0 = 5 := by
  intro ⟨q, hq⟩
  rw [Nat.mul_zero] at hq
  -- `hq : 0 = 5`, which is false.
  exact absurd hq (by decide)
-- @endregion

-- @region whole_number_arithmetic.zero_div_zero_every
-- @provenance library
/-- And `0 ÷ 0` has no single answer: *every* `q` satisfies `q × 0 = 0`.
This applies core Lean's `Nat.mul_zero`. -/
theorem zero_div_zero_every (q : Nat) : q * 0 = 0 := Nat.mul_zero q
-- @endregion

-- @region whole_number_arithmetic.multiplying_need_not_enlarge
-- @provenance independent
/-- "Multiplying always makes a number bigger" is false. One counterexample is enough:
`9 × 1 = 9` is not bigger than `9`. -/
theorem multiplying_need_not_enlarge : ¬ ∀ a b : Nat, a < a * b := by
  intro h
  have h91 : 9 < 9 * 1 := h 9 1
  exact absurd h91 (by decide)
-- @endregion

end Lumenary.WholeNumberArithmetic
