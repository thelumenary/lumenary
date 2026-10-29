/-
The Lumenary — formal mathematics
Clock arithmetic: remainders and modular arithmetic.

`a % n` is Lean's name for "the remainder of `a` on division by `n`". We prove, mirroring the
lesson, that the remainder of a sum or a product depends only on the remainders of its parts
(from division with remainder, not by quoting the library), that a number sharing a factor with
`n` can never have a multiplicative partner modulo `n`, and that powers repeat in cycles.
Statements about one particular clock (`Fin 12`, `Fin 7`, …) are checked by `decide`, which
makes Lean try every case. Core Lean only, no Mathlib. Mathlib analogue: `ZMod n` is the ring
of remainders modulo `n`, `Nat.ModEq` is congruence, and `ZMod.unitOfCoprime` gives the partner
of a number coprime to `n` (the converse direction, proved later with Euclid's algorithm).
-/

namespace Lumenary.ModularArithmetic

/-! ### Remainders -/

-- @region modular_arithmetic.div_add_mod
-- @provenance library
/-- **Division with remainder.** Every `a` is `n` times its quotient plus its remainder:
`n · (a / n) + a % n = a`. This applies core Lean's `Nat.div_add_mod`. -/
theorem div_add_mod (a n : Nat) : n * (a / n) + a % n = a := Nat.div_add_mod a n
-- @endregion

-- @region modular_arithmetic.mod_lt
-- @provenance library
/-- A remainder on division by `n > 0` is always one of `0, 1, …, n - 1`: `a % n < n`.
This applies core Lean's `Nat.mod_lt`. -/
theorem mod_lt (a : Nat) {n : Nat} (hn : 0 < n) : a % n < n := Nat.mod_lt a hn
-- @endregion

-- @region modular_arithmetic.clock_example
-- @provenance independent
/-- On a 12-hour clock, 29 hours after 9 o'clock it is 2 o'clock: `(9 + 29) mod 12 = 2`. -/
theorem clock_example : (9 + 29) % 12 = 2 := by decide
-- @endregion

-- @region modular_arithmetic.week_example
-- @provenance independent
/-- Number the days Monday = 0, Tuesday = 1, …, Sunday = 6. Then 100 days after a Monday is
day `100 mod 7 = 2`, a Wednesday. -/
theorem week_example : (0 + 100) % 7 = 2 := by decide
-- @endregion

/-! ### Reduce first, then calculate -/

-- @region modular_arithmetic.add_mod_of_division
-- @provenance independent
/-- **The remainder of a sum depends only on the remainders.**
`(a + b) mod n = ((a mod n) + (b mod n)) mod n`.
The lesson's proof: write `a = n·q₁ + r₁` and `b = n·q₂ + r₂`. Then
`a + b = n·(q₁ + q₂) + (r₁ + r₂)`, and adding a multiple of `n` never changes a remainder
(`Nat.mul_add_mod`). -/
theorem add_mod_of_division (a b n : Nat) : (a + b) % n = (a % n + b % n) % n := by
  -- The two divisions with remainder.
  have ha := Nat.div_add_mod a n
  have hb := Nat.div_add_mod b n
  -- Regroup: `a + b` is a multiple of `n` plus `r₁ + r₂`.
  have hsum : a + b = n * (a / n + b / n) + (a % n + b % n) := by
    calc a + b = (n * (a / n) + a % n) + (n * (b / n) + b % n) := by rw [ha, hb]
      _ = n * (a / n + b / n) + (a % n + b % n) := by rw [Nat.mul_add]; omega
  rw [hsum, Nat.mul_add_mod]
-- @endregion

-- @region modular_arithmetic.mul_mod_of_division
-- @provenance independent
/-- **The remainder of a product depends only on the remainders.**
`(a · b) mod n = ((a mod n) · (b mod n)) mod n`.
Proof: with `a = n·q₁ + r₁` and `b = n·q₂ + r₂`, expanding gives
`a · b = n·(q₁·b + r₁·q₂) + r₁·r₂`, a multiple of `n` plus `r₁ · r₂`. -/
theorem mul_mod_of_division (a b n : Nat) : (a * b) % n = (a % n * (b % n)) % n := by
  have ha := Nat.div_add_mod a n
  have hb := Nat.div_add_mod b n
  have hprod : a * b = n * (a / n * b + a % n * (b / n)) + a % n * (b % n) := by
    calc a * b = (n * (a / n) + a % n) * b := by rw [ha]
      _ = n * (a / n) * b + a % n * b := Nat.add_mul _ _ _
      _ = n * (a / n) * b + a % n * (n * (b / n) + b % n) := by rw [hb]
      _ = n * (a / n * b + a % n * (b / n)) + a % n * (b % n) := by
        rw [Nat.mul_add (a % n), Nat.mul_add n, Nat.mul_assoc, ← Nat.add_assoc,
          Nat.mul_left_comm (a % n) n]
  rw [hprod, Nat.mul_add_mod]
-- @endregion

-- @region modular_arithmetic.add_mod_library
-- @provenance library
/-- The same fact for sums, quoted from core Lean's library (`Nat.add_mod`). Compare
`add_mod_of_division`, which proves it here from division with remainder. -/
theorem add_mod_library (a b n : Nat) : (a + b) % n = (a % n + b % n) % n := Nat.add_mod a b n
-- @endregion

/-! ### Zero products and partners -/

-- @region modular_arithmetic.zero_product_mod_twelve
-- @provenance independent
/-- On a 12-hour clock a product can be `0` although neither factor is:
`3 · 4 = 12 ≡ 0 (mod 12)` while `3 mod 12 = 3` and `4 mod 12 = 4`. -/
theorem zero_product_mod_twelve : (3 * 4) % 12 = 0 ∧ 3 % 12 ≠ 0 ∧ 4 % 12 ≠ 0 := by decide
-- @endregion

-- @region modular_arithmetic.no_partner_of_common_factor
-- @provenance independent
/-- **A common factor blocks a partner.** If some `d > 1` divides both `a` and `n`, then no `b`
has `a · b mod n = 1`.
Proof: `d` divides `a · b`, and `d` divides `n`, so `d` divides the remainder `a · b mod n`
(the remainder is `a · b` minus a multiple of `n`). If that remainder were `1`, then `d` would
divide `1`, so `d = 1`, contradicting `d > 1`. -/
theorem no_partner_of_common_factor {a n d : Nat} (hd : 1 < d) (hda : d ∣ a) (hdn : d ∣ n)
    (b : Nat) : (a * b) % n ≠ 1 := by
  intro h
  -- `d` divides `a · b` …
  have hab : d ∣ a * b := Nat.dvd_mul_right_of_dvd hda b
  -- … so it divides the remainder of `a · b` on division by `n`, which is `1`.
  have h1 : d ∣ (a * b) % n := (Nat.dvd_mod_iff hdn).mpr hab
  rw [h] at h1
  have : d = 1 := Nat.eq_one_of_dvd_one h1
  omega
-- @endregion

-- @region modular_arithmetic.four_no_partner_mod_ten
-- @provenance independent
/-- `4` has no partner modulo `10`: `4` and `10` share the factor `2`. This is
`no_partner_of_common_factor` with `d = 2`. -/
theorem four_no_partner_mod_ten (b : Nat) : (4 * b) % 10 ≠ 1 :=
  no_partner_of_common_factor (d := 2) (by decide) (by decide) (by decide) b
-- @endregion

-- @region modular_arithmetic.partners_mod_twelve
-- @provenance independent
/-- On a 12-hour clock exactly `1, 5, 7, 11` have a multiplicative partner. Lean's `Fin 12`
is clock arithmetic: its numbers are `0, …, 11` and `*` multiplies and takes the remainder.
`decide` checks all 144 products. -/
theorem partners_mod_twelve :
    ∀ a : Fin 12, (∃ b : Fin 12, a * b = 1) ↔ (a = 1 ∨ a = 5 ∨ a = 7 ∨ a = 11) := by
  decide
-- @endregion

-- @region modular_arithmetic.partners_mod_seven
-- @provenance independent
/-- Modulo the prime `7`, every non-zero remainder has a partner
(`1·1`, `2·4`, `3·5`, `6·6` all leave remainder `1`). `decide` checks every case. -/
theorem partners_mod_seven : ∀ a : Fin 7, a ≠ 0 → ∃ b : Fin 7, a * b = 1 := by decide
-- @endregion

-- @region modular_arithmetic.row_is_shuffle_mod_seven
-- @provenance independent
/-- Modulo `7`, multiplying by a non-zero `a` never sends two different remainders to the
same place: each row of the multiplication table is a shuffle of `0, …, 6`. (This is the
property check digits rely on.) -/
theorem row_is_shuffle_mod_seven :
    ∀ a x y : Fin 7, a ≠ 0 → a * x = a * y → x = y := by decide
-- @endregion

/-! ### Repeating patterns -/

-- @region modular_arithmetic.pow_three_mod_seven
-- @provenance independent
/-- The powers of `2` modulo `7` repeat `1, 2, 4, 1, 2, 4, …`. In particular
`2^(3k) mod 7 = 1` for every `k`.
Proof by induction: `2^(3(k+1)) = 2^(3k) · 8`, and `8 mod 7 = 1`, so by
`mul_mod_of_division` the remainder is `1 · 1 = 1`. -/
theorem pow_three_mod_seven (k : Nat) : 2 ^ (3 * k) % 7 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc 2 ^ (3 * (k + 1)) % 7 = (2 ^ (3 * k) * 8) % 7 := by
          rw [Nat.mul_succ, Nat.pow_add]
      _ = (2 ^ (3 * k) % 7 * (8 % 7)) % 7 := mul_mod_of_division _ _ _
      _ = 1 := by rw [ih]
-- @endregion

-- @region modular_arithmetic.last_digit_seven_pow
-- @provenance independent
/-- The last digit of `7^(4k + 2)` is always `9`: the last digits of `7, 49, 343, 2401, …`
repeat `7, 9, 3, 1`. Proof: `7^4 = 2401` leaves remainder `1` on division by `10`, so
`7^(4k) mod 10 = 1` by induction, and `7^2 = 49`. For example, `7^2026` ends in `9`. -/
theorem last_digit_seven_pow (k : Nat) : 7 ^ (4 * k + 2) % 10 = 9 := by
  have h4 : ∀ j : Nat, 7 ^ (4 * j) % 10 = 1 := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      calc 7 ^ (4 * (j + 1)) % 10 = (7 ^ (4 * j) * 2401) % 10 := by
            rw [Nat.mul_succ, Nat.pow_add]
        _ = (7 ^ (4 * j) % 10 * (2401 % 10)) % 10 := mul_mod_of_division _ _ _
        _ = 1 := by rw [ih]
  calc 7 ^ (4 * k + 2) % 10 = (7 ^ (4 * k) * 49) % 10 := by rw [Nat.pow_add]
    _ = (7 ^ (4 * k) % 10 * (49 % 10)) % 10 := mul_mod_of_division _ _ _
    _ = 9 := by rw [h4 k]
-- @endregion

-- @region modular_arithmetic.ten_pow_mod_nine
-- @provenance independent
/-- `10^k mod 9 = 1` for every `k`, because `10 = 9 + 1` leaves remainder `1`. This is why a
number and the sum of its digits leave the same remainder on division by `9`
("casting out nines"). -/
theorem ten_pow_mod_nine (k : Nat) : 10 ^ k % 9 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc 10 ^ (k + 1) % 9 = (10 ^ k * 10) % 9 := by rw [Nat.pow_succ]
      _ = (10 ^ k % 9 * (10 % 9)) % 9 := mul_mod_of_division _ _ _
      _ = 1 := by rw [ih]
-- @endregion

end Lumenary.ModularArithmetic
