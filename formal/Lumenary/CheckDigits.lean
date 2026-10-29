/-
The Lumenary — formal mathematics
Check digits and error detection: ISBN-10, ISBN-13, the Luhn scheme and parity bits.

A code number is a list of digits. A *weighted check sum* multiplies the digit in position `k`
by a weight `w k` and adds up. We prove one general lemma about such sums (what happens when
one digit in the middle changes), and from it, for **every** ISBN-10, that a single wrong digit
or a swap of two neighbouring digits is always detected, and for every ISBN-13 that a single
wrong digit is detected. Facts about all pairs of digits (which swaps ISBN-13 and Luhn miss)
are checked by `decide`, which tries all 100 pairs. Parity bits are proved by induction on the
list of bits. Core Lean only, no Mathlib. Mathlib analogue: these are *linear codes*; Mathlib
has `ZMod 11` (a field, because 11 is prime) and Hamming distance (`hammingDist`).
-/

namespace Lumenary.CheckDigits

/-! ### Weighted check sums -/

-- @region check_digits.wsum
-- @provenance definition
/-- The weighted sum of a list of digits: the digit in position `k` is multiplied by `w k`.
`wsum w k ds` starts counting positions at `k`. -/
def wsum (w : Nat → Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | k, d :: ds => w k * d + wsum w (k + 1) ds
-- @endregion

-- @region check_digits.wsum_append_cons
-- @provenance independent
/-- **Splitting a check sum at one digit.** If a code is `pre ++ x :: post` (some digits, then
the digit `x`, then more digits), its weighted sum is the sum over `pre`, plus `x` times its
weight, plus the sum over `post`. So when only `x` changes, only the middle term changes.
Proof by induction on the digits before `x`. -/
theorem wsum_append_cons (w : Nat → Nat) (pre post : List Nat) (x k : Nat) :
    wsum w k (pre ++ x :: post) =
      wsum w k pre + w (k + pre.length) * x + wsum w (k + pre.length + 1) post := by
  induction pre generalizing k with
  | nil => simp [wsum]
  | cons d ds ih =>
    simp only [List.cons_append, wsum, ih, List.length_cons]
    have h1 : k + 1 + ds.length = k + (ds.length + 1) := by omega
    rw [h1]
    omega
-- @endregion

/-! ### ISBN-10 -/

-- @region check_digits.isbn10_sum
-- @provenance definition
/-- The ISBN-10 check sum `1·d₁ + 2·d₂ + ⋯ + 10·d₁₀` (the weight of position `k` is `k`). -/
def isbn10Sum (ds : List Nat) : Nat := wsum (fun k => k) 1 ds
-- @endregion

-- @region check_digits.valid_isbn10
-- @provenance definition
/-- A valid ISBN-10: ten digits (the last may be `10`, printed `X`) whose check sum is a
multiple of `11`. -/
abbrev ValidISBN10 (ds : List Nat) : Prop := ds.length = 10 ∧ isbn10Sum ds % 11 = 0
-- @endregion

-- @region check_digits.example_isbn10
-- @provenance independent
/-- The sample number `3-16-148410-X` is a valid ISBN-10 (`X` stands for `10`):
`1·3 + 2·1 + 3·6 + 4·1 + 5·4 + 6·8 + 7·4 + 8·1 + 9·0 + 10·10 = 231 = 21 · 11`. -/
theorem example_isbn10 : ValidISBN10 [3, 1, 6, 1, 4, 8, 4, 1, 0, 10] := by decide
-- @endregion

-- @region check_digits.isbn10_check_digit
-- @provenance independent
/-- **How to compute the check digit.** For any nine digits, appending
`(1·d₁ + ⋯ + 9·d₉) mod 11` gives a valid ISBN-10.
Proof: if the first nine digits have sum `S`, the full sum is `S + 10 · (S mod 11)`. Writing
`S = 11q + r`, this is `11q + 11r`, a multiple of 11. (Because `10 ≡ -1 (mod 11)`.) -/
theorem isbn10_check_digit (ds : List Nat) (h : ds.length = 9) :
    ValidISBN10 (ds ++ [isbn10Sum ds % 11]) := by
  refine ⟨by simp [h], ?_⟩
  have hsplit := wsum_append_cons (fun k => k) ds [] (isbn10Sum ds % 11) 1
  simp only [wsum, Nat.add_zero, h] at hsplit
  show wsum (fun k => k) 1 (ds ++ [isbn10Sum ds % 11]) % 11 = 0
  rw [hsplit]
  -- `S + 10 · (S mod 11)` is a multiple of 11.
  show (isbn10Sum ds + (1 + 9) * (isbn10Sum ds % 11)) % 11 = 0
  omega
-- @endregion

-- @region check_digits.cancel_mod_eleven
-- @provenance independent
/-- Modulo the prime `11`, a non-zero weight can be cancelled: if `w ≠ 0` and
`w · x ≡ w · y (mod 11)` for remainders `x, y`, then `x = y`. In words, each non-zero row of
the multiplication table modulo 11 is a shuffle. `decide` checks all `11³` cases. -/
theorem cancel_mod_eleven : ∀ w, w < 11 → ∀ x, x < 11 → ∀ y, y < 11 → w ≠ 0 →
    (w * x) % 11 = (w * y) % 11 → x = y := by decide
-- @endregion

-- @region check_digits.isbn10_single_error
-- @provenance independent
/-- **ISBN-10 detects every single-digit error.** If two ISBN-10s are identical except for
one digit (`x` in one, `y` in the other) and both are valid, then `x = y`.
Proof: by `wsum_append_cons` the two sums differ only in the term `w · x` versus `w · y`, where
the weight `w` is the position, between 1 and 10. Both sums are multiples of 11, so
`w · x ≡ w · y (mod 11)`, and `cancel_mod_eleven` gives `x = y`. -/
theorem isbn10_single_error (pre post : List Nat) (x y : Nat) (hx : x ≤ 10) (hy : y ≤ 10)
    (h₁ : ValidISBN10 (pre ++ x :: post)) (h₂ : ValidISBN10 (pre ++ y :: post)) : x = y := by
  obtain ⟨hlen, hs₁⟩ := h₁
  obtain ⟨_, hs₂⟩ := h₂
  simp only [List.length_append, List.length_cons] at hlen
  unfold isbn10Sum at hs₁ hs₂
  rw [wsum_append_cons] at hs₁ hs₂
  -- Name the weight and the two middle terms, so that only linear arithmetic remains.
  generalize hu : (1 + pre.length) * x = u at hs₁
  generalize hv : (1 + pre.length) * y = v at hs₂
  have huv : u % 11 = v % 11 := by omega
  rw [← hu, ← hv] at huv
  exact cancel_mod_eleven (1 + pre.length) (by omega) x (by omega) y (by omega) (by omega) huv
-- @endregion

-- @region check_digits.isbn10_adjacent_swap
-- @provenance independent
/-- **ISBN-10 detects every swap of two neighbouring digits.** If `… x y …` and `… y x …` are
both valid ISBN-10s, then `x = y` (so nothing was really swapped).
Proof: neighbouring positions have weights `w` and `w + 1`, so the two sums are
`… + w·x + (w+1)·y + …` and `… + w·y + (w+1)·x + …`. Their difference is `y - x`, which lies
strictly between `-11` and `11`; it is a multiple of 11 only when `x = y`. -/
theorem isbn10_adjacent_swap (pre post : List Nat) (x y : Nat) (hx : x ≤ 10) (hy : y ≤ 10)
    (h₁ : ValidISBN10 (pre ++ x :: y :: post)) (h₂ : ValidISBN10 (pre ++ y :: x :: post)) :
    x = y := by
  obtain ⟨_, hs₁⟩ := h₁
  obtain ⟨_, hs₂⟩ := h₂
  unfold isbn10Sum at hs₁ hs₂
  simp only [wsum_append_cons, wsum] at hs₁ hs₂
  -- The two middle terms: `w·x + (w+1)·y` and `w·y + (w+1)·x`, with `w = 1 + pre.length`.
  rw [Nat.add_mul (1 + pre.length) 1 y] at hs₁
  rw [Nat.add_mul (1 + pre.length) 1 x] at hs₂
  generalize (1 + pre.length) * x = u at hs₁ hs₂
  generalize (1 + pre.length) * y = v at hs₁ hs₂
  omega
-- @endregion

-- @region check_digits.swap_caught_by_isbn10
-- @provenance independent
/-- Swapping the neighbouring digits `1` and `6` in `3-16-148410-X` gives `3-61-148410-X`,
which is **not** a valid ISBN-10: the error is caught. -/
theorem swap_caught_by_isbn10 : ¬ ValidISBN10 [3, 6, 1, 1, 4, 8, 4, 1, 0, 10] := by decide
-- @endregion

/-! ### ISBN-13 -/

-- @region check_digits.isbn13_weight
-- @provenance definition
/-- ISBN-13 weights: positions `1, 3, 5, …` have weight `1`, positions `2, 4, 6, …` weight `3`. -/
def isbn13Weight (k : Nat) : Nat := if k % 2 = 1 then 1 else 3
-- @endregion

-- @region check_digits.valid_isbn13
-- @provenance definition
/-- A valid ISBN-13: thirteen digits whose weighted sum `d₁ + 3d₂ + d₃ + 3d₄ + ⋯ + d₁₃` is a
multiple of `10`. -/
abbrev ValidISBN13 (ds : List Nat) : Prop :=
  ds.length = 13 ∧ wsum isbn13Weight 1 ds % 10 = 0
-- @endregion

-- @region check_digits.example_isbn13
-- @provenance independent
/-- `978-3-16-148410-0` is a valid ISBN-13: its weighted sum is `100`. -/
theorem example_isbn13 : ValidISBN13 [9, 7, 8, 3, 1, 6, 1, 4, 8, 4, 1, 0, 0] := by decide
-- @endregion

-- @region check_digits.cancel_three_mod_ten
-- @provenance independent
/-- The weight `3` can be cancelled modulo 10: `3 · x ≡ 3 · y (mod 10)` forces `x = y` for
digits `x, y`. (The row of `3` in the multiplication table modulo 10 is a shuffle, because
`3` has the partner `7`.) `decide` checks all 100 pairs. -/
theorem cancel_three_mod_ten : ∀ x, x < 10 → ∀ y, y < 10 →
    (3 * x) % 10 = (3 * y) % 10 → x = y := by decide
-- @endregion

-- @region check_digits.isbn13_single_error
-- @provenance independent
/-- **ISBN-13 detects every single-digit error.** Same structure as for ISBN-10: the two sums
differ only in `w · x` versus `w · y`, the weight `w` is `1` or `3`, and both can be cancelled
modulo 10 (`cancel_three_mod_ten`). -/
theorem isbn13_single_error (pre post : List Nat) (x y : Nat) (hx : x ≤ 9) (hy : y ≤ 9)
    (h₁ : ValidISBN13 (pre ++ x :: post)) (h₂ : ValidISBN13 (pre ++ y :: post)) : x = y := by
  obtain ⟨_, hs₁⟩ := h₁
  obtain ⟨_, hs₂⟩ := h₂
  rw [wsum_append_cons] at hs₁ hs₂
  unfold isbn13Weight at hs₁ hs₂
  -- The weight of the changed position is `1` or `3` (the same in both codes).
  split at hs₁ <;> split at hs₂
  · -- weight 1: the sums differ by `y - x` itself.
    omega
  · omega
  · omega
  · -- weight 3: cancel the 3.
    generalize hu : 3 * x = u at hs₁
    generalize hv : 3 * y = v at hs₂
    have huv : u % 10 = v % 10 := by omega
    rw [← hu, ← hv] at huv
    exact cancel_three_mod_ten x (by omega) y (by omega) huv
-- @endregion

-- @region check_digits.isbn13_swap_rule
-- @provenance independent
/-- **Which neighbouring swaps does ISBN-13 miss?** Swapping neighbours `a, b` (weights `1` and
`3`) leaves the check sum unchanged modulo 10 exactly when `a = b` or the digits differ by 5.
`decide` checks all 100 pairs of digits. -/
theorem isbn13_swap_rule : ∀ a, a < 10 → ∀ b, b < 10 →
    ((a + 3 * b) % 10 = (b + 3 * a) % 10 ↔ (a = b ∨ a + 5 = b ∨ b + 5 = a)) := by
  decide
-- @endregion

-- @region check_digits.isbn13_missed_swap
-- @provenance independent
/-- A swap ISBN-13 cannot see: `978-3-16-148410-0` and the same digits with the neighbours `1`
and `6` swapped are **both** valid, because `6 - 1 = 5`. -/
theorem isbn13_missed_swap :
    ValidISBN13 [9, 7, 8, 3, 1, 6, 1, 4, 8, 4, 1, 0, 0] ∧
      ValidISBN13 [9, 7, 8, 3, 6, 1, 1, 4, 8, 4, 1, 0, 0] := by decide
-- @endregion

/-! ### The Luhn scheme (bank cards, phone IMEI numbers) -/

-- @region check_digits.luhn_double
-- @provenance definition
/-- Luhn's doubling: double the digit, and if the result has two digits, add them
(`2·7 = 14 → 1 + 4 = 5`). For a digit `d` this is `2d` if `d < 5` and `2d - 9` otherwise. -/
def luhnDouble (d : Nat) : Nat := if d < 5 then 2 * d else 2 * d - 9
-- @endregion

-- @region check_digits.luhn_sum
-- @provenance definition
/-- The Luhn sum, reading the digits **from the right**: the last digit is added as it is, the
next one doubled with `luhnDouble`, the next added as it is, and so on. A number passes the
Luhn test when this sum is a multiple of 10. (`luhnSumRev` takes the digits right to left.) -/
def luhnSumRev : Bool → List Nat → Nat
  | _, [] => 0
  | dbl, d :: ds => (if dbl then luhnDouble d else d) + luhnSumRev (!dbl) ds
-- @endregion

-- @region check_digits.example_luhn
-- @provenance independent
/-- The number `7992 7398 713` passes the Luhn test: its Luhn sum is `70`. -/
theorem example_luhn : luhnSumRev false [7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3].reverse % 10 = 0 := by
  decide
-- @endregion

-- @region check_digits.luhn_double_shuffle
-- @provenance independent
/-- Luhn's doubling sends different digits to different digits (`0,1,…,9 ↦ 0,2,4,6,8,1,3,5,7,9`),
so a single wrong digit always changes the Luhn sum by something that is not a multiple of 10.
`decide` checks all pairs. -/
theorem luhn_double_shuffle : ∀ a, a < 10 → ∀ b, b < 10 →
    luhnDouble a = luhnDouble b → a = b := by decide
-- @endregion

-- @region check_digits.luhn_swap_rule
-- @provenance independent
/-- **The one swap Luhn misses.** Swapping neighbours `a, b` (one of them doubled) leaves the Luhn
sum unchanged modulo 10 exactly when `a = b` or the pair is `0, 9` or `9, 0`. -/
theorem luhn_swap_rule : ∀ a, a < 10 → ∀ b, b < 10 →
    ((a + luhnDouble b) % 10 = (b + luhnDouble a) % 10 ↔
      (a = b ∨ (a = 0 ∧ b = 9) ∨ (a = 9 ∧ b = 0))) := by
  decide
-- @endregion

/-! ### Parity bits -/

-- @region check_digits.parity
-- @provenance definition
/-- The parity of a list of bits: `true` if it contains an odd number of `1`s (`true`s),
`false` if an even number. (`xor` is "exactly one of the two".) -/
def parity : List Bool → Bool
  | [] => false
  | b :: bs => xor b (parity bs)
-- @endregion

-- @region check_digits.parity_append
-- @provenance independent
/-- The parity of two blocks of bits put together is the `xor` of their parities.
Proof by induction on the first block. -/
theorem parity_append (l₁ l₂ : List Bool) : parity (l₁ ++ l₂) = xor (parity l₁) (parity l₂) := by
  induction l₁ with
  | nil => simp [parity]
  | cons a as ih => simp [parity, ih]
-- @endregion

-- @region check_digits.add_parity_bit
-- @provenance independent
/-- **Adding a parity bit.** Appending the parity of a message to the message always gives an
even number of `1`s in total: `parity (bs ++ [parity bs]) = false`. -/
theorem add_parity_bit (bs : List Bool) : parity (bs ++ [parity bs]) = false := by
  rw [parity_append]
  simp [parity]
-- @endregion

-- @region check_digits.parity_flip
-- @provenance independent
/-- Flipping any one bit flips the parity. Proof by induction on the bits before it. -/
theorem parity_flip (pre post : List Bool) (b : Bool) :
    parity (pre ++ (!b) :: post) = !parity (pre ++ b :: post) := by
  induction pre with
  | nil => simp [parity]
  | cons a as ih => simp [parity, ih]
-- @endregion

-- @region check_digits.single_flip_detected
-- @provenance independent
/-- **A parity bit detects any single flipped bit**: if the sent word had even parity, the
received word with one bit flipped has odd parity, so the receiver knows something went wrong. -/
theorem single_flip_detected (pre post : List Bool) (b : Bool)
    (h : parity (pre ++ b :: post) = false) : parity (pre ++ (!b) :: post) = true := by
  rw [parity_flip, h]
  rfl
-- @endregion

-- @region check_digits.double_flip_undetected
-- @provenance independent
/-- **… but never two.** Flipping two bits (`a` and, further on, `b`) leaves the parity exactly
as it was, so the error passes unnoticed. Two uses of `parity_flip`. -/
theorem double_flip_undetected (pre mid post : List Bool) (a b : Bool) :
    parity (pre ++ (!a) :: (mid ++ (!b) :: post)) = parity (pre ++ a :: (mid ++ b :: post)) := by
  rw [parity_flip]
  have h : pre ++ a :: (mid ++ (!b) :: post) = (pre ++ a :: mid) ++ (!b) :: post := by simp
  have h' : pre ++ a :: (mid ++ b :: post) = (pre ++ a :: mid) ++ b :: post := by simp
  rw [h, h', parity_flip]
  simp
-- @endregion

/-! ### Detecting is not correcting -/

-- @region check_digits.one_digit_apart
-- @provenance definition
/-- Two codes are *one digit apart* if they agree everywhere except in one position. -/
def OneDigitApart (c₁ c₂ : List Nat) : Prop :=
  ∃ pre post : List Nat, ∃ x y : Nat, x ≠ y ∧ c₁ = pre ++ x :: post ∧ c₂ = pre ++ y :: post
-- @endregion

-- @region check_digits.cannot_correct
-- @provenance independent
/-- **A check digit cannot tell you which digit is wrong.** The received number `3-26-148410-X`
is invalid, and it is one digit away from **two different** valid ISBN-10s, `3-16-148410-X`
and `1-26-148410-X`. So the scheme detects the error but cannot correct it. -/
theorem cannot_correct :
    ¬ ValidISBN10 [3, 2, 6, 1, 4, 8, 4, 1, 0, 10] ∧
      ValidISBN10 [3, 1, 6, 1, 4, 8, 4, 1, 0, 10] ∧
      ValidISBN10 [1, 2, 6, 1, 4, 8, 4, 1, 0, 10] ∧
      OneDigitApart [3, 2, 6, 1, 4, 8, 4, 1, 0, 10] [3, 1, 6, 1, 4, 8, 4, 1, 0, 10] ∧
      OneDigitApart [3, 2, 6, 1, 4, 8, 4, 1, 0, 10] [1, 2, 6, 1, 4, 8, 4, 1, 0, 10] := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact ⟨[3], [6, 1, 4, 8, 4, 1, 0, 10], 2, 1, by decide, rfl, rfl⟩
  · exact ⟨[], [2, 6, 1, 4, 8, 4, 1, 0, 10], 3, 1, by decide, rfl, rfl⟩
-- @endregion

end Lumenary.CheckDigits
