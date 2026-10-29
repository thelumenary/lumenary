/-
The Lumenary — formal mathematics
Secret codes ("for grown-ups" companion to the Grades 3–5 lesson).

Number the letters A = 0, B = 1, …, Z = 25. A Caesar shift by `k` sends letter number `n` to
`(n + k) % 26`: the remainder on division by 26 is what makes Z wrap round to A. We prove that a
shift stays inside the alphabet, that shifting by `26 − k` undoes shifting by `k`, that two
shifts make one shift, that a shift never sends two letters to the same letter, and that there
are exactly 26 different shifts (so only 25 that change anything). Then we shift real
characters (computers store `A` as 65, …, `Z` as 90), check the lesson's messages, and prove
that decoding undoes encoding for **every** message. Finally we count the keys of a
substitution cipher: 26! of them.

Core Lean 4 only. Mathlib analogue: Caesar shifts are addition in `ZMod 26`, and substitution
keys are elements of `Equiv.Perm (Fin 26)`, of which there are `Nat.factorial 26`.
-/

namespace Lumenary.SecretCodes

/-! ### Shifting letter numbers round the alphabet wheel -/

-- @region secret_codes.shift
-- @provenance definition
/-- A Caesar shift by `k` on letter numbers (A = 0, …, Z = 25): move `k` places on, wrapping
round from 25 back to 0. -/
def shift (k n : Nat) : Nat := (n + k) % 26
-- @endregion

-- @region secret_codes.wrap_around
-- @provenance independent
/-- Shifting by 3 wraps round the end of the alphabet: X (23) → A (0), Y (24) → B (1),
Z (25) → C (2). And M (12) → P (15) needs no wrapping. -/
theorem wrap_around : shift 3 23 = 0 ∧ shift 3 24 = 1 ∧ shift 3 25 = 2 ∧ shift 3 12 = 15 := by
  decide
-- @endregion

-- @region secret_codes.shift_lt
-- @provenance library
/-- A shift always lands on one of the 26 letters: a remainder on division by 26 is less
than 26. This applies core Lean's `Nat.mod_lt`. -/
theorem shift_lt (k n : Nat) : shift k n < 26 :=
  Nat.mod_lt _ (by decide)
-- @endregion

-- @region secret_codes.shift_undo
-- @provenance independent
/-- **A shift forward by `k` is undone by a shift forward by `26 − k`**: together they move
26 places, once round the whole wheel. -/
theorem shift_undo (k n : Nat) (hk : k ≤ 26) (hn : n < 26) : shift (26 - k) (shift k n) = n := by
  unfold shift
  omega
-- @endregion

-- @region secret_codes.shift_shift
-- @provenance independent
/-- Two shifts, one after the other, are one shift: by `a`, then by `b`, is the same as by
`a + b`. (So the order of two shifts does not matter.) -/
theorem shift_shift (a b n : Nat) : shift b (shift a n) = shift (a + b) n := by
  unfold shift
  omega
-- @endregion

-- @region secret_codes.shift_twenty_six
-- @provenance independent
/-- Shifting by 26 changes nothing: it goes once round the wheel. -/
theorem shift_twenty_six (n : Nat) (hn : n < 26) : shift 26 n = n := by
  unfold shift
  omega
-- @endregion

-- @region secret_codes.shift_add_twenty_six
-- @provenance independent
/-- Shifting by `k + 26` is the same as shifting by `k`. So every shift is one of the shifts
0, 1, …, 25: there are **at most** 26 different shifts. -/
theorem shift_add_twenty_six (k n : Nat) : shift (k + 26) n = shift k n := by
  unfold shift
  omega
-- @endregion

-- @region secret_codes.shifts_differ
-- @provenance independent
/-- The shifts 0, 1, …, 25 are all different: shift `k` sends A (0) to letter number `k`. So
there are **exactly** 26 shifts — and only 25 that change the message. -/
theorem shifts_differ (k : Nat) (hk : k < 26) : shift k 0 = k := by
  unfold shift
  omega
-- @endregion

-- @region secret_codes.shift_injective
-- @provenance independent
/-- A shift never sends two different letters to the same letter. That is why a coded message
can always be decoded. -/
theorem shift_injective (k n m : Nat) (hn : n < 26) (hm : m < 26)
    (h : shift k n = shift k m) : n = m := by
  unfold shift at h
  omega
-- @endregion

/-! ### Shifting real messages -/

-- @region secret_codes.shift_char
-- @provenance definition
/-- Shift one character. Computers store `A` as the number 65, …, `Z` as 90. A capital letter
is turned into its letter number (subtract 65), shifted, and turned back (add 65); spaces and
other characters are left as they are. -/
def shiftChar (k : Nat) (c : Char) : Char :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then Char.ofNat ((c.toNat - 65 + k) % 26 + 65) else c
-- @endregion

-- @region secret_codes.caesar
-- @provenance definition
/-- The Caesar cipher with key `k`: shift every letter of the message by `k`. -/
def caesar (k : Nat) (message : String) : String :=
  String.ofList (message.toList.map (shiftChar k))
-- @endregion

-- @region secret_codes.meet_at_noon
-- @provenance independent
/-- Julius Caesar's shift of 3: MEET AT NOON becomes PHHW DW QRRQ. -/
theorem meet_at_noon : caesar 3 "MEET AT NOON" = "PHHW DW QRRQ" := by
  decide
-- @endregion

-- @region secret_codes.zebra
-- @provenance independent
/-- Wrapping round: with a shift of 3, ZEBRA becomes CHEUD (Z → C). -/
theorem zebra : caesar 3 "ZEBRA" = "CHEUD" := by
  decide
-- @endregion

-- @region secret_codes.decode_by_23
-- @provenance independent
/-- To decode a shift of 3, shift forward by 26 − 3 = 23. -/
theorem decode_by_23 : caesar 23 "PHHW DW QRRQ" = "MEET AT NOON" := by
  decide
-- @endregion

-- @region secret_codes.try_every_shift
-- @provenance independent
/-- Breaking a Caesar cipher by trying every key: among the 26 shifts of WKLV LV IXQ, one
reads THIS IS FUN. -/
theorem try_every_shift : "THIS IS FUN" ∈ (List.range 26).map (fun k => caesar k "WKLV LV IXQ") := by
  decide
-- @endregion

-- @region secret_codes.to_nat_of_nat
-- @provenance independent
/-- Turning a small number into a character and back gives the same number. -/
theorem toNat_ofNat_small (m : Nat) (h : m < 55296) : (Char.ofNat m).toNat = m := by
  have hv : m.isValidChar := Or.inl h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
-- @endregion

-- @region secret_codes.shift_char_undo
-- @provenance independent
/-- Shifting a character by `k` and then by `26 − k` gives it back: for a capital letter by
`shift_undo`, and any other character was never changed. -/
theorem shiftChar_undo (k : Nat) (hk : k ≤ 26) (c : Char) :
    shiftChar (26 - k) (shiftChar k c) = c := by
  unfold shiftChar
  by_cases h : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · have e := toNat_ofNat_small ((c.toNat - 65 + k) % 26 + 65) (by omega)
    rw [ite_eq_left h, ite_eq_left (by rw [e]; omega)]
    apply Char.toNat_inj.mp
    rw [toNat_ofNat_small _ (by omega), e]
    omega
  · rw [ite_eq_right h, ite_eq_right h]
-- @endregion

-- @region secret_codes.caesar_undo
-- @provenance independent
/-- **Decoding undoes encoding, for every message and every key**: the Caesar cipher with key
`26 − k` decodes the Caesar cipher with key `k`. -/
theorem caesar_undo (k : Nat) (hk : k ≤ 26) (message : String) :
    caesar (26 - k) (caesar k message) = message := by
  unfold caesar
  rw [String.toList_ofList, List.map_map]
  have : (shiftChar (26 - k) ∘ shiftChar k) = id := funext (shiftChar_undo k hk)
  rw [this, List.map_id, String.ofList_toList]
-- @endregion

/-! ### Substitution ciphers have far too many keys to try -/

-- @region secret_codes.factorial
-- @provenance definition
/-- `factorial n = 1 × 2 × ⋯ × n`. (Mathlib calls it `Nat.factorial`.) -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
-- @endregion

-- @region secret_codes.substitution_keys
-- @provenance independent
/-- A substitution key chooses a code letter for A (26 choices), then for B (25 left), and so
on: 26 × 25 × ⋯ × 1 keys — more than 400 million million million million. -/
theorem substitution_keys : factorial 26 = 403291461126605635584000000 := by
  decide
-- @endregion

end Lumenary.SecretCodes
