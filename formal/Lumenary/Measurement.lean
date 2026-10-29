/-
The Lumenary — formal mathematics
Measurement: comparing lengths, units, rulers, bent strings and clocks ("for grown-ups"
companion to the K–2 lesson on measuring length and time).

Lengths here are whole numbers of some unit (say centimetres), so they are natural numbers,
and "A is longer than B" is `b < a`. Times on a 12-hour clock face are counted in minutes
after 12 o'clock, and the clock wraps around every 720 minutes.

What is proved: "longer than" is transitive (library and by comparison with a string);
measuring with a smaller unit gives a bigger number; reading the end of a ruler gives the
length exactly when the object starts at 0; a ruler has one more mark than spaces; bending a
string never changes its length although its ends may move closer together; and two half
hours make an hour on the clock face. Core Lean 4 only. Mathlib analogue: lengths and
measures live in `MeasureTheory`, and physical units are not formalised there at all.
-/

namespace Lumenary.Measurement

/-! ### Comparing lengths -/

-- @region measurement.longer_trans
-- @provenance library
/-- If A is longer than B, and B is longer than C, then A is longer than C.
(Lengths `a, b, c` in whole units; "A is longer than B" is `b < a`.)
This applies core Lean's `Nat.lt_trans`. -/
theorem longer_trans {a b c : Nat} (hab : b < a) (hbc : c < b) : c < a :=
  Nat.lt_trans hbc hab
-- @endregion

-- @region measurement.compare_with_string
-- @provenance independent
/-- Comparing two things that cannot be put side by side, using a string as a go-between.
Cut a string exactly as long as the table (`string = table`). If the door is wider than the
string (`string < door`), the door is wider than the table. -/
theorem compare_with_string {door table string : Nat} (h₁ : string = table)
    (h₂ : string < door) : table < door := by
  rw [← h₁]
  exact h₂
-- @endregion

/-! ### Units -/

-- @region measurement.smaller_unit_bigger_number
-- @provenance independent
/-- Measuring with a smaller unit gives a bigger number. If something is `k` big units long
(`k ≥ 1`) and one big unit is `m` small units (`m ≥ 2`), then it is `k * m` small units
long, and `k < k * m`:
`k = k · 1 < k · m`. -/
theorem smaller_unit_bigger_number (k m : Nat) (hk : 0 < k) (hm : 1 < m) : k < k * m :=
  calc k = k * 1 := (Nat.mul_one k).symm
    _ < k * m := Nat.mul_lt_mul_of_pos_left hm hk
-- @endregion

-- @region measurement.units_end_to_end
-- @provenance definition
/-- Lay copies of one unit end to end, with a gap after each copy (a gap of `0` means no
gap). Each entry of `gaps` is one copy of the unit followed by its gap; the result is how
far the row of units reaches. -/
def reach (unit : Nat) : List Nat → Nat
  | [] => 0
  | gap :: gaps => unit + gap + reach unit gaps
-- @endregion

-- @region measurement.reach_no_gaps
-- @provenance independent
/-- With no gaps, `n` copies of a unit reach exactly `n` units: measuring is counting units
laid end to end. Proof by induction on the number of copies. -/
theorem reach_no_gaps (unit n : Nat) : reach unit (List.replicate n 0) = n * unit := by
  induction n with
  | zero => simp [reach]
  | succ n ih => simp only [List.replicate, reach, ih, Nat.add_zero, Nat.succ_mul, Nat.add_comm]
-- @endregion

-- @region measurement.gaps_reach_further
-- @provenance independent
/-- Gaps make a row of units reach further than the number of units says: `n` copies with
gaps reach at least `n` units. So if the row ends exactly at the end of an object, counting
the copies gives a number that is too small (or exactly right, if there were no gaps). -/
theorem gaps_reach_further (unit : Nat) (gaps : List Nat) : gaps.length * unit ≤ reach unit gaps := by
  induction gaps with
  | nil => simp [reach]
  | cons g gs ih =>
    simp only [List.length_cons, Nat.succ_mul, reach]
    omega
-- @endregion

/-! ### Rulers -/

-- @region measurement.ruler_length
-- @provenance definition
/-- An object lying along a ruler from the mark `start` to the mark `finish` is
`finish - start` units long. -/
def rulerLength (start finish : Nat) : Nat := finish - start
-- @endregion

-- @region measurement.pencil_from_three
-- @provenance independent
/-- A pencil from the 3 mark to the 18 mark is 15 units long, not 18. -/
theorem pencil_from_three : rulerLength 3 18 = 15 := rfl
-- @endregion

-- @region measurement.read_end_iff_start_zero
-- @provenance independent
/-- Reading the number at the end of the object gives its length **exactly when** the object
starts at 0 (for an object of positive length). This is why we line things up with 0. -/
theorem read_end_iff_start_zero (start finish : Nat) (h : start < finish) :
    rulerLength start finish = finish ↔ start = 0 := by
  unfold rulerLength
  omega
-- @endregion

-- @region measurement.marks
-- @provenance definition
/-- The marks on a ruler from `start` to `finish`, including both ends. -/
def marks (start finish : Nat) : List Nat := List.range' start (finish - start + 1)
-- @endregion

-- @region measurement.marks_length
-- @provenance library
/-- There is always one more mark than spaces: from `start` to `finish` there are
`(finish - start) + 1` marks but only `finish - start` units. Counting marks instead of the
spaces between them gives an answer one too big. This applies core Lean's
`List.length_range'`. -/
theorem marks_length (start finish : Nat) :
    (marks start finish).length = rulerLength start finish + 1 :=
  List.length_range'
-- @endregion

/-! ### Bent strings -/

-- @region measurement.dir
-- @provenance definition
/-- The four directions a piece of string can point on squared paper. -/
inductive Dir where
  | right | up | left | down
  deriving DecidableEq, Repr
-- @endregion

-- @region measurement.piece
-- @provenance definition
/-- A straight piece of a string: which way it points and how long it is. A string is a list
of pieces joined end to end. -/
structure Piece where
  dir : Dir
  len : Nat
  deriving DecidableEq, Repr
-- @endregion

-- @region measurement.string_length
-- @provenance definition
/-- The length of a string: add up the lengths of its pieces. -/
def stringLength : List Piece → Nat
  | [] => 0
  | p :: ps => p.len + stringLength ps
-- @endregion

-- @region measurement.bend
-- @provenance definition
/-- Bend a string: point each piece in a new direction `newDir p`, keeping its length. -/
def bend (newDir : Piece → Dir) (s : List Piece) : List Piece :=
  s.map fun p => ⟨newDir p, p.len⟩
-- @endregion

-- @region measurement.bend_keeps_length
-- @provenance independent
/-- **A bent string is exactly as long as before.** However the pieces are pointed, the
lengths being added up are the same. Proof by induction on the pieces. -/
theorem bend_keeps_length (newDir : Piece → Dir) (s : List Piece) :
    stringLength (bend newDir s) = stringLength s := by
  induction s with
  | nil => rfl
  | cons p ps ih => simp only [bend, List.map, stringLength] at ih ⊢; rw [ih]
-- @endregion

-- @region measurement.end_point
-- @provenance definition
/-- Where the far end of a string lands if its near end is at `(0, 0)` on squared paper. -/
def endPoint : List Piece → Int × Int
  | [] => (0, 0)
  | ⟨d, n⟩ :: ps =>
    let (x, y) := endPoint ps
    match d with
    | .right => (x + n, y)
    | .up => (x, y + n)
    | .left => (x - n, y)
    | .down => (x, y - n)
-- @endregion

-- @region measurement.bent_string_example
-- @provenance independent
/-- A string 6 units long, first straight and then bent into an L: the length is the same,
but the far end lands somewhere else — closer to the start. Bending changes where the ends
are, not how long the string is. -/
theorem bent_string_example :
    stringLength [⟨.right, 6⟩] = stringLength [⟨.right, 3⟩, ⟨.up, 3⟩] ∧
    endPoint [⟨.right, 6⟩] = (6, 0) ∧ endPoint [⟨.right, 3⟩, ⟨.up, 3⟩] = (3, 3) := by
  decide
-- @endregion

/-! ### Clocks -/

-- @region measurement.later
-- @provenance definition
/-- Times on a 12-hour clock face, in minutes after 12 o'clock (`0 ≤ t < 720`).
`later t m` is the time `m` minutes after `t`; the clock wraps round after 720 minutes. -/
def later (t m : Nat) : Nat := (t + m) % 720
-- @endregion

-- @region measurement.hour_shown
-- @provenance definition
/-- The hour the short hand has reached at time `t`, from 1 to 12. -/
def hourShown (t : Nat) : Nat := if (t / 60) % 12 = 0 then 12 else (t / 60) % 12
-- @endregion

-- @region measurement.minute_number
-- @provenance definition
/-- The number on the clock face that the long hand points at, when the minutes are a
multiple of 5: at 30 minutes past the hour it points at 6. -/
def minuteNumber (t : Nat) : Nat := (t % 60) / 5
-- @endregion

-- @region measurement.half_hour_twice
-- @provenance independent
/-- Two half hours make an hour, at every time on the clock face — even across 12 o'clock. -/
theorem half_hour_twice (t : Nat) : later (later t 30) 30 = later t 60 := by
  unfold later
  omega
-- @endregion

-- @region measurement.half_past_seven
-- @provenance independent
/-- At half past seven (450 minutes after 12 o'clock) the short hand has reached 7 (it is
halfway to 8) and the long hand points at 6. Half an hour later it is 8 o'clock. -/
theorem half_past_seven :
    hourShown 450 = 7 ∧ minuteNumber 450 = 6 ∧ later 450 30 = 8 * 60 := by
  decide
-- @endregion

-- @region measurement.half_past_eleven
-- @provenance independent
/-- Half an hour after half past eleven, the clock shows 12 o'clock, not 13 o'clock. -/
theorem half_past_eleven : hourShown (later (11 * 60 + 30) 30) = 12 := by decide
-- @endregion

end Lumenary.Measurement
