/-
The Lumenary — formal mathematics
Data, tallies and picture graphs ("for grown-ups" companion to the K–2 lesson).

A class survey — "How did you come to school today?" — is written as a Lean list of answers,
one per child, and the tally for a category is the number of answers in it (`List.count`).
We check the class's tallies and the "which is most" and "how many more" questions by
calculation, and prove the lesson's key fact for *every* possible survey: when each answer goes
into exactly one category, the category totals add up to the number of answers. Tallies grouped
in fives are division with remainder. Finally, a survey in which children may choose several
answers shows why the totals can then add up to more than the number of children.

Core Lean 4 only. Mathlib analogue: `List.count`, `Multiset.count`, and `Finset.card_eq_sum_card_fiberwise`
(the sizes of the parts of a partition add up to the size of the whole).
-/

namespace Lumenary.DataAndTallies

/-! ### One answer per child -/

-- @region data_and_tallies.way
-- @provenance definition
/-- The four categories for the question "How did you come to school today?". Every child's
answer is exactly one of them. -/
inductive Way where
  | walk | bus | bike | car
  deriving DecidableEq, Repr
-- @endregion

-- @region data_and_tallies.answers
-- @provenance definition
/-- The answers of the 24 children in Ms Wanjiru's class, in the order they were asked. -/
def answers : List Way :=
  [.walk, .bus, .walk, .car, .bike, .walk, .bus, .walk, .bike, .bus, .walk, .car,
   .walk, .bus, .bike, .walk, .bus, .walk, .bike, .bus, .car, .walk, .bus, .bike]
-- @endregion

-- @region data_and_tallies.tally
-- @provenance definition
/-- The tally for category `w`: how many answers in the list are `w`. -/
def tally (w : Way) (l : List Way) : Nat := l.count w
-- @endregion

-- @region data_and_tallies.class_tallies
-- @provenance independent
/-- The class's tallies: 9 walk, 7 come by bus, 5 by bike and 3 by car — 24 answers in all.
`decide` makes Lean count every category itself. -/
theorem class_tallies :
    tally .walk answers = 9 ∧ tally .bus answers = 7 ∧ tally .bike answers = 5 ∧
      tally .car answers = 3 ∧ answers.length = 24 := by
  decide
-- @endregion

-- @region data_and_tallies.totals_add_up
-- @provenance independent
/-- **The totals add up.** For *every* list of answers, the four tallies add up to the number of
answers. Proof by induction on the list: one more answer adds one mark to the tally of its own
category and none to the others, so both sides grow by one. -/
theorem totals_add_up (l : List Way) :
    tally .walk l + tally .bus l + tally .bike l + tally .car l = l.length := by
  induction l with
  | nil => rfl
  | cons w rest ih =>
    unfold tally at ih ⊢
    -- Look at which category the new answer `w` is in; `simp` uses `List.count_cons`.
    cases w <;> simp <;> omega
-- @endregion

-- @region data_and_tallies.walk_is_most
-- @provenance independent
/-- Walking is the most common answer: no category has a bigger tally. We check each of the
four categories in turn. -/
theorem walk_is_most : ∀ w : Way, tally w answers ≤ tally .walk answers := by
  intro w
  cases w <;> decide
-- @endregion

-- @region data_and_tallies.how_many_more
-- @provenance independent
/-- "How many more children walk than come by bus?" Two more: `9 − 7 = 2`. -/
theorem how_many_more : tally .walk answers - tally .bus answers = 2 := by decide
-- @endregion

/-! ### Tally marks in fives -/

-- @region data_and_tallies.gates
-- @provenance definition
/-- The number of complete groups of five ("gates") in a tally of `n` marks. -/
def gates (n : Nat) : Nat := n / 5
-- @endregion

-- @region data_and_tallies.loose
-- @provenance definition
/-- The marks left over after the complete groups of five. -/
def loose (n : Nat) : Nat := n % 5
-- @endregion

-- @region data_and_tallies.tally_in_fives
-- @provenance library
/-- Counting a tally by fives, then counting on the loose marks, always gives the number of
marks: `5 × gates + loose = n`. This applies core Lean's `Nat.div_add_mod`. -/
theorem tally_in_fives (n : Nat) : 5 * gates n + loose n = n := Nat.div_add_mod n 5
-- @endregion

-- @region data_and_tallies.nine_in_fives
-- @provenance independent
/-- A tally of 9 is one gate of five and four loose marks. -/
theorem nine_in_fives : gates 9 = 1 ∧ loose 9 = 4 := ⟨rfl, rfl⟩
-- @endregion

/-! ### When one answer is counted in two categories -/

-- @region data_and_tallies.fruit
-- @provenance definition
/-- Fruits for the question "Which fruits do you like?", where children may choose several. -/
inductive Fruit where
  | mango | banana | papaya
  deriving DecidableEq, Repr
-- @endregion

-- @region data_and_tallies.likes
-- @provenance definition
/-- Four children's answers. The second and fourth child each chose two fruits. -/
def likes : List (List Fruit) := [[.mango], [.banana, .mango], [.papaya], [.mango, .papaya]]
-- @endregion

-- @region data_and_tallies.likers
-- @provenance definition
/-- How many children chose fruit `f`. -/
def likers (f : Fruit) (l : List (List Fruit)) : Nat := l.countP (fun choices => choices.contains f)
-- @endregion

-- @region data_and_tallies.likes_overcount
-- @provenance independent
/-- With several answers allowed, the totals no longer add up to the number of children: the
three totals are 3, 1 and 2, which make 6, but only 4 children were asked. -/
theorem likes_overcount :
    likers .mango likes + likers .banana likes + likers .papaya likes = 6 ∧ likes.length = 4 := by
  decide
-- @endregion

end Lumenary.DataAndTallies
