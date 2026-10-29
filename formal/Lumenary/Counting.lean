/-
The Lumenary — formal mathematics
Counting: one number word for each object, why the last word tells how many, and comparing
collections by pairing ("for grown-ups" companion to the K–2 lesson on counting).

A collection is written as a Lean `List`, and counting aloud is modelled by `countAloud`, which
pairs each object with the number word said while touching it. We prove that every object gets
exactly one word, that the words said are 1, 2, 3, … with none skipped or repeated, that the
last word said is the number of objects (the "cardinal principle"), and that counting in a
different order ends on the same word. Separately, `Paired` describes lining two collections up
side by side; we prove that this works with none left over exactly when the two collections
have the same number of members. Finally: every counting number has a next one, so there is no
largest counting number.

Core Lean 4 only. Mathlib analogue: `List.length`, `List.Perm.length_eq`, `Finset.card`, and
`Fintype.card_congr` (finite types that can be paired one-to-one have the same cardinality).
-/

namespace Lumenary.Counting

/-! ### Counting aloud -/

-- @region counting.goats
-- @provenance definition
/-- Nomin's seven goats, in the order they come through the gate. -/
def goats : List String := ["Snowy", "Patch", "Socks", "Star", "Pebble", "Moss", "Biscuit"]
-- @endregion

-- @region counting.count_aloud
-- @provenance definition
/-- Counting aloud, starting with the number word `n`: the first object is paired with `n`,
the next object with the next number, and so on. Counting from one is `countAloud l 1`. -/
def countAloud {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, n => (n, x) :: countAloud xs (n + 1)
-- @endregion

-- @region counting.goats_last_word
-- @provenance independent
/-- Counting Nomin's goats from one, the last pair is "seven — Biscuit". Lean works out the
whole count itself, so `rfl` is enough. -/
theorem goats_last_word : (countAloud goats 1).getLast? = some (7, "Biscuit") := rfl
-- @endregion

-- @region counting.one_word_each
-- @provenance independent
/-- Every object is touched exactly once, in order: if we forget the number words and keep only
the objects, we get back exactly the collection we started with — nothing skipped, nothing
counted twice. Proof by induction on the list. -/
theorem one_word_each {α : Type} (l : List α) (n : Nat) :
    (countAloud l n).map Prod.snd = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [countAloud, ih]
-- @endregion

-- @region counting.words_said
-- @provenance independent
/-- The number words said are `n, n + 1, n + 2, …`, one for each object, in order and without
gaps or repeats. (`List.range' n k` is the list `[n, n + 1, …, n + k - 1]`.) -/
theorem words_said {α : Type} (l : List α) (n : Nat) :
    (countAloud l n).map Prod.fst = List.range' n l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [countAloud, ih, List.range'_succ]
-- @endregion

-- @region counting.last_word
-- @provenance independent
/-- Starting from the word `n`, the last word said for a non-empty collection is
`n + (number of objects) - 1`. Proof by induction: a one-object collection ends on `n`; for a
longer one, the last word is the last word of counting the rest, starting from `n + 1`. -/
theorem last_word {α : Type} (l : List α) (n : Nat) (h : l ≠ []) :
    ((countAloud l n).map Prod.fst).getLast? = some (n + l.length - 1) := by
  induction l generalizing n with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    cases xs with
    | nil => simp [countAloud]
    | cons y ys =>
      -- The rest of the collection, `y :: ys`, is counted starting from `n + 1`.
      have step := ih (n + 1) (List.cons_ne_nil y ys)
      simp only [countAloud, List.map_cons, List.getLast?_cons_cons] at step ⊢
      rw [step]
      simp only [List.length_cons]
      congr 1
      omega
-- @endregion

-- @region counting.last_word_is_count
-- @provenance independent
/-- **The last word tells how many.** Counting a non-empty collection from one, the last
number word said is exactly the number of objects in it (its length). -/
theorem last_word_is_count {α : Type} (l : List α) (h : l ≠ []) :
    ((countAloud l 1).map Prod.fst).getLast? = some l.length := by
  rw [last_word l 1 h, Nat.add_comm, Nat.add_sub_cancel]
-- @endregion

-- @region counting.count_any_order
-- @provenance independent
/-- **Order does not matter.** If `l₂` is the same collection as `l₁` in a different order
(`l₁.Perm l₂`: a rearrangement), counting either one ends on the same word. The words said
are `1, 2, …, length` (`words_said`), and rearranging does not change the length
(core Lean's `List.Perm.length_eq`). -/
theorem count_any_order {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ((countAloud l₁ 1).map Prod.fst).getLast? = ((countAloud l₂ 1).map Prod.fst).getLast? := by
  rw [words_said, words_said, h.length_eq]
-- @endregion

-- @region counting.count_reverse
-- @provenance library
/-- Counting backwards along the line of goats gives the same number as counting forwards.
This applies core Lean's `List.length_reverse`. -/
theorem count_reverse {α : Type} (l : List α) : l.reverse.length = l.length :=
  List.length_reverse
-- @endregion

-- @region counting.empty_count
-- @provenance independent
/-- Counting the empty collection: there is nothing to touch, so no number word is said at all.
The number of members of the empty collection is zero. -/
theorem empty_count : countAloud ([] : List String) 1 = [] ∧ ([] : List String).length = 0 :=
  ⟨rfl, rfl⟩
-- @endregion

/-! ### Comparing by pairing -/

-- @region counting.paired
-- @provenance definition
/-- `Paired xs ys` says the two collections can be lined up side by side, one member of `xs`
with one member of `ys`, with none left over: either both are empty, or we pair their first
members and can pair up the rest. -/
inductive Paired {α β : Type} : List α → List β → Prop
  | nil : Paired [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} : Paired xs ys → Paired (x :: xs) (y :: ys)
-- @endregion

-- @region counting.paired_same_count
-- @provenance independent
/-- If two collections pair up with none left over, counting them gives the same number.
Proof by induction on the pairing: each pair adds one to both counts. -/
theorem Paired.same_count {α β : Type} {xs : List α} {ys : List β} (h : Paired xs ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]
-- @endregion

-- @region counting.paired_of_same_count
-- @provenance independent
/-- Conversely, two collections with the same number of members can be paired up with none
left over: pair the first members, then pair the rest in the same way. -/
theorem paired_of_same_count {α β : Type} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length → Paired xs ys
  | [], [], _ => Paired.nil
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | _ :: xs, _ :: ys, h => Paired.cons (paired_of_same_count xs ys (by simpa using h))
-- @endregion

-- @region counting.paired_iff_same_count
-- @provenance independent
/-- **Pairing and counting agree.** Two collections pair up with none left over exactly when
they have the same number of members. -/
theorem paired_iff_same_count {α β : Type} (xs : List α) (ys : List β) :
    Paired xs ys ↔ xs.length = ys.length :=
  ⟨Paired.same_count, paired_of_same_count xs ys⟩
-- @endregion

-- @region counting.children
-- @provenance definition
/-- Tomás's four friends and Tomás himself: he hands out cups to his guests first. -/
def children : List String := ["Lina", "Kofi", "Mei", "Arjun", "Tomás"]
-- @endregion

-- @region counting.cups
-- @provenance definition
/-- The cups on the shelf. -/
def cups : List String := ["red", "blue", "green", "yellow"]
-- @endregion

-- @region counting.not_enough_cups
-- @provenance independent
/-- The children and the cups cannot be paired with none left over: if they could, there would
be as many children as cups, but there are 5 children and only 4 cups. -/
theorem not_enough_cups : ¬ Paired children cups := by
  intro h
  have same : children.length = cups.length := h.same_count
  -- `same` says `5 = 4`, which Lean can see is false.
  exact absurd same (by decide)
-- @endregion

/-! ### There is no largest counting number -/

-- @region counting.always_a_next
-- @provenance library
/-- Every counting number has a next one, and the next one is bigger.
This applies core Lean's `Nat.lt_succ_self`. -/
theorem always_a_next (n : Nat) : n < n + 1 := Nat.lt_succ_self n
-- @endregion

-- @region counting.no_largest_number
-- @provenance independent
/-- **There is no largest counting number.** Suppose some `n` were at least as big as every
counting number. Then `n + 1 ≤ n`, which is impossible. -/
theorem no_largest_number : ¬ ∃ n : Nat, ∀ m : Nat, m ≤ n := by
  intro ⟨n, h⟩
  have h' : n + 1 ≤ n := h (n + 1)
  exact Nat.not_succ_le_self n h'
-- @endregion

end Lumenary.Counting
