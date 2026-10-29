/-
The Lumenary — formal mathematics
Systematic listing and counting ("for grown-ups" companion to the Grades 3–5 lesson).

An organised list is a recipe that a computer can follow. Here the recipes are Lean functions:
`pairs` lists every (first choice, second choice), like the branches of a tree diagram;
`arrangements` lists every order of some objects; `handshakes` lists every pair of people once.
We prove, for all sizes, that the lists have the lengths the lesson predicts — `m × n`,
`1 × 2 × ⋯ × n`, and `n × (n − 1) ÷ 2` — and that the organised list of pairs misses nothing,
adds nothing and repeats nothing.

Core Lean 4 only. Mathlib analogue: `List.product` with `List.length_product`,
`List.permutations` with `List.length_permutations`, and `Finset.card_powersetCard` for
handshakes (choosing 2 of `n`).
-/

namespace Lumenary.SystematicListing

/-! ### Two choices: the product rule -/

-- @region systematic_listing.pairs
-- @provenance definition
/-- The organised list of all pairs `(a, b)`: take the first choices one at a time, and for each
one run through all the second choices — exactly what a tree diagram does. -/
def pairs {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, bs => bs.map (fun b => (a, b)) ++ pairs as bs
-- @endregion

-- @region systematic_listing.length_pairs
-- @provenance independent
/-- **The product rule.** With `m` first choices and `n` second choices there are `m × n` pairs:
each first choice starts a branch with `n` endings. -/
theorem length_pairs {α β : Type} (as : List α) (bs : List β) :
    (pairs as bs).length = as.length * bs.length := by
  induction as with
  | nil => simp [pairs]
  | cons a as ih =>
    simp only [pairs, List.length_append, List.length_map, ih, List.length_cons]
    rw [Nat.succ_mul]
    omega
-- @endregion

-- @region systematic_listing.mem_pairs
-- @provenance independent
/-- **Nothing is missed, nothing is extra.** A pair is on the organised list exactly when its
first part is one of the first choices and its second part is one of the second choices. -/
theorem mem_pairs {α β : Type} (as : List α) (bs : List β) (a : α) (b : β) :
    (a, b) ∈ pairs as bs ↔ a ∈ as ∧ b ∈ bs := by
  induction as with
  | nil => simp [pairs]
  | cons x xs ih =>
    simp only [pairs, List.mem_append, List.mem_map, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (⟨b', hb', rfl, rfl⟩ | ⟨ha, hb⟩)
      · exact ⟨Or.inl rfl, hb'⟩
      · exact ⟨Or.inr ha, hb⟩
    · rintro ⟨rfl | ha, hb⟩
      · exact Or.inl ⟨b, hb, rfl, rfl⟩
      · exact Or.inr ⟨ha, hb⟩
-- @endregion

-- @region systematic_listing.nodup_pairs
-- @provenance independent
/-- **Nothing is counted twice.** If the first choices are all different and the second choices
are all different, every pair on the organised list is different. Pairs from different branches
differ in their first part; pairs on the same branch differ in their second part. -/
theorem nodup_pairs {α β : Type} (as : List α) (bs : List β)
    (has : as.Nodup) (hbs : bs.Nodup) : (pairs as bs).Nodup := by
  induction as with
  | nil => simp [pairs]
  | cons a as ih =>
    rw [List.nodup_cons] at has
    simp only [pairs]
    rw [List.nodup_append]
    refine ⟨?_, ih has.2, ?_⟩
    · -- On the branch of `a`, pairs `(a, b₁)` and `(a, b₂)` differ because `b₁ ≠ b₂`.
      exact List.Pairwise.map _ (fun b₁ b₂ hne h => hne (Prod.mk.inj h).2) hbs
    · intro p hp q hq hpq
      subst hpq
      rw [List.mem_map] at hp
      obtain ⟨b, _, rfl⟩ := hp
      exact has.1 ((mem_pairs as bs a b).1 hq).1
-- @endregion

-- @region systematic_listing.shirts
-- @provenance definition
/-- Three shirts and two pairs of trousers. -/
def shirts : List String := ["red", "blue", "yellow"]
-- @endregion

-- @region systematic_listing.trousers
-- @provenance definition
/-- Two pairs of trousers. -/
def trousers : List String := ["black", "brown"]
-- @endregion

-- @region systematic_listing.outfits
-- @provenance independent
/-- The six outfits, listed shirt by shirt. Lean writes out the list itself and checks it. -/
theorem outfits :
    pairs shirts trousers =
      [("red", "black"), ("red", "brown"), ("blue", "black"), ("blue", "brown"),
       ("yellow", "black"), ("yellow", "brown")] := by
  decide
-- @endregion

-- @region systematic_listing.three_choices
-- @provenance independent
/-- Three choices in a row (starter, main course, drink) give `a × b × c` meals: pair the
starters with the mains first, then pair each of those with a drink. -/
theorem three_choices {α β γ : Type} (as : List α) (bs : List β) (cs : List γ) :
    (pairs (pairs as bs) cs).length = as.length * bs.length * cs.length := by
  rw [length_pairs, length_pairs]
-- @endregion

/-! ### Arrangements in a row -/

-- @region systematic_listing.insert_everywhere
-- @provenance definition
/-- All the ways to put `x` into a row `ys`: at the front, or after the first object, …, or at
the very end. -/
def insertEverywhere {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (y :: ·)
-- @endregion

-- @region systematic_listing.arrangements
-- @provenance definition
/-- Every arrangement of a row of objects: arrange all but the first object, then put the first
object into every possible place. -/
def arrangements {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (arrangements xs).flatMap (insertEverywhere x)
-- @endregion

-- @region systematic_listing.three_in_a_row
-- @provenance independent
/-- Ana, Bo and Chen can stand in a row in exactly these 6 orders, all different. -/
theorem three_in_a_row :
    arrangements ["Ana", "Bo", "Chen"] =
      [["Ana", "Bo", "Chen"], ["Bo", "Ana", "Chen"], ["Bo", "Chen", "Ana"],
       ["Ana", "Chen", "Bo"], ["Chen", "Ana", "Bo"], ["Chen", "Bo", "Ana"]] ∧
    (arrangements ["Ana", "Bo", "Chen"]).Nodup := by
  decide
-- @endregion

-- @region systematic_listing.factorial
-- @provenance definition
/-- `factorial n = 1 × 2 × ⋯ × n`, written `n!`. (Mathlib calls it `Nat.factorial`.) -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
-- @endregion

-- @region systematic_listing.length_insert_everywhere
-- @provenance independent
/-- In a row of `n` objects there are `n + 1` places to put one more object. -/
theorem length_insertEverywhere {α : Type} (x : α) (ys : List α) :
    (insertEverywhere x ys).length = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [insertEverywhere, ih]
-- @endregion

-- @region systematic_listing.mem_insert_everywhere_length
-- @provenance independent
/-- Putting one more object into a row of `n` objects always gives a row of `n + 1`. -/
theorem mem_insertEverywhere_length {α : Type} (x : α) (ys zs : List α)
    (h : zs ∈ insertEverywhere x ys) : zs.length = ys.length + 1 := by
  induction ys generalizing zs with
  | nil =>
    simp only [insertEverywhere, List.mem_singleton] at h
    subst h
    rfl
  | cons y ys ih =>
    simp only [insertEverywhere, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨ws, hws, rfl⟩
    · rfl
    · simp [ih ws hws]
-- @endregion

-- @region systematic_listing.mem_arrangements_length
-- @provenance independent
/-- Every arrangement of a row uses all of its objects: it has the same length as the row. -/
theorem mem_arrangements_length {α : Type} (xs zs : List α) (h : zs ∈ arrangements xs) :
    zs.length = xs.length := by
  induction xs generalizing zs with
  | nil =>
    simp only [arrangements, List.mem_singleton] at h
    subst h
    rfl
  | cons x xs ih =>
    simp only [arrangements, List.mem_flatMap] at h
    obtain ⟨ws, hws, hzs⟩ := h
    rw [mem_insertEverywhere_length x ws zs hzs, ih ws hws, List.length_cons]
-- @endregion

-- @region systematic_listing.length_flat_map_const
-- @provenance independent
/-- If every item on a list `L` opens a branch of exactly `k` endings, the tree has
`L.length × k` endings. -/
theorem length_flatMap_const {α β : Type} (L : List α) (f : α → List β) (k : Nat)
    (h : ∀ a ∈ L, (f a).length = k) : (L.flatMap f).length = L.length * k := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.length_append, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)), List.length_cons, Nat.succ_mul]
    omega
-- @endregion

-- @region systematic_listing.length_arrangements
-- @provenance independent
/-- **`n` different objects can be arranged in a row in `n!` ways.** Arrange the other `n − 1`
objects (in `(n − 1)!` ways), then choose one of the `n` places for the last object. -/
theorem length_arrangements {α : Type} (xs : List α) :
    (arrangements xs).length = factorial xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [arrangements]
    rw [length_flatMap_const _ _ (xs.length + 1)
      (fun ws hws => by rw [length_insertEverywhere, mem_arrangements_length xs ws hws]),
      ih, List.length_cons, factorial, Nat.mul_comm]
-- @endregion

/-! ### Handshakes: when order does not matter -/

-- @region systematic_listing.handshakes
-- @provenance definition
/-- The handshakes among people `0, 1, …, n - 1`, listed systematically: when person `n`
arrives, they shake hands with each of the `n` people already there. Each handshake `(i, j)`
is listed once, with `i < j`. -/
def handshakes : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => handshakes n ++ (List.range n).map (fun i => (i, n))
-- @endregion

-- @region systematic_listing.handshakes_count
-- @provenance independent
/-- **Counting handshakes.** Among `n` people there are `n × (n − 1) ÷ 2` handshakes; we state it
without division as `2 × handshakes + n = n × n`. (When person `n + 1` arrives, `n` new
handshakes appear.) -/
theorem handshakes_count (n : Nat) : 2 * (handshakes n).length + n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [handshakes, List.length_append, List.length_map, List.length_range]
    rw [Nat.succ_mul_succ]
    omega
-- @endregion

-- @region systematic_listing.five_friends
-- @provenance independent
/-- Five friends make 10 handshakes. Counting each person's 4 handshakes gives `5 × 4 = 20`,
which counts every handshake twice. -/
theorem five_friends : (handshakes 5).length = 10 ∧ 5 * 4 = 2 * 10 := by
  decide
-- @endregion

end Lumenary.SystematicListing
