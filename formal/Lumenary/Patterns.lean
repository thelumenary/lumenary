/-
The Lumenary — formal mathematics
Patterns: repeating and growing patterns ("for grown-ups" companion to the K–2 lesson).

A pattern is a rule that gives the item at each position 1, 2, 3, …, so in Lean it is a
function from positions (natural numbers) to items. For a repeating pattern whose unit has `k`
items, the item `k` places further on is always the same; from that one fact we prove that the
item `k × q` places further on is the same, and hence that the item at any position can be
predicted from the remainder on division by `k` — without listing every item. For growing
patterns we prove that the rule "add 2 each time" and the rule "2 × the step number" give the
same pattern. Finally we prove that the first few items never decide a pattern: 1, 2, 4 can go on
as 8 (doubling) or as 7 (add 1, then 2, then 3), and in general any finite start can be
continued in two different ways.

Core Lean 4 only. Mathlib analogue: `Function.Periodic` and `Function.Periodic.map_mod_nat`
(a periodic function's value depends only on the remainder).
-/

namespace Lumenary.Patterns

/-! ### Repeating patterns -/

-- @region patterns.colour
-- @provenance definition
/-- The colours of Thandi's beads. -/
inductive Colour where
  | red | blue | green
  deriving DecidableEq, Repr
-- @endregion

-- @region patterns.bead
-- @provenance definition
/-- Thandi's necklace: red, blue, green, red, blue, green, … The bead at position `n` (counting
from 1) depends on the remainder when `n + 2` is divided by 3, so bead 1 is red, bead 2 blue
and bead 3 green. -/
def bead (n : Nat) : Colour :=
  match (n + 2) % 3 with
  | 0 => .red
  | 1 => .blue
  | _ => .green
-- @endregion

-- @region patterns.first_beads
-- @provenance independent
/-- The first six beads are red, blue, green, red, blue, green. -/
theorem first_beads :
    [bead 1, bead 2, bead 3, bead 4, bead 5, bead 6] = [.red, .blue, .green, .red, .blue, .green] :=
  rfl
-- @endregion

-- @region patterns.bead_repeats
-- @provenance independent
/-- **Three places on, the same colour.** The unit red–blue–green has 3 beads, so the bead 3 places
further on always has the same colour: adding 3 does not change the remainder on division by 3. -/
theorem bead_repeats (n : Nat) : bead (n + 3) = bead n := by
  have h : (n + 3 + 2) % 3 = (n + 2) % 3 := by
    rw [Nat.add_right_comm, Nat.add_mod_right]
  unfold bead
  rw [h]
-- @endregion

-- @region patterns.unit_is_not_one_bead
-- @provenance independent
/-- The unit is not a single bead: the pattern does *not* repeat after 1 place or after 2 places
(bead 2 differs from bead 1, and bead 3 differs from bead 1). -/
theorem unit_is_not_one_bead : bead 2 ≠ bead 1 ∧ bead 3 ≠ bead 1 := by decide
-- @endregion

-- @region patterns.repeats
-- @provenance definition
/-- A pattern `p` **repeats with a unit of `k` items** when the item `k` places further on is
always the same as the item here. -/
def Repeats {α : Type} (p : Nat → α) (k : Nat) : Prop := ∀ n, p (n + k) = p n
-- @endregion

-- @region patterns.repeats_many
-- @provenance independent
/-- If a pattern repeats with a unit of `k` items, then the item `k × q` places further on is
also the same, for every `q`. Proof by induction on `q`: each extra unit is `k` more places. -/
theorem repeats_many {α : Type} {p : Nat → α} {k : Nat} (h : Repeats p k) :
    ∀ q n, p (n + k * q) = p n := by
  intro q
  induction q with
  | zero => intro n; rfl
  | succ q ih =>
    intro n
    calc p (n + k * (q + 1)) = p ((n + k * q) + k) := by rw [Nat.mul_succ, Nat.add_assoc]
      _ = p (n + k * q) := h (n + k * q)
      _ = p n := ih n
-- @endregion

-- @region patterns.predict
-- @provenance independent
/-- **Predicting without drawing every item.** In a pattern that repeats with a unit of `k` items,
the item at position `n` is the same as the item at position `n % k` (the remainder when `n`
is divided by `k`): write `n = (n % k) + k × (n / k)` and use `repeats_many`. -/
theorem predict {α : Type} {p : Nat → α} {k : Nat} (h : Repeats p k) (n : Nat) :
    p n = p (n % k) := by
  calc p n = p (n % k + k * (n / k)) := by rw [Nat.mod_add_div]
    _ = p (n % k) := repeats_many h (n / k) (n % k)
-- @endregion

-- @region patterns.bead_hundred
-- @provenance independent
/-- The 100th bead is red. Since `100 = 3 × 33 + 1`, the 100th bead is the same as the 1st. -/
theorem bead_hundred : bead 100 = .red :=
  calc bead 100 = bead (100 % 3) := predict bead_repeats 100
    _ = .red := rfl
-- @endregion

/-! ### Growing patterns -/

-- @region patterns.add_two
-- @provenance definition
/-- The growing pattern 2, 4, 6, 8, … described by its step rule: start at 0 before step 1, and
add 2 at each step. -/
def addTwo : Nat → Nat
  | 0 => 0
  | n + 1 => addTwo n + 2
-- @endregion

-- @region patterns.twice
-- @provenance definition
/-- The same pattern described by a rule for the `n`-th item: `2 × n`. -/
def twice (n : Nat) : Nat := 2 * n
-- @endregion

-- @region patterns.add_two_eq_twice
-- @provenance independent
/-- **Two descriptions, one pattern.** "Add 2 each time" and "2 × the step number" give the same
item at every step. Proof by induction: both start at 0, and both grow by 2 at each step. -/
theorem addTwo_eq_twice (n : Nat) : addTwo n = twice n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc addTwo (k + 1) = addTwo k + 2 := rfl
      _ = twice k + 2 := by rw [ih]
      _ = twice (k + 1) := (Nat.mul_succ 2 k).symm
-- @endregion

/-! ### The first few items do not decide a pattern -/

-- @region patterns.doubling
-- @provenance definition
/-- The doubling rule: item `n` is `2 ^ (n - 1)`, giving 1, 2, 4, 8, 16, … -/
def doubling (n : Nat) : Nat := 2 ^ (n - 1)
-- @endregion

-- @region patterns.add_more
-- @provenance definition
/-- The "add one more each time" rule: start at 1, then add 1, then 2, then 3, …, giving
1, 2, 4, 7, 11, … (There is no item 0; we set `addMore 0 = 0`, and it is never used.) -/
def addMore : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => addMore (n + 1) + (n + 1)
-- @endregion

-- @region patterns.same_start_different_rules
-- @provenance independent
/-- **1, 2, 4 — and then?** The doubling rule and the add-more rule agree on the first three
items, 1, 2, 4, but the fourth item is 8 for one and 7 for the other. -/
theorem same_start_different_rules :
    [doubling 1, doubling 2, doubling 3] = [addMore 1, addMore 2, addMore 3] ∧
      doubling 4 = 8 ∧ addMore 4 = 7 := by
  decide
-- @endregion

-- @region patterns.start_never_decides
-- @provenance independent
/-- **No finite start decides a pattern.** Whatever list of first items `start` you are given,
there are two rules `f` and `g` that agree on all of them but give different next items. (Take
`f` to continue the list with 0s, and `g` to be the same except one bigger at the next place.) -/
theorem start_never_decides (start : List Nat) :
    ∃ f g : Nat → Nat, (∀ i, i < start.length → f i = g i) ∧ f start.length ≠ g start.length := by
  refine ⟨fun i => start.getD i 0,
    fun i => if i = start.length then start.getD i 0 + 1 else start.getD i 0, ?_, ?_⟩
  · intro i hi
    have hne : i ≠ start.length := Nat.ne_of_lt hi
    simp [hne]
  · simp
-- @endregion

end Lumenary.Patterns
