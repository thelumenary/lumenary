/-
The Lumenary — formal mathematics
Doing and undoing: actions, the action of doing nothing, and actions that can or cannot be
undone ("for grown-ups" companion to the K–2 lesson).

An *action* on a little world of things is a function from the world to itself: it says what
each thing becomes. `u` *undoes* `a` when doing `a` and then `u` always puts everything back.
We model a card (face up or down), an arrow that can be turned, steps along a path, a tower
of blocks, an egg and a whiteboard, and prove which actions can be undone and how.

The main theorem, `cannot_undo_of_same_result`, explains why some actions cannot be undone
at all: if an action sends two different things to the same result, nothing can tell which
one to go back to. Core Lean 4 only. Mathlib analogue: an action that can be undone is a
function with a left inverse (`Function.LeftInverse`), which forces it to be injective
(`Function.LeftInverse.injective`); actions that can be undone in both orders are
permutations (`Equiv.Perm`), and collections of them form groups.
-/

namespace Lumenary.ActionsAndUndoing

/-! ### Actions, doing nothing, undoing -/

-- @region actions_and_undoing.action
-- @provenance definition
/-- An action on a world of things of type `α`: for each thing, what it becomes. -/
abbrev Action (α : Type) : Type := α → α
-- @endregion

-- @region actions_and_undoing.do_nothing
-- @provenance definition
/-- The action of **doing nothing**: every thing stays exactly as it was. -/
def doNothing {α : Type} : Action α := fun x => x
-- @endregion

-- @region actions_and_undoing.and_then
-- @provenance definition
/-- Do `a`, and then do `b`. -/
def andThen {α : Type} (a b : Action α) : Action α := fun x => b (a x)
-- @endregion

-- @region actions_and_undoing.undoes
-- @provenance definition
/-- `u` **undoes** `a` when doing `a` and then `u` puts every thing back as it was. -/
def Undoes {α : Type} (u a : Action α) : Prop := ∀ x, u (a x) = x
-- @endregion

-- @region actions_and_undoing.do_nothing_then
-- @provenance independent
/-- Doing nothing and then doing `a` has the same effect as just doing `a`. -/
theorem doNothing_andThen {α : Type} (a : Action α) : andThen doNothing a = a := rfl
-- @endregion

-- @region actions_and_undoing.then_do_nothing
-- @provenance independent
/-- Doing `a` and then doing nothing also has the same effect as just doing `a`. -/
theorem andThen_doNothing {α : Type} (a : Action α) : andThen a doNothing = a := rfl
-- @endregion

-- @region actions_and_undoing.undo_is_do_nothing
-- @provenance independent
/-- If `u` undoes `a`, then "do `a`, then `u`" is the same action as doing nothing. -/
theorem andThen_undo {α : Type} {a u : Action α} (h : Undoes u a) : andThen a u = doNothing :=
  funext h
-- @endregion

-- @region actions_and_undoing.do_nothing_undoes_itself
-- @provenance independent
/-- Doing nothing is undone by doing nothing. -/
theorem doNothing_undoes_doNothing {α : Type} : Undoes (doNothing : Action α) doNothing :=
  fun _ => rfl
-- @endregion

/-! ### A card: flipping undoes flipping -/

-- @region actions_and_undoing.card
-- @provenance definition
/-- A card lies face up or face down. -/
inductive Card where
  | faceUp | faceDown
  deriving DecidableEq, Repr
-- @endregion

-- @region actions_and_undoing.flip
-- @provenance definition
/-- Flip the card over. -/
def flip : Action Card
  | .faceUp => .faceDown
  | .faceDown => .faceUp
-- @endregion

-- @region actions_and_undoing.flip_undoes_flip
-- @provenance independent
/-- Flipping a card is undone by flipping it again. Check both cases. -/
theorem flip_undoes_flip : Undoes flip flip := by
  intro c
  cases c <;> rfl
-- @endregion

/-! ### An arrow: quarter turns -/

-- @region actions_and_undoing.arrow
-- @provenance definition
/-- An arrow on a card can point up, right, down or left. -/
inductive Arrow where
  | up | right | down | left
  deriving DecidableEq, Repr
-- @endregion

-- @region actions_and_undoing.quarter_turn
-- @provenance definition
/-- Turn the arrow a quarter turn clockwise (the way clock hands go). -/
def quarterTurn : Action Arrow
  | .up => .right
  | .right => .down
  | .down => .left
  | .left => .up
-- @endregion

-- @region actions_and_undoing.quarter_back
-- @provenance definition
/-- Turn the arrow a quarter turn back (anticlockwise). -/
def quarterBack : Action Arrow
  | .up => .left
  | .left => .down
  | .down => .right
  | .right => .up
-- @endregion

-- @region actions_and_undoing.quarter_back_undoes
-- @provenance independent
/-- A quarter turn is undone by a quarter turn back. -/
theorem quarterBack_undoes_quarterTurn : Undoes quarterBack quarterTurn := by
  intro a
  cases a <;> rfl
-- @endregion

-- @region actions_and_undoing.three_more_turns
-- @provenance independent
/-- A quarter turn is *also* undone by three more quarter turns the same way. -/
theorem three_more_turns_undo :
    Undoes (fun a => quarterTurn (quarterTurn (quarterTurn a))) quarterTurn := by
  intro a
  cases a <;> rfl
-- @endregion

-- @region actions_and_undoing.quarter_turn_not_self_undo
-- @provenance independent
/-- A quarter turn is **not** undone by doing it again: an arrow pointing up ends up pointing
down. One counterexample is enough. -/
theorem quarterTurn_not_undone_by_itself : ¬ Undoes quarterTurn quarterTurn := by
  intro h
  have hup : quarterTurn (quarterTurn Arrow.up) = Arrow.up := h Arrow.up
  -- But two quarter turns take `up` to `down`, and `down ≠ up`.
  exact absurd hup (by decide)
-- @endregion

/-! ### Steps along a path -/

-- @region actions_and_undoing.forward
-- @provenance definition
/-- Walk `n` steps forward along a path (positions are integers). -/
def forward (n : Int) : Action Int := fun x => x + n
-- @endregion

-- @region actions_and_undoing.back
-- @provenance definition
/-- Walk `n` steps back. -/
def back (n : Int) : Action Int := fun x => x - n
-- @endregion

-- @region actions_and_undoing.back_undoes_forward
-- @provenance library
/-- "Take 3 steps forward" is undone by "take 3 steps back" — for any number of steps.
This applies core Lean's `Int.add_sub_cancel`. -/
theorem back_undoes_forward (n : Int) : Undoes (back n) (forward n) :=
  fun x => Int.add_sub_cancel x n
-- @endregion

-- @region actions_and_undoing.forward_again
-- @provenance independent
/-- Walking forward again does **not** undo walking forward (unless the number of steps is
`0`): starting from `0`, two walks of `n` steps end at `n + n`, not at `0`. -/
theorem forward_not_undone_by_itself (n : Int) (hn : n ≠ 0) :
    ¬ Undoes (forward n) (forward n) := by
  intro h
  have h0 : 0 + n + n = 0 := h 0
  omega
-- @endregion

/-! ### Actions that cannot be undone -/

-- @region actions_and_undoing.cannot_undo
-- @provenance independent
/-- **Why some actions cannot be undone.** If an action sends two *different* things `x`
and `y` to the *same* result, then no action can undo it: an undo would have to take that one
result back to `x` and also back to `y`.
`x = u (a x) = u (a y) = y`, which contradicts `x ≠ y`. -/
theorem cannot_undo_of_same_result {α : Type} (a : Action α) {x y : α} (hxy : x ≠ y)
    (h : a x = a y) : ¬ ∃ u, Undoes u a := by
  intro ⟨u, hu⟩
  apply hxy
  calc x = u (a x) := (hu x).symm
    _ = u (a y) := by rw [h]
    _ = y := hu y
-- @endregion

-- @region actions_and_undoing.board
-- @provenance definition
/-- A small whiteboard that shows a picture of a cat, a picture of a dog, or nothing. -/
inductive Board where
  | cat | dog | blank
  deriving DecidableEq, Repr
-- @endregion

-- @region actions_and_undoing.wipe
-- @provenance definition
/-- Wipe the board clean, whatever was on it. -/
def wipe : Action Board := fun _ => .blank
-- @endregion

-- @region actions_and_undoing.wipe_cannot_be_undone
-- @provenance independent
/-- Wiping the board cannot be undone: the cat board and the dog board both become blank,
so no action can know which picture to bring back. -/
theorem wipe_cannot_be_undone : ¬ ∃ u, Undoes u wipe :=
  cannot_undo_of_same_result wipe (x := .cat) (y := .dog) (by decide) rfl
-- @endregion

-- @region actions_and_undoing.egg
-- @provenance definition
/-- An egg is whole or cracked. -/
inductive Egg where
  | whole | cracked
  deriving DecidableEq, Repr
-- @endregion

-- @region actions_and_undoing.crack
-- @provenance definition
/-- Crack the egg. (Cracking an egg that is already cracked leaves it cracked.) -/
def crack : Action Egg := fun _ => .cracked
-- @endregion

-- @region actions_and_undoing.crack_cannot_be_undone
-- @provenance independent
/-- Cracking an egg cannot be undone, even in our tiny model: a whole egg and a cracked egg
both end up cracked. -/
theorem crack_cannot_be_undone : ¬ ∃ u, Undoes u crack :=
  cannot_undo_of_same_result crack (x := .whole) (y := .cracked) (by decide) rfl
-- @endregion

/-! ### A tower of blocks -/

-- @region actions_and_undoing.add_block
-- @provenance definition
/-- Put one more block on a tower (the tower's height is a natural number). -/
def addBlock : Action Nat := fun n => n + 1
-- @endregion

-- @region actions_and_undoing.take_block
-- @provenance definition
/-- Take one block off the tower. Taking a block from an empty spot does nothing:
in Lean, `0 - 1 = 0` for natural numbers. -/
def takeBlock : Action Nat := fun n => n - 1
-- @endregion

-- @region actions_and_undoing.take_undoes_add
-- @provenance library
/-- Adding a block is undone by taking it away again. This applies core Lean's
`Nat.add_sub_cancel`. -/
theorem takeBlock_undoes_addBlock : Undoes takeBlock addBlock :=
  fun n => Nat.add_sub_cancel n 1
-- @endregion

-- @region actions_and_undoing.take_cannot_be_undone
-- @provenance independent
/-- But "take a block away" cannot be undone in general: a tower of 1 block and an empty
spot both end up with 0 blocks, so nothing can tell whether to put a block back. -/
theorem takeBlock_cannot_be_undone : ¬ ∃ u, Undoes u takeBlock :=
  cannot_undo_of_same_result takeBlock (x := 1) (y := 0) (by decide) rfl
-- @endregion

end Lumenary.ActionsAndUndoing
