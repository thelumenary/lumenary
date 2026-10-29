/-
The Lumenary — formal mathematics
One thing after another ("for grown-ups" companion to the Grades 3–5 lesson).

An action is a function from things to things, and "do `f`, then do `g`" is the chain
`andThen f g` (written `g ∘ f` later on). We show that "add 5, then double" and "double, then
add 5" differ for every starting number, while two additions (or two multiplications) can be
done in either order; that a quarter turn and a flip of an L-shaped tile do not commute; that
four quarter turns do nothing; and, in general, the **socks-and-shoes rule**: a chain is undone
by undoing its steps in reverse order — first for two steps, then for chains of any length.

Core Lean 4 only. Mathlib analogue: `Function.comp`, `Function.LeftInverse.comp`, and in groups
`mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹`.
-/

namespace Lumenary.ChainingActions

/-! ### Chains of actions -/

-- @region chaining_actions.and_then
-- @provenance definition
/-- `andThen f g` is the chain "do `f`, then do `g` to the result". Later you will meet it
written `g ∘ f`, read "`g` after `f`". -/
def andThen {α : Type} (f g : α → α) : α → α := fun x => g (f x)
-- @endregion

-- @region chaining_actions.add_five
-- @provenance definition
/-- The action "add 5". -/
def addFive (n : Nat) : Nat := n + 5
-- @endregion

-- @region chaining_actions.double
-- @provenance definition
/-- The action "double". -/
def double (n : Nat) : Nat := 2 * n
-- @endregion

-- @region chaining_actions.start_at_three
-- @provenance independent
/-- Starting at 3: "add 5, then double" goes 3 → 8 → 16, but "double, then add 5" goes
3 → 6 → 11. -/
theorem start_at_three : andThen addFive double 3 = 16 ∧ andThen double addFive 3 = 11 := by
  decide
-- @endregion

-- @region chaining_actions.add_then_double
-- @provenance independent
/-- For **every** starting number `n`, "add 5, then double" gives exactly 5 more than "double,
then add 5": doubling `n + 5` doubles the 5 as well, giving `2 × n + 10` instead of
`2 × n + 5`. -/
theorem add_then_double (n : Nat) :
    andThen addFive double n = andThen double addFive n + 5 := by
  unfold andThen addFive double
  omega
-- @endregion

-- @region chaining_actions.never_agree
-- @provenance independent
/-- So the two orders **never** give the same result, whatever number you start with. -/
theorem never_agree (n : Nat) : andThen addFive double n ≠ andThen double addFive n := by
  rw [add_then_double]
  omega
-- @endregion

-- @region chaining_actions.adding_commutes
-- @provenance independent
/-- But some actions can be done in either order: "add `a`, then add `b`" is the same action as
"add `b`, then add `a`", for every starting number. -/
theorem adding_commutes (a b : Nat) :
    andThen (· + a) (· + b) = andThen (· + b) (· + a) := by
  funext n
  show n + a + b = n + b + a
  omega
-- @endregion

-- @region chaining_actions.multiplying_commutes
-- @provenance library
/-- Likewise "multiply by `a`, then by `b`" is the same as "multiply by `b`, then by `a`". This
applies core Lean's `Nat.mul_right_comm`. -/
theorem multiplying_commutes (a b : Nat) :
    andThen (· * a) (· * b) = andThen (· * b) (· * a) := by
  funext n
  exact Nat.mul_right_comm n a b
-- @endregion

/-! ### Undoing a chain: socks and shoes -/

-- @region chaining_actions.undoes
-- @provenance definition
/-- `Undoes u f` says that the action `u` undoes the action `f`: doing `f` and then `u` puts
every thing back exactly as it was. -/
def Undoes {α : Type} (u f : α → α) : Prop := ∀ x, u (f x) = x
-- @endregion

-- @region chaining_actions.socks_and_shoes
-- @provenance independent
/-- **The socks-and-shoes rule.** If `uf` undoes `f` and `ug` undoes `g`, then the chain
"`f`, then `g`" is undone by "`ug`, then `uf`" — undo the **last** action first. After `f` and
`g`, undoing `g` takes us back to just after `f`; then undoing `f` takes us back to the
start. -/
theorem socks_and_shoes {α : Type} {f g uf ug : α → α}
    (hf : Undoes uf f) (hg : Undoes ug g) : Undoes (andThen ug uf) (andThen f g) := by
  intro x
  unfold andThen
  rw [hg (f x), hf x]
-- @endregion

-- @region chaining_actions.halve
-- @provenance definition
/-- The action "halve" on whole numbers (Lean rounds an odd number down). -/
def halve (n : Nat) : Nat := n / 2
-- @endregion

-- @region chaining_actions.sub_five
-- @provenance definition
/-- The action "subtract 5" on whole numbers (Lean stops at 0). -/
def subFive (n : Nat) : Nat := n - 5
-- @endregion

-- @region chaining_actions.halve_undoes_double
-- @provenance independent
/-- Halving undoes doubling. -/
theorem halve_undoes_double : Undoes halve double := by
  intro n
  unfold halve double
  omega
-- @endregion

-- @region chaining_actions.sub_five_undoes_add_five
-- @provenance independent
/-- Subtracting 5 undoes adding 5. -/
theorem subFive_undoes_addFive : Undoes subFive addFive := by
  intro n
  unfold subFive addFive
  omega
-- @endregion

-- @region chaining_actions.undo_add_five_then_double
-- @provenance independent
/-- "Add 5, then double" is undone by "halve, then subtract 5" — the undoing actions in reverse
order. This is the socks-and-shoes rule applied to the two facts above. -/
theorem undo_addFive_then_double : Undoes (andThen halve subFive) (andThen addFive double) :=
  socks_and_shoes subFive_undoes_addFive halve_undoes_double
-- @endregion

-- @region chaining_actions.wrong_order_fails
-- @provenance independent
/-- Undoing in the original order does **not** work: "subtract 5, then halve" does not undo
"add 5, then double". From 3 the chain reaches 16, and 16 − 5 = 11 is odd, so halving cannot
give back 3. -/
theorem wrong_order_fails : ¬ Undoes (andThen subFive halve) (andThen addFive double) := by
  intro h
  have h3 := h 3
  revert h3
  decide
-- @endregion

/-! ### Turning and flipping -/

-- @region chaining_actions.dir
-- @provenance definition
/-- The four directions an arrow on a card can point. -/
inductive Dir where
  | up | right | down | left
  deriving DecidableEq, Repr
-- @endregion

-- @region chaining_actions.quarter_turn
-- @provenance definition
/-- A quarter turn clockwise (the way clock hands go). -/
def quarterTurn : Dir → Dir
  | .up => .right
  | .right => .down
  | .down => .left
  | .left => .up
-- @endregion

-- @region chaining_actions.four_quarter_turns
-- @provenance independent
/-- Four quarter turns, one after another, have the same effect as doing nothing: a full
turn. There are only four directions to check. -/
theorem four_quarter_turns (d : Dir) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn d))) = d := by
  cases d <;> rfl
-- @endregion

-- @region chaining_actions.three_more_turns_undo
-- @provenance independent
/-- So a quarter turn is undone by **three more** quarter turns. -/
theorem three_more_turns_undo :
    Undoes (andThen quarterTurn (andThen quarterTurn quarterTurn)) quarterTurn := by
  intro d
  cases d <;> rfl
-- @endregion

-- @region chaining_actions.turn_point
-- @provenance definition
/-- A quarter turn clockwise about the corner `(0, 0)`, acting on a point `(x, y)` of the grid
(with `y` going up): it sends `(x, y)` to `(y, −x)`, so "up" `(0, 1)` goes to "right"
`(1, 0)`. -/
def turnPoint (p : Int × Int) : Int × Int := (p.2, -p.1)
-- @endregion

-- @region chaining_actions.flip_point
-- @provenance definition
/-- Flipping a tile over, left to right: the mirror image in the up–down line through
`(0, 0)`. -/
def flipPoint (p : Int × Int) : Int × Int := (-p.1, p.2)
-- @endregion

-- @region chaining_actions.l_shape
-- @provenance definition
/-- An L-shaped tile, as the grid points it covers: a bar from `(0, 0)` up to `(0, 2)` and a
foot out to `(1, 0)`. -/
def lShape : List (Int × Int) := [(0, 2), (0, 1), (0, 0), (1, 0)]
-- @endregion

-- @region chaining_actions.turn_flip_differ
-- @provenance independent
/-- **Turning and flipping do not commute.** "Turn, then flip" moves the L so that it covers
the point `(−1, 0)`; "flip, then turn" leaves that point empty. So the two chains put the
tile in different positions. -/
theorem turn_flip_differ :
    ((-1, 0) : Int × Int) ∈ lShape.map (andThen turnPoint flipPoint) ∧
    ((-1, 0) : Int × Int) ∉ lShape.map (andThen flipPoint turnPoint) := by
  decide
-- @endregion

-- @region chaining_actions.four_turns_points
-- @provenance independent
/-- Four quarter turns move every point of the grid back to where it started:
`(x, y) → (y, −x) → (−x, −y) → (−y, x) → (x, y)`. -/
theorem four_turns_points (p : Int × Int) :
    turnPoint (turnPoint (turnPoint (turnPoint p))) = p := by
  obtain ⟨x, y⟩ := p
  simp [turnPoint]
-- @endregion

/-! ### Chains of any length -/

-- @region chaining_actions.step
-- @provenance definition
/-- A step that can be undone: an action `act`, an action `back`, and a guarantee that `back`
undoes `act`. -/
structure Step (α : Type) where
  act : α → α
  back : α → α
  back_act : ∀ x, back (act x) = x
-- @endregion

-- @region chaining_actions.run_steps
-- @provenance definition
/-- Follow a chain of steps, first to last. -/
def runSteps {α : Type} : List (Step α) → α → α
  | [], x => x
  | s :: ss, x => runSteps ss (s.act x)
-- @endregion

-- @region chaining_actions.undo_steps
-- @provenance definition
/-- Undo a chain of steps: undo all the *later* steps first, and the first step last. -/
def undoSteps {α : Type} : List (Step α) → α → α
  | [], x => x
  | s :: ss, x => s.back (undoSteps ss x)
-- @endregion

-- @region chaining_actions.undo_run
-- @provenance independent
/-- **Undoing in reverse order works for chains of any length.** Proved by working through the
chain: undoing the rest of the chain takes us back to just after the first step, and undoing
the first step takes us back to the start. -/
theorem undo_run {α : Type} (ss : List (Step α)) (x : α) : undoSteps ss (runSteps ss x) = x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    simp only [runSteps, undoSteps]
    rw [ih, s.back_act]
-- @endregion

-- @region chaining_actions.add_five_step
-- @provenance definition
/-- "Add 5", with its undo "subtract 5". -/
def addFiveStep : Step Nat := ⟨addFive, subFive, subFive_undoes_addFive⟩
-- @endregion

-- @region chaining_actions.double_step
-- @provenance definition
/-- "Double", with its undo "halve". -/
def doubleStep : Step Nat := ⟨double, halve, halve_undoes_double⟩
-- @endregion

-- @region chaining_actions.there_and_back
-- @provenance independent
/-- There and back again: the chain add 5, double, add 5 takes 3 to 21, and undoing it in
reverse order (subtract 5, halve, subtract 5) brings 21 back to 3. -/
theorem there_and_back :
    runSteps [addFiveStep, doubleStep, addFiveStep] 3 = 21 ∧
    undoSteps [addFiveStep, doubleStep, addFiveStep] 21 = 3 := by
  decide
-- @endregion

end Lumenary.ChainingActions
