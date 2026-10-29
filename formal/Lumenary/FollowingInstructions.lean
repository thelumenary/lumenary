/-
The Lumenary — formal mathematics
Following and giving precise instructions: programs for moving on a grid ("for grown-ups"
companion to the K–2 lesson).

Two little programming languages. *Arrow cards* move one square up, down, left or right on a
grid map. A *floor robot* understands "forward", "turn left" and "turn right", so where it
goes depends on which way it is facing. A program is a list of instructions, followed one
after another; Lean runs programs exactly as written, with no guessing.

What is proved: running one program and then another is the same as running the joined
program (`run_append`); two different programs can reach the same square; every arrow program
needs at least as many steps as the "across plus up" distance to its target, and a program of
exactly that length always exists (`taxi_le_length`, `straight_route`); for the robot the
order of instructions matters, "turn left, then turn right" does nothing, and a buggy program
is fixed by changing one instruction. Core Lean 4 only. Mathlib analogue: lists and
`List.foldl` are core Lean; the "across plus up" distance is the ℓ¹ (taxicab) distance.
-/

namespace Lumenary.FollowingInstructions

/-! ### Arrow cards on a grid map -/

-- @region following_instructions.pos
-- @provenance definition
/-- A square on a grid map: `x` squares to the right and `y` squares up from the start. -/
structure Pos where
  x : Int
  y : Int
  deriving DecidableEq, Repr
-- @endregion

-- @region following_instructions.arrow
-- @provenance definition
/-- The four arrow cards. -/
inductive Arrow where
  | up | down | left | right
  deriving DecidableEq, Repr
-- @endregion

-- @region following_instructions.step
-- @provenance definition
/-- What one arrow card does: move one square in its direction. -/
def step : Arrow → Pos → Pos
  | .up, p => ⟨p.x, p.y + 1⟩
  | .down, p => ⟨p.x, p.y - 1⟩
  | .left, p => ⟨p.x - 1, p.y⟩
  | .right, p => ⟨p.x + 1, p.y⟩
-- @endregion

-- @region following_instructions.run
-- @provenance definition
/-- Follow a program of arrow cards from the square `p`: do the first card, then follow the
rest of the program from where you are. -/
def run : List Arrow → Pos → Pos
  | [], p => p
  | a :: prog, p => run prog (step a p)
-- @endregion

-- @region following_instructions.start
-- @provenance definition
/-- The start square. -/
def start : Pos := ⟨0, 0⟩
-- @endregion

-- @region following_instructions.run_append
-- @provenance independent
/-- Following program `p` and then program `q` is the same as following the joined program
`p ++ q`. Proof by induction on `p`. -/
theorem run_append (p q : List Arrow) (s : Pos) : run (p ++ q) s = run q (run p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => exact ih (step a s)
-- @endregion

-- @region following_instructions.to_the_tree
-- @provenance independent
/-- The program `→ → ↑` takes you from the start to the square 2 across and 1 up. -/
theorem to_the_tree : run [.right, .right, .up] start = ⟨2, 1⟩ := rfl
-- @endregion

-- @region following_instructions.two_programs
-- @provenance independent
/-- There is more than one correct program: `↑ → →` and `→ ↑ →` are different programs that
end on the same square as `→ → ↑`. -/
theorem two_programs :
    run [.up, .right, .right] start = ⟨2, 1⟩ ∧ run [.right, .up, .right] start = ⟨2, 1⟩ ∧
    [Arrow.up, .right, .right] ≠ [.right, .up, .right] := by
  decide
-- @endregion

-- @region following_instructions.taxi
-- @provenance definition
/-- The "across plus up" distance between two squares: how many squares across, plus how many
squares up or down. (Grown-ups call it the taxicab distance.) -/
def taxi (p q : Pos) : Nat := (q.x - p.x).natAbs + (q.y - p.y).natAbs
-- @endregion

-- @region following_instructions.taxi_step
-- @provenance independent
/-- One arrow card changes the "across plus up" distance from a fixed square by at most 1. -/
theorem taxi_step (s p : Pos) (a : Arrow) : taxi s (step a p) ≤ taxi s p + 1 := by
  cases a <;> simp only [taxi, step] <;> omega
-- @endregion

-- @region following_instructions.taxi_le_length
-- @provenance independent
/-- **No program is shorter than the distance.** Every arrow program that goes from `s` to a
square uses at least as many cards as the "across plus up" distance to that square: each card
moves you at most one square closer. Proof by induction on the program. -/
theorem taxi_le_length (prog : List Arrow) (s : Pos) : taxi s (run prog s) ≤ prog.length := by
  -- Strengthen: start the program at any square `p`, measuring from `s`.
  suffices h : ∀ p : Pos, taxi s (run prog p) ≤ taxi s p + prog.length by
    have := h s
    simpa [taxi] using this
  induction prog with
  | nil => intro p; simp [run]
  | cons a prog ih =>
    intro p
    have h1 := ih (step a p)
    have h2 := taxi_step s p a
    simp only [run, List.length_cons]
    omega
-- @endregion

-- @region following_instructions.straight_route
-- @provenance independent
/-- **A shortest program always exists**: to reach the square `a` across and `b` up, use `a`
right arrows and then `b` up arrows — exactly `a + b` cards, the distance. -/
theorem straight_route (a b : Nat) :
    run (List.replicate a .right ++ List.replicate b .up) start = ⟨a, b⟩ := by
  rw [run_append]
  -- Each block of identical arrows moves you that many squares.
  have hr : ∀ (n : Nat) (p : Pos), run (List.replicate n .right) p = ⟨p.x + n, p.y⟩ := by
    intro n
    induction n with
    | zero => intro p; simp [run]
    | succ n ih =>
      intro p
      simp only [List.replicate, run, step, ih]
      congr 1
      omega
  have hu : ∀ (n : Nat) (p : Pos), run (List.replicate n .up) p = ⟨p.x, p.y + n⟩ := by
    intro n
    induction n with
    | zero => intro p; simp [run]
    | succ n ih =>
      intro p
      simp only [List.replicate, run, step, ih]
      congr 1
      omega
  rw [hr, hu]
  simp [start]
-- @endregion

/-! ### A floor robot that turns -/

-- @region following_instructions.heading
-- @provenance definition
/-- Which way the robot is facing. -/
inductive Heading where
  | north | east | south | west
  deriving DecidableEq, Repr
-- @endregion

-- @region following_instructions.robot
-- @provenance definition
/-- A floor robot: where it is, and which way it faces. -/
structure Robot where
  pos : Pos
  facing : Heading
  deriving DecidableEq, Repr
-- @endregion

-- @region following_instructions.cmd
-- @provenance definition
/-- The robot's three buttons. Turning happens on the spot: the robot stays on its square. -/
inductive Cmd where
  | forward | turnLeft | turnRight
  deriving DecidableEq, Repr
-- @endregion

-- @region following_instructions.exec
-- @provenance definition
/-- What one button does to the robot. -/
def exec : Cmd → Robot → Robot
  | .forward, ⟨p, .north⟩ => ⟨⟨p.x, p.y + 1⟩, .north⟩
  | .forward, ⟨p, .east⟩ => ⟨⟨p.x + 1, p.y⟩, .east⟩
  | .forward, ⟨p, .south⟩ => ⟨⟨p.x, p.y - 1⟩, .south⟩
  | .forward, ⟨p, .west⟩ => ⟨⟨p.x - 1, p.y⟩, .west⟩
  | .turnLeft, ⟨p, .north⟩ => ⟨p, .west⟩
  | .turnLeft, ⟨p, .west⟩ => ⟨p, .south⟩
  | .turnLeft, ⟨p, .south⟩ => ⟨p, .east⟩
  | .turnLeft, ⟨p, .east⟩ => ⟨p, .north⟩
  | .turnRight, ⟨p, .north⟩ => ⟨p, .east⟩
  | .turnRight, ⟨p, .east⟩ => ⟨p, .south⟩
  | .turnRight, ⟨p, .south⟩ => ⟨p, .west⟩
  | .turnRight, ⟨p, .west⟩ => ⟨p, .north⟩
-- @endregion

-- @region following_instructions.run_robot
-- @provenance definition
/-- Press the buttons of a robot program one after another. -/
def runRobot : List Cmd → Robot → Robot
  | [], r => r
  | c :: prog, r => runRobot prog (exec c r)
-- @endregion

-- @region following_instructions.home
-- @provenance definition
/-- The robot starts at the start square, facing north (up the page). -/
def home : Robot := ⟨start, .north⟩
-- @endregion

-- @region following_instructions.order_matters
-- @provenance independent
/-- **The order of the steps matters.** "Forward, then turn right" leaves the robot one square
up, facing east; "turn right, then forward" leaves it one square to the right. -/
theorem order_matters :
    runRobot [.forward, .turnRight] home = ⟨⟨0, 1⟩, .east⟩ ∧
    runRobot [.turnRight, .forward] home = ⟨⟨1, 0⟩, .east⟩ := by
  decide
-- @endregion

-- @region following_instructions.left_then_right
-- @provenance independent
/-- "Turn left, then turn right" does nothing at all, wherever the robot is and whichever way
it faces. (Check all four headings.) -/
theorem left_then_right (r : Robot) : exec .turnRight (exec .turnLeft r) = r := by
  obtain ⟨p, h⟩ := r
  cases h <;> rfl
-- @endregion

-- @region following_instructions.four_lefts
-- @provenance independent
/-- Four left turns bring the robot back to facing the way it started. -/
theorem four_lefts (r : Robot) : runRobot [.turnLeft, .turnLeft, .turnLeft, .turnLeft] r = r := by
  obtain ⟨p, h⟩ := r
  cases h <;> rfl
-- @endregion

-- @region following_instructions.debug
-- @provenance independent
/-- **Finding and fixing a bug.** The target is 2 squares up and 1 square to the right. The
program "forward, forward, turn left, forward" goes the wrong way (left instead of right);
changing the one wrong instruction to "turn right" fixes it. -/
theorem debug :
    (runRobot [.forward, .forward, .turnLeft, .forward] home).pos = ⟨-1, 2⟩ ∧
    (runRobot [.forward, .forward, .turnRight, .forward] home).pos = ⟨1, 2⟩ := by
  decide
-- @endregion

end Lumenary.FollowingInstructions
