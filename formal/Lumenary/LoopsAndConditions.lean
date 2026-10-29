/-
The Lumenary — formal mathematics
Repetition and decisions ("for grown-ups" companion to the Grades 3–5 lesson).

A floor robot follows instructions; `repeatBlock n block` is the loop "repeat `n` times:
`block`". We check that "repeat 4 times: forward, turn right" brings the robot home while
3 repeats do not, and prove for all programs that loops can be split and joined. Decisions are
`if … then … else`: FizzBuzz, with a proof that it says "FizzBuzz" exactly for the multiples of
3 and 5, and that checking the conditions in the wrong order is a bug. Column addition is a
loop over the columns with a carry: we prove, for every list of columns, that it computes the
right sum and that with digits 0–9 the carry is never more than 1. Finally a "repeat until"
loop whose stopping condition is never true: Lean only accepts loops that finish, so we give
the loop a fuel tank, and prove that this loop always uses up all its fuel.

Core Lean 4 only. Mathlib analogue: `Nat.digits` and `Nat.ofDigits` for place value.
-/

namespace Lumenary.LoopsAndConditions

/-! ### A robot that repeats -/

-- @region loops_and_conditions.instr
-- @provenance definition
/-- The robot's two instructions. -/
inductive Instr where
  | forward | turnRight
  deriving DecidableEq, Repr
-- @endregion

-- @region loops_and_conditions.heading
-- @provenance definition
/-- The four directions the robot can face. -/
inductive Heading where
  | north | east | south | west
  deriving DecidableEq, Repr
-- @endregion

-- @region loops_and_conditions.robot
-- @provenance definition
/-- Where the robot is (`x` across, `y` up) and which way it faces. -/
structure Robot where
  x : Int
  y : Int
  heading : Heading
  deriving DecidableEq, Repr
-- @endregion

-- @region loops_and_conditions.turn_right
-- @provenance definition
/-- A quarter turn to the right (clockwise). -/
def turnRight : Heading → Heading
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north
-- @endregion

-- @region loops_and_conditions.step
-- @provenance definition
/-- Follow one instruction: move one square the way you face, or turn right on the spot. -/
def step (r : Robot) : Instr → Robot
  | .forward =>
    match r.heading with
    | .north => { r with y := r.y + 1 }
    | .east => { r with x := r.x + 1 }
    | .south => { r with y := r.y - 1 }
    | .west => { r with x := r.x - 1 }
  | .turnRight => { r with heading := turnRight r.heading }
-- @endregion

-- @region loops_and_conditions.run
-- @provenance definition
/-- Follow a whole program, one instruction after another. -/
def run (r : Robot) : List Instr → Robot
  | [] => r
  | i :: is => run (step r i) is
-- @endregion

-- @region loops_and_conditions.repeat_block
-- @provenance definition
/-- The loop "repeat `n` times: `block`", written out as a long program. -/
def repeatBlock : Nat → List Instr → List Instr
  | 0, _ => []
  | n + 1, block => block ++ repeatBlock n block
-- @endregion

-- @region loops_and_conditions.home
-- @provenance definition
/-- The robot starts at `(0, 0)`, facing north. -/
def home : Robot := ⟨0, 0, .north⟩
-- @endregion

-- @region loops_and_conditions.square_loop
-- @provenance independent
/-- The 3-line loop "repeat 4 times: forward, turn right" is the same as the 8-instruction
program written out in full. -/
theorem square_loop :
    repeatBlock 4 [.forward, .turnRight] =
      [.forward, .turnRight, .forward, .turnRight, .forward, .turnRight, .forward, .turnRight] :=
  rfl
-- @endregion

-- @region loops_and_conditions.square_returns
-- @provenance independent
/-- **The square loop brings the robot home**: back at `(0, 0)`, facing north again. -/
theorem square_returns : run home (repeatBlock 4 [.forward, .turnRight]) = home := by
  decide
-- @endregion

-- @region loops_and_conditions.three_repeats_not_home
-- @provenance independent
/-- The number of repeats matters: after only 3 repeats the robot is at `(1, 0)`, facing
west — three sides of the square, not home. -/
theorem three_repeats_not_home :
    run home (repeatBlock 3 [.forward, .turnRight]) = ⟨1, 0, .west⟩ := by
  decide
-- @endregion

-- @region loops_and_conditions.run_append
-- @provenance independent
/-- Following one program and then another is the same as following the two joined
together. Proved for every pair of programs. -/
theorem run_append (r : Robot) (p q : List Instr) : run r (p ++ q) = run (run r p) q := by
  induction p generalizing r with
  | nil => rfl
  | cons i is ih => exact ih (step r i)
-- @endregion

-- @region loops_and_conditions.repeat_add
-- @provenance independent
/-- "Repeat `m + n` times" is "repeat `m` times" followed by "repeat `n` times". -/
theorem repeat_add (m n : Nat) (block : List Instr) :
    repeatBlock (m + n) block = repeatBlock m block ++ repeatBlock n block := by
  induction m with
  | zero => simp [repeatBlock]
  | succ m ih => rw [Nat.succ_add, repeatBlock, repeatBlock, ih, List.append_assoc]
-- @endregion

-- @region loops_and_conditions.repeat_length
-- @provenance independent
/-- Written out in full, "repeat `n` times" a block of `k` instructions has `n × k`
instructions. A loop saves a lot of writing! -/
theorem repeat_length (n : Nat) (block : List Instr) :
    (repeatBlock n block).length = n * block.length := by
  induction n with
  | zero => simp [repeatBlock]
  | succ n ih => rw [repeatBlock, List.length_append, ih, Nat.succ_mul, Nat.add_comm]
-- @endregion

-- @region loops_and_conditions.eight_returns
-- @provenance independent
/-- Going round the square twice is the loop "repeat 8 times": it also brings the robot
home — because it is the square loop followed by the square loop. -/
theorem eight_returns : run home (repeatBlock 8 [.forward, .turnRight]) = home := by
  rw [show 8 = 4 + 4 from rfl, repeat_add, run_append, square_returns, square_returns]
-- @endregion

/-! ### Decisions: FizzBuzz -/

-- @region loops_and_conditions.say
-- @provenance definition
/-- What a player says in FizzBuzz. -/
inductive Say where
  | number (n : Nat)
  | fizz
  | buzz
  | fizzBuzz
  deriving DecidableEq, Repr
-- @endregion

-- @region loops_and_conditions.fizz_buzz
-- @provenance definition
/-- The FizzBuzz rule, as `if … then … else` decisions, checked in this order: multiple of 3
and of 5 (that is, of 15)? multiple of 3? multiple of 5? otherwise the number itself. -/
def fizzBuzz (n : Nat) : Say :=
  if n % 15 = 0 then .fizzBuzz
  else if n % 3 = 0 then .fizz
  else if n % 5 = 0 then .buzz
  else .number n
-- @endregion

-- @region loops_and_conditions.fizz_buzz_to_fifteen
-- @provenance independent
/-- The loop "for each number from 1 to 15: say `fizzBuzz n`". -/
theorem fizzBuzz_to_fifteen :
    (List.range' 1 15).map fizzBuzz =
      [.number 1, .number 2, .fizz, .number 4, .buzz, .fizz, .number 7, .number 8, .fizz,
       .buzz, .number 11, .fizz, .number 13, .number 14, .fizzBuzz] := by
  decide
-- @endregion

-- @region loops_and_conditions.fizz_buzz_iff
-- @provenance independent
/-- The rule says "FizzBuzz" **exactly** for the numbers that are multiples of 3 **and** of 5 —
for every number, not just the first fifteen. -/
theorem fizzBuzz_iff (n : Nat) : fizzBuzz n = .fizzBuzz ↔ n % 3 = 0 ∧ n % 5 = 0 := by
  unfold fizzBuzz
  split
  · constructor
    · intro _
      omega
    · intro _
      rfl
  · split
    · simp only [reduceCtorEq, false_iff]
      omega
    · split
      · simp only [reduceCtorEq, false_iff]
        omega
      · simp only [reduceCtorEq, false_iff]
        omega
-- @endregion

-- @region loops_and_conditions.fizz_buzz_buggy
-- @provenance definition
/-- A buggy version that checks "multiple of 3?" first. -/
def fizzBuzzBuggy (n : Nat) : Say :=
  if n % 3 = 0 then .fizz
  else if n % 5 = 0 then .buzz
  else if n % 15 = 0 then .fizzBuzz
  else .number n
-- @endregion

-- @region loops_and_conditions.buggy_never_fizz_buzz
-- @provenance independent
/-- **The order of the conditions matters.** The buggy version never says "FizzBuzz": every
multiple of 15 is a multiple of 3, so the first condition always catches it. -/
theorem buggy_never_fizzBuzz (n : Nat) : fizzBuzzBuggy n ≠ .fizzBuzz := by
  unfold fizzBuzzBuggy
  split
  · simp
  · split
    · simp
    · split
      · omega
      · simp
-- @endregion

/-! ### Column addition: a loop with a carry -/

-- @region loops_and_conditions.value
-- @provenance definition
/-- The value of a list of digits written **ones first**: `[3, 4, 6]` means
3 + 10 × 4 + 100 × 6 = 643. -/
def value : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * value ds
-- @endregion

-- @region loops_and_conditions.add_columns
-- @provenance definition
/-- **Column addition.** The columns are pairs (top digit, bottom digit), ones column first.
Loop over the columns: add the two digits and the carry, write down the ones digit of the
total, and carry the tens to the next column. At the end, write down the last carry if it is
not 0. -/
def addColumns : List (Nat × Nat) → Nat → List Nat
  | [], carry => if carry = 0 then [] else [carry]
  | (a, b) :: rest, carry =>
    (a + b + carry) % 10 :: addColumns rest ((a + b + carry) / 10)
-- @endregion

-- @region loops_and_conditions.example_368_275
-- @provenance independent
/-- 368 + 275: ones 8 + 5 = 13 (write 3, carry 1); tens 6 + 7 + 1 = 14 (write 4, carry 1);
hundreds 3 + 2 + 1 = 6. The answer is 643 (written ones first: `[3, 4, 6]`). -/
theorem example_368_275 :
    addColumns [(8, 5), (6, 7), (3, 2)] 0 = [3, 4, 6] ∧ value [3, 4, 6] = 368 + 275 := by
  decide
-- @endregion

-- @region loops_and_conditions.add_columns_correct
-- @provenance independent
/-- **Column addition is correct**, for every list of columns and every starting carry: the
value of the answer is the value of the top row plus the value of the bottom row plus the
carry. In each column the total `t` is split as `t = (t % 10) + 10 × (t / 10)`: the ones digit
stays, and the tens move one column left, where they are worth 10 times as much. -/
theorem addColumns_correct (cols : List (Nat × Nat)) (carry : Nat) :
    value (addColumns cols carry) =
      value (cols.map Prod.fst) + value (cols.map Prod.snd) + carry := by
  induction cols generalizing carry with
  | nil =>
    simp only [addColumns, List.map_nil]
    split
    · simp only [value]
      omega
    · simp only [value]
      omega
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [addColumns, value, List.map_cons, ih]
    omega
-- @endregion

-- @region loops_and_conditions.carry_le_one
-- @provenance independent
/-- With digits 0–9 and a carry of 0 or 1, a column total is at most 9 + 9 + 1 = 19, so the
next carry is again 0 or 1. -/
theorem carry_le_one (a b c : Nat) (ha : a ≤ 9) (hb : b ≤ 9) (hc : c ≤ 1) :
    (a + b + c) / 10 ≤ 1 := by
  omega
-- @endregion

-- @region loops_and_conditions.add_columns_digits
-- @provenance independent
/-- So, starting with no carry, column addition of two numbers written with digits 0–9 only
ever writes down digits 0–9: the answer is a proper number. -/
theorem addColumns_digits (cols : List (Nat × Nat)) (carry : Nat) (hc : carry ≤ 1)
    (hd : ∀ p ∈ cols, p.1 ≤ 9 ∧ p.2 ≤ 9) : ∀ d ∈ addColumns cols carry, d ≤ 9 := by
  induction cols generalizing carry with
  | nil =>
    intro d hdmem
    simp only [addColumns] at hdmem
    split at hdmem
    · simp at hdmem
    · simp only [List.mem_singleton] at hdmem
      omega
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    intro d hdmem
    simp only [addColumns, List.mem_cons] at hdmem
    have hab := hd (a, b) (List.mem_cons_self ..)
    rcases hdmem with rfl | hrest
    · omega
    · exact ih ((a + b + carry) / 10) (carry_le_one a b carry hab.1 hab.2 hc)
        (fun q hq => hd q (List.mem_cons_of_mem _ hq)) d hrest
-- @endregion

/-! ### Repeat until: a loop that never stops -/

-- @region loops_and_conditions.repeat_until
-- @provenance definition
/-- "Repeat `act` until `stop` is true", starting from `n`. Lean only accepts functions that
always finish, so the loop gets a fuel tank: it gives up after `fuel` steps. The answer is the
final number and the number of steps taken. -/
def repeatUntil (stop : Int → Bool) (act : Int → Int) : Nat → Int → Int × Nat
  | 0, n => (n, 0)
  | fuel + 1, n =>
    if stop n then (n, 0)
    else
      let r := repeatUntil stop act fuel (act n)
      (r.1, r.2 + 1)
-- @endregion

-- @region loops_and_conditions.count_up
-- @provenance independent
/-- "Start at 0; repeat 'add 3' until the number is bigger than 20": it stops at 21 after
7 steps. -/
theorem count_up : repeatUntil (fun m => m > 20) (· + 3) 100 0 = (21, 7) := by
  decide
-- @endregion

-- @region loops_and_conditions.count_down_fixed
-- @provenance independent
/-- "Start at 9; repeat 'take away 2' until the number is less than 1": it stops at −1 after
5 steps (9, 7, 5, 3, 1, −1). -/
theorem count_down_fixed : repeatUntil (fun m => m < 1) (· - 2) 100 9 = (-1, 5) := by
  decide
-- @endregion

-- @region loops_and_conditions.odd_minus_twos
-- @provenance independent
/-- Why "start at 9, take away 2 until you reach **exactly** 0" never stops: after `k` steps
the number is `9 − 2 × k`, which is odd, so it is never 0. -/
theorem odd_minus_twos (k : Nat) : (9 : Int) - 2 * k ≠ 0 := by
  omega
-- @endregion

-- @region loops_and_conditions.never_stops
-- @provenance independent
/-- The same fact about the loop itself: starting from **any odd number**, "take away 2 until
the number equals 0" uses up **all** of its fuel, however big the tank. The stopping condition
is never true, so on its own the loop would run for ever. -/
theorem never_stops (fuel : Nat) (n : Int) (h : n % 2 = 1) :
    (repeatUntil (fun m => m == 0) (· - 2) fuel n).2 = fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    have hne : n ≠ 0 := by omega
    simp [repeatUntil, hne, ih (n - 2) (by omega)]
-- @endregion

end Lumenary.LoopsAndConditions
