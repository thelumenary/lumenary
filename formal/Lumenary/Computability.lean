/-
The Lumenary — formal mathematics
Computability: Turing machines, diagonal arguments, the halting problem, reductions and
Rice's theorem.

Proved here (`@provenance independent`): a small Turing-machine simulator and two concrete runs
(a binary incrementer and the two-state busy beaver, checked by evaluation); the diagonal
argument behind the halting problem, stated abstractly for any notion of "program"; Cantor's
diagonal argument that no sequence lists every function `ℕ → ℕ`; the counting argument that some
function `ℕ → ℕ` is not computable; the transfer of undecidability along a many-one reduction;
and, from Rice's theorem, the undecidability of "does this program compute the zero function?".

From Mathlib (`@provenance library`): Mathlib's model of computation is the partial recursive
functions `Nat.Partrec`, with programs `Nat.Partrec.Code` and a universal evaluator
`Nat.Partrec.Code.eval` (Carneiro's formalisation). We cite the halting problem
`ComputablePred.halting_problem`, its recursive enumerability, Post's theorem
`ComputablePred.computable_iff_re_compl_re'` and Rice's theorem `ComputablePred.rice₂`.

Not formalised: the equivalence of our toy Turing machines with `Nat.Partrec` (Mathlib proves
related simulation results in `Mathlib.Computability.TuringMachine`), and the Church–Turing
thesis, which is not a mathematical statement at all.
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

namespace Lumenary.Computability

open Nat.Partrec (Code)

/-! ### A tiny Turing-machine simulator -/

-- @region computability.dir
-- @provenance definition
/-- The head of a Turing machine moves one cell left or right at every step. -/
inductive Dir
  | left
  | right
  deriving DecidableEq, Repr
-- @endregion

-- @region computability.tape
-- @provenance definition
/-- A two-symbol tape (`false` = blank `0`, `true` = `1`), stored as the scanned cell together
with the cells to its left and to its right, each list starting next to the head. Only finitely
many cells are ever non-blank; the lists grow when the head walks off their ends. -/
structure Tape where
  left : List Bool
  head : Bool
  right : List Bool
  deriving DecidableEq, Repr
-- @endregion

-- @region computability.tape_move
-- @provenance definition
/-- Move the head one cell. Walking off the stored part of the tape reveals a blank. -/
def Tape.move : Dir → Tape → Tape
  | .left, ⟨[], h, r⟩ => ⟨[], false, h :: r⟩
  | .left, ⟨a :: l, h, r⟩ => ⟨l, a, h :: r⟩
  | .right, ⟨l, h, []⟩ => ⟨h :: l, false, []⟩
  | .right, ⟨l, h, a :: r⟩ => ⟨h :: l, a, r⟩
-- @endregion

-- @region computability.tape_ones
-- @provenance definition
/-- The number of `1`s on the tape. -/
def Tape.ones (t : Tape) : Nat :=
  (t.left ++ t.head :: t.right).count true
-- @endregion

-- @region computability.machine
-- @provenance definition
/-- A Turing machine with states `Q`: in state `q` reading symbol `b`, it writes a symbol,
moves, and goes to a new state — or halts (`none`). The table is finite when `Q` is. -/
def Machine (Q : Type) := Q → Bool → Bool × Dir × Option Q
-- @endregion

-- @region computability.config
-- @provenance definition
/-- A configuration: the current state (`none` once the machine has halted) and the tape. -/
structure Config (Q : Type) where
  state : Option Q
  tape : Tape
  deriving DecidableEq
-- @endregion

-- @region computability.step
-- @provenance definition
/-- One step of the machine `M`. A halted configuration stays where it is. -/
def step {Q : Type} (M : Machine Q) : Config Q → Config Q
  | ⟨none, t⟩ => ⟨none, t⟩
  | ⟨some q, t⟩ =>
      let (w, d, q') := M q t.head
      ⟨q', Tape.move d { t with head := w }⟩
-- @endregion

-- @region computability.run
-- @provenance definition
/-- Run `M` for `n` steps. (A run that has not halted after `n` steps may halt later — or
never: no bound on `n` can tell the two apart in general. That is the halting problem.) -/
def run {Q : Type} (M : Machine Q) : Nat → Config Q → Config Q
  | 0, c => c
  | n + 1, c => run M n (step M c)
-- @endregion

-- @region computability.incr
-- @provenance definition
/-- A one-state binary incrementer. The head starts on the least significant bit, with more
significant bits to its left. Reading `1`: write `0` and carry left. Reading `0` (or a blank):
write `1` and halt. -/
def incr : Machine Unit
  | (), true => (false, .left, some ())
  | (), false => (true, .left, none)
-- @endregion

-- @region computability.incr_eleven
-- @provenance independent
/-- The incrementer turns `1011` (eleven) into `1100` (twelve) in three steps, checked by
evaluation. The tape then reads `1 1 0 0` from left to right, with the head on its first cell. -/
theorem incr_eleven :
    run incr 3 ⟨some (), ⟨[true, false, true], true, []⟩⟩ =
      ⟨none, ⟨[], true, [true, false, false]⟩⟩ := by
  decide
-- @endregion

-- @region computability.bb2
-- @provenance definition
/-- The two-state busy beaver (states `false` = A, `true` = B):
A0 → 1RB, A1 → 1LB, B0 → 1LA, B1 → 1R(halt). -/
def bb2 : Machine Bool
  | false, false => (true, .right, some true)
  | false, true => (true, .left, some true)
  | true, false => (true, .left, some false)
  | true, true => (true, .right, none)
-- @endregion

-- @region computability.bb2_run
-- @provenance independent
/-- Started in state A on a blank tape, `bb2` is still running after 5 steps, halts at step 6,
and leaves four `1`s: the values `S(2) = 6` and `Σ(2) = 4` of Radó's busy-beaver functions are
attained by this machine. (That no two-state machine does better needs a proof that every other
two-state machine either halts sooner or never halts; that is not formalised here.) -/
theorem bb2_run :
    (run bb2 5 ⟨some false, ⟨[], false, []⟩⟩).state ≠ none ∧
      (run bb2 6 ⟨some false, ⟨[], false, []⟩⟩).state = none ∧
      (run bb2 6 ⟨some false, ⟨[], false, []⟩⟩).tape.ones = 4 := by
  decide
-- @endregion

/-! ### Diagonal arguments -/

-- @region computability.no_halting_decider
-- @provenance independent
/-- **The diagonal argument behind the halting problem**, for any notion of program.
Let `Halts p q` mean "program `p` halts on input `q`", and let `d` be any proposed decider.
If programs are flexible enough to build the *diagonal program* `e`, which on input `q` halts
exactly when `d` says "`q` does not halt on `q`", then `d` is wrong somewhere: feeding `e` to
itself, `e` halts on `e` iff `d e e = false`, while correctness would demand `d e e = true`. -/
theorem no_halting_decider {P : Type*} (Halts : P → P → Prop) (d : P → P → Bool)
    (diag : ∃ e : P, ∀ q, Halts e q ↔ d q q = false) :
    ¬ ∀ p q, Halts p q ↔ d p q = true := by
  intro hd
  obtain ⟨e, he⟩ := diag
  have h1 : Halts e e ↔ d e e = false := he e
  have h2 : Halts e e ↔ d e e = true := hd e e
  cases hde : d e e
  · -- `d e e = false`: then `e` halts on `e`, so correctness forces `d e e = true`.
    exact Bool.false_ne_true (hde ▸ h2.1 (h1.2 hde))
  · -- `d e e = true`: then `e` halts on `e`, so the diagonal property forces `d e e = false`.
    exact Bool.false_ne_true (hde ▸ (h1.1 (h2.2 hde)).symm)
-- @endregion

-- @region computability.cantor_diag
-- @provenance independent
/-- **Cantor's diagonal argument.** No sequence `e 0, e 1, e 2, …` of functions `ℕ → ℕ`
contains every function: `f n = e n n + 1` differs from `e n` at the input `n`. -/
theorem cantor_diag (e : ℕ → ℕ → ℕ) : ¬ Function.Surjective e := by
  intro he
  obtain ⟨k, hk⟩ := he (fun n => e n n + 1)
  have : e k k = e k k + 1 := congrFun hk k
  omega
-- @endregion

-- @region computability.exists_not_computable
-- @provenance independent
/-- **Most functions are not computable.** Every computable `f : ℕ → ℕ` is evaluated by some
program (`Nat.Partrec.Code.exists_code`), different functions need different programs, and there
are only countably many programs. So if every function were computable, `ℕ → ℕ` would be
countable and could be listed as a sequence — contradicting `cantor_diag`. -/
theorem exists_not_computable : ∃ f : ℕ → ℕ, ¬ Computable f := by
  by_contra hall
  push Not at hall
  -- Choose a program for every function.
  have hcode : ∀ f : ℕ → ℕ, ∃ c : Code, c.eval = (f : ℕ →. ℕ) := fun f =>
    Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 (hall f))
  choose code hcode using hcode
  -- Different functions get different programs.
  have hinj : Function.Injective code := by
    intro f g hfg
    funext n
    have h : ((f : ℕ →. ℕ) n) = ((g : ℕ →. ℕ) n) := by
      rw [← hcode f, ← hcode g, hfg]
    exact Part.some_injective h
  -- So `ℕ → ℕ` is countable, hence listed by a sequence, contradicting the diagonal argument.
  have : Countable (ℕ → ℕ) := hinj.countable
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ → ℕ)
  exact cantor_diag e he
-- @endregion

/-! ### The halting problem and Rice's theorem in Mathlib -/

-- @region computability.halting_problem
-- @provenance library
/-- **The halting problem is undecidable** (Turing 1936): for any fixed input `n`, no computable
predicate decides, for every program `c`, whether `c` halts on `n`. This applies Mathlib's
`ComputablePred.halting_problem`. -/
theorem halting_problem (n : ℕ) : ¬ ComputablePred fun c : Code => (c.eval n).Dom :=
  ComputablePred.halting_problem n
-- @endregion

-- @region computability.halting_re
-- @provenance library
/-- The halting set *is* recursively enumerable: run the program and say "yes" if it stops.
This applies Mathlib's `ComputablePred.halting_problem_re`. -/
theorem halting_re (n : ℕ) : REPred fun c : Code => (c.eval n).Dom :=
  ComputablePred.halting_problem_re n
-- @endregion

-- @region computability.post
-- @provenance library
/-- **Post's theorem**: a predicate is decidable if and only if both it and its negation are
recursively enumerable. This applies Mathlib's `ComputablePred.computable_iff_re_compl_re'`. -/
theorem post {α : Type*} [Primcodable α] (p : α → Prop) :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬ p a :=
  ComputablePred.computable_iff_re_compl_re'
-- @endregion

-- @region computability.non_halting_not_re
-- @provenance independent
/-- The set of programs that do **not** halt on `n` is not even recursively enumerable:
if it were, the halting set would be decidable by Post's theorem. -/
theorem non_halting_not_re (n : ℕ) : ¬ REPred fun c : Code => ¬ (c.eval n).Dom := by
  intro h
  exact halting_problem n ((post _).2 ⟨halting_re n, h⟩)
-- @endregion

-- @region computability.undecidable_of_reduces
-- @provenance independent
/-- **Reductions transfer undecidability.** If `p` many-one reduces to `q` (a computable `f`
with `p a ↔ q (f a)`) and `p` is undecidable, then so is `q`: a decider for `q`, composed with
`f`, would decide `p`. The composition step is Mathlib's
`ComputablePred.computable_of_manyOneReducible`. -/
theorem undecidable_of_reduces {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop} (hpq : ManyOneReducible p q) (hp : ¬ ComputablePred p) :
    ¬ ComputablePred q := fun hq =>
  hp (ComputablePred.computable_of_manyOneReducible hpq hq)
-- @endregion

-- @region computability.rice
-- @provenance library
/-- **Rice's theorem** (1953): a property of programs that depends only on the partial function
a program computes is decidable only if it is trivial — true of no program or of every program.
This applies Mathlib's `ComputablePred.rice₂`. -/
theorem rice (C : Set Code) (H : ∀ cf cg : Code, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ :=
  ComputablePred.rice₂ C H
-- @endregion

-- @region computability.zero_function_undecidable
-- @provenance independent
/-- **No algorithm decides whether a program computes the constant function `0`.**
The property depends only on the function computed, and it is non-trivial: the program
`Code.const 0` has it, and a program that never halts does not. Rice's theorem finishes. -/
theorem zero_function_undecidable :
    ¬ ComputablePred fun c : Code => c.eval = fun _ => Part.some 0 := by
  intro h
  -- A program that diverges on every input.
  obtain ⟨cnone, hnone⟩ := Nat.Partrec.Code.exists_code.1 Nat.Partrec.none
  have hC := (rice {c : Code | c.eval = fun _ => Part.some 0}
    (fun cf cg hfg => by
      change cf.eval = _ ↔ cg.eval = _
      rw [hfg])).1 h
  rcases hC with hempty | huniv
  · -- `Code.const 0` computes the zero function, so the set is not empty.
    have hmem : Code.const 0 ∈ {c : Code | c.eval = fun _ => Part.some 0} := by
      show (Code.const 0).eval = fun _ => Part.some 0
      funext m
      exact Nat.Partrec.Code.eval_const 0 m
    rw [hempty] at hmem
    exact hmem
  · -- The diverging program does not, so the set is not everything.
    have hmem : cnone ∈ {c : Code | c.eval = fun _ => Part.some 0} := by
      rw [huniv]
      exact Set.mem_univ _
    have h0 : (Part.none : Part ℕ) = Part.some 0 := by
      have := congrFun hmem 0
      rw [hnone] at this
      exact this
    exact Part.some_ne_none 0 h0.symm
-- @endregion

end Lumenary.Computability
