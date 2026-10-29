/-
The Lumenary — formal mathematics
Programming for mathematics: loops, recursion, testing versus proving, and binary numbers.

Lean is a programming language as well as a proof checker: a `def` is a program that Lean can
run, and a `theorem` can state a fact about what that program computes for *every* input. This
module writes the lesson's programs in Lean — a `for` loop with a running total that looks almost
exactly like the Python version, a recursive sum, and conversion to and from binary — and then
proves what testing alone cannot: the formula `1 + 2 + ⋯ + n = n(n + 1)/2` for every `n`, that the
sum of the first `n` odd numbers is `n²`, that the binary conversion is correct for every number,
and that binary representations without leading zeros are unique.

Lean's floating-point type `Float` behaves like Python's (`0.1 + 0.2 == 0.3` evaluates to
`false`), but its arithmetic is carried out by the computer's hardware, so Lean cannot reason about
it inside proofs; exact fractions (`Rat`) can be. Core Lean only.
-/

namespace Lumenary.ProgrammingIntro

/-! ### A loop, and the same sum written recursively -/

-- @region programming_intro.sum_for
-- @provenance definition
/-- The sum `1 + 2 + ⋯ + n`, computed by a loop with a running total — the Lean version of the
Python program
```
total = 0
for i in range(1, n + 1):
    total = total + i
```
Here `total := total + i` is an **assignment**: replace the stored value of `total`. -/
def sumFor (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [1:n+1] do
    total := total + i
  return total
-- @endregion

-- @region programming_intro.sum_for_examples
-- @provenance independent
/-- Running the loop: `1 + ⋯ + 10 = 55` and `1 + ⋯ + 100 = 5050`. (`decide +kernel` asks Lean's
trusted kernel to run the program and compare the answers.) -/
theorem sum_for_examples : sumFor 10 = 55 ∧ sumFor 100 = 5050 := by
  decide +kernel
-- @endregion

-- @region programming_intro.assignment_example
-- @provenance independent
/-- Assignment is not equality. The program "`x := 5`, then `x := x + 1`" ends with `x = 6`… -/
theorem assignment_example :
    (Id.run do
      let mut x := 5
      x := x + 1
      return x) = 6 := by
  rfl
-- @endregion

-- @region programming_intro.no_solution_x_eq_x_add_one
-- @provenance independent
/-- … but as an *equation*, `x = x + 1` has no solution at all. -/
theorem no_solution_x_eq_x_add_one : ¬ ∃ x : Nat, x = x + 1 := by
  intro ⟨x, hx⟩
  omega
-- @endregion

-- @region programming_intro.sum_to
-- @provenance definition
/-- The same sum, defined **recursively**: the sum up to `0` is `0`, and the sum up to `n + 1` is
the sum up to `n`, plus `n + 1`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)
-- @endregion

-- @region programming_intro.loop_agrees_tested
-- @provenance independent
/-- **Testing**: the loop and the recursive definition agree for each of the 40 inputs
`n = 0, 1, …, 39`. Lean checks this by running both programs on every one of these inputs. It
says nothing about `n = 40` or beyond. -/
theorem loop_agrees_tested : ∀ n, n < 40 → sumFor n = sumTo n := by
  decide +kernel
-- @endregion

-- @region programming_intro.gauss_formula
-- @provenance independent
/-- **Proof for every `n`**: `2 · (1 + 2 + ⋯ + n) = n(n + 1)`, by induction. It holds for `n = 0`;
and if it holds for `n`, then `2 · sumTo (n + 1) = 2 · sumTo n + 2(n + 1) = n(n + 1) + 2(n + 1)
= (n + 1)(n + 2)`. -/
theorem gauss_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc 2 * sumTo (k + 1) = 2 * sumTo k + 2 * (k + 1) := by
          rw [sumTo, Nat.mul_add]
      _ = k * (k + 1) + 2 * (k + 1) := by rw [ih]
      _ = (k + 1) * (k + 1 + 1) := by
          rw [← Nat.add_mul, Nat.mul_comm, Nat.add_comm k 2, Nat.add_comm 2 k]
-- @endregion

/-! ### A loop with an accumulator, proved correct -/

-- @region programming_intro.sum_acc
-- @provenance definition
/-- A loop written as a function with an **accumulator** `acc` (the running total): it adds
`n, n − 1, …, 1` to `acc`, one number per step. -/
def sumAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))
-- @endregion

-- @region programming_intro.sum_acc_correct
-- @provenance independent
/-- The accumulator loop is correct for **every** input: starting from any running total `acc`, it
ends with `acc + (1 + ⋯ + n)`. Proved by induction on `n`, for all `acc` at once. -/
theorem sum_acc_correct (n acc : Nat) : sumAcc n acc = acc + sumTo n := by
  induction n generalizing acc with
  | zero => rfl
  | succ k ih =>
    show sumAcc k (acc + (k + 1)) = acc + (sumTo k + (k + 1))
    rw [ih]
    omega
-- @endregion

/-! ### Odd numbers -/

-- @region programming_intro.sum_odds
-- @provenance definition
/-- The sum of the first `n` odd numbers, `1 + 3 + 5 + ⋯ + (2n − 1)`. -/
def sumOdds : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdds n + (2 * n + 1)
-- @endregion

-- @region programming_intro.sum_odds_eq_square
-- @provenance independent
/-- The sum of the first `n` odd numbers is `n²` — for every `n`, by induction:
`n² + (2n + 1) = (n + 1)²`. -/
theorem sum_odds_eq_square (n : Nat) : sumOdds n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumOdds k + (2 * k + 1) = (k + 1) * (k + 1)
    rw [ih, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
-- @endregion

/-! ### Binary numbers -/

-- @region programming_intro.from_binary
-- @provenance definition
/-- The value of a list of binary digits, **least significant digit first**: `[1, 0, 1, 1]` means
`1·1 + 0·2 + 1·4 + 1·8 = 13`. Each step: value of `d :: ds` is `d + 2 · (value of ds)`. -/
def fromBinary : List Nat → Nat
  | [] => 0
  | d :: ds => d + 2 * fromBinary ds
-- @endregion

-- @region programming_intro.bits_aux
-- @provenance definition
/-- Repeated division by `2`: the remainder is the next binary digit, and we continue with the
quotient. (The extra argument `fuel` limits the number of steps, which makes it easy for Lean to
see that the program stops; `n` steps are always enough.) -/
def bitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else (n % 2) :: bitsAux fuel (n / 2)
-- @endregion

-- @region programming_intro.to_binary
-- @provenance definition
/-- The binary digits of `n`, least significant first; `toBinary 0` is the empty list. -/
def toBinary (n : Nat) : List Nat := bitsAux n n
-- @endregion

-- @region programming_intro.binary_examples
-- @provenance independent
/-- Examples, computed by running the programs: `13 = 1101₂` (digits `[1, 0, 1, 1]` from the
right), `45 = 101101₂`, and back again. -/
theorem binary_examples :
    toBinary 13 = [1, 0, 1, 1] ∧ toBinary 45 = [1, 0, 1, 1, 0, 1] ∧
      fromBinary [1, 0, 1, 1, 0, 1] = 45 := by
  decide
-- @endregion

-- @region programming_intro.from_bits_aux
-- @provenance independent
/-- The heart of the correctness proof: if `n ≤ fuel`, the digits produced by repeated division
have value `n`. Induction on `fuel`: for `n > 0` the digits are `n % 2` followed by the digits of
`n / 2`, and `n % 2 + 2 · (n / 2) = n`. -/
theorem from_bits_aux : ∀ fuel n, n ≤ fuel → fromBinary (bitsAux fuel n) = n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    show 0 = n
    omega
  | succ k ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      rfl
    · show fromBinary (if n = 0 then [] else (n % 2) :: bitsAux k (n / 2)) = n
      split
      · contradiction
      · show n % 2 + 2 * fromBinary (bitsAux k (n / 2)) = n
        rw [ih (n / 2) (by omega)]
        omega
-- @endregion

-- @region programming_intro.from_to_binary
-- @provenance independent
/-- **The conversion to binary is correct for every natural number**: the digits that `toBinary`
produces have value `n`. -/
theorem from_to_binary (n : Nat) : fromBinary (toBinary n) = n :=
  from_bits_aux n n (Nat.le_refl n)
-- @endregion

-- @region programming_intro.all_bits
-- @provenance definition
/-- Every entry of the list is a binary digit, `0` or `1`. -/
def AllBits : List Nat → Prop
  | [] => True
  | d :: ds => d < 2 ∧ AllBits ds
-- @endregion

-- @region programming_intro.no_leading_zero
-- @provenance definition
/-- No leading zeros: the most significant digit (the **last** entry, since we store the least
significant digit first) is not `0`. The empty list, which represents `0`, counts as fine. -/
def NoLeadingZero : List Nat → Prop
  | [] => True
  | [d] => d ≠ 0
  | _ :: d :: ds => NoLeadingZero (d :: ds)
-- @endregion

-- @region programming_intro.value_ne_zero
-- @provenance independent
/-- A non-empty digit list without leading zeros has a non-zero value. -/
theorem value_ne_zero : ∀ (d : Nat) (ds : List Nat), NoLeadingZero (d :: ds) →
    fromBinary (d :: ds) ≠ 0
  | d, [], h => by
    show d + 2 * 0 ≠ 0
    have : d ≠ 0 := h
    omega
  | d, e :: es, h => by
    have ih := value_ne_zero e es h
    show d + 2 * fromBinary (e :: es) ≠ 0
    omega
-- @endregion

-- @region programming_intro.binary_exists
-- @provenance independent
/-- **Existence**: every natural number has a binary representation without leading zeros.
(Proved by induction, following the repeated-division algorithm: write `n = 2q + r` with
`r = n % 2`, represent `q`, and put `r` in front.) -/
theorem binary_exists : ∀ n, ∃ l, AllBits l ∧ NoLeadingZero l ∧ fromBinary l = n := by
  -- Induction on a bound `b` for `n`, so that we may use the statement for `n / 2`.
  have key : ∀ b n, n ≤ b → ∃ l, AllBits l ∧ NoLeadingZero l ∧ fromBinary l = n := by
    intro b
    induction b with
    | zero =>
      intro n hn
      exact ⟨[], trivial, trivial, by show 0 = n; omega⟩
    | succ k ih =>
      intro n hn
      by_cases h0 : n = 0
      · exact ⟨[], trivial, trivial, by show 0 = n; omega⟩
      · obtain ⟨l, hbits, hlead, hval⟩ := ih (n / 2) (by omega)
        refine ⟨(n % 2) :: l, ⟨Nat.mod_lt n (by decide), hbits⟩, ?_, ?_⟩
        · cases l with
          | nil =>
            -- Then `n / 2 = 0`, so `n = 1` and the single digit is `1`.
            have hq : n / 2 = 0 := by rw [← hval]; rfl
            show n % 2 ≠ 0
            omega
          | cons e es => exact hlead
        · show n % 2 + 2 * fromBinary l = n
          rw [hval]
          omega
  intro n
  exact key n n (Nat.le_refl n)
-- @endregion

-- @region programming_intro.binary_unique
-- @provenance independent
/-- **Uniqueness**: two binary representations without leading zeros that have the same value are
the same list. The last digit is forced (it is the remainder on division by `2`); remove it, and
the rest represent the same smaller number — so by induction they agree too. -/
theorem binary_unique : ∀ l₁ l₂ : List Nat, AllBits l₁ → AllBits l₂ →
    NoLeadingZero l₁ → NoLeadingZero l₂ → fromBinary l₁ = fromBinary l₂ → l₁ = l₂
  | [], [], _, _, _, _, _ => rfl
  | [], e :: es, _, _, _, h₂, hv => absurd hv.symm (value_ne_zero e es h₂)
  | d :: ds, [], _, _, h₁, _, hv => absurd hv (value_ne_zero d ds h₁)
  | d :: ds, e :: es, ⟨hd, hds⟩, ⟨he, hes⟩, h₁, h₂, hv => by
    have hv' : d + 2 * fromBinary ds = e + 2 * fromBinary es := hv
    have hde : d = e := by omega
    have hrest : fromBinary ds = fromBinary es := by omega
    have hlead₁ : NoLeadingZero ds := by
      cases ds with
      | nil => trivial
      | cons _ _ => exact h₁
    have hlead₂ : NoLeadingZero es := by
      cases es with
      | nil => trivial
      | cons _ _ => exact h₂
    rw [hde, binary_unique ds es hds hes hlead₁ hlead₂ hrest]
-- @endregion

/-! ### Exact fractions -/

-- @region programming_intro.exact_tenths
-- @provenance independent
/-- With exact fractions, one tenth plus two tenths **is** three tenths. (Python's `Fraction` and
Lean's `Rat` both store numerator and denominator exactly; floating-point numbers do not.) -/
theorem exact_tenths : (1 / 10 + 2 / 10 : Rat) = 3 / 10 := by
  decide +kernel
-- @endregion

end Lumenary.ProgrammingIntro
