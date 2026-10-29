/-
The Lumenary — formal mathematics
First steps in Lean: propositions and proofs, rewriting, induction, reading Mathlib, and what a
machine check does and does not guarantee.

Proved here (`@provenance independent`): small facts checked by computation (`rfl`); `p ∧ q → q ∧ p`
twice (as a term and with tactics), modus ponens, chaining implications, `p ∨ q → q ∨ p` and the
contrapositive; two rewriting examples; `n + 0 = n` by definition and `0 + n = n` by induction;
the formula `2 · (0 + 1 + ⋯ + n) = n(n + 1)` by induction; that no natural number squares to 2
(a correct proof of a statement that is *weaker* than "√2 is irrational"); and some facts about
Lean's conventions that a reader of formal statements must know: natural-number subtraction
stops at 0, natural-number division rounds down, and a hypothesis that can never hold proves
anything.

From the library (`@provenance library`): core Lean's `Nat.zero_add` and
`Classical.byContradiction` (double negation elimination, a classical principle), Mathlib's
`Nat.exists_infinite_primes`, `irrational_sqrt_two` and `div_zero`, and Mathlib's `norm_num`
extension that certifies that 97 is prime.
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace Lumenary.IntroLean

/-! ### Proofs by computation -/

-- @region intro_lean.two_add_two
-- @provenance independent
/-- `2 + 2 = 4`. The proof `rfl` ("reflexivity") asks Lean to compute both sides; they are the
same natural number, so the proof is accepted. -/
theorem two_add_two : 2 + 2 = 4 := rfl
-- @endregion

/-! ### Propositions are types, proofs are terms -/

-- @region intro_lean.and_swap
-- @provenance independent
/-- If `p` and `q` are both true, then `q` and `p` are both true. As a **term**: a proof of
`p ∧ q → q ∧ p` is a function that takes a proof of `p ∧ q` — a pair `⟨hp, hq⟩` — and
returns a proof of `q ∧ p`, the pair `⟨hq, hp⟩`. -/
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩
-- @endregion

-- @region intro_lean.and_swap_tactics
-- @provenance independent
/-- The same theorem proved with **tactics**, commands that build the proof step by step.
`intro` assumes the hypothesis, `obtain` splits the pair, `constructor` splits the goal
`q ∧ p` into two goals, and `exact` closes each one. -/
theorem and_swap_tactics (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  constructor
  · exact hq
  · exact hp
-- @endregion

-- @region intro_lean.modus_ponens
-- @provenance independent
/-- **Modus ponens**: from `p → q` and `p`, conclude `q`. A proof of `p → q` *is* a function
from proofs of `p` to proofs of `q`, so we just apply it to `hp`. -/
theorem modus_ponens (p q : Prop) (hpq : p → q) (hp : p) : q :=
  hpq hp
-- @endregion

-- @region intro_lean.imp_trans
-- @provenance independent
/-- Implications chain: from `p → q` and `q → r`, conclude `p → r`. The proof is the
composite of the two functions. -/
theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  fun hp => hqr (hpq hp)
-- @endregion

-- @region intro_lean.or_swap
-- @provenance independent
/-- `p ∨ q → q ∨ p`, by **cases**: a proof of `p ∨ q` is either a proof of `p` (`inl`) or a
proof of `q` (`inr`), and we handle each case. -/
theorem or_swap (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq
-- @endregion

-- @region intro_lean.contrapositive
-- @provenance independent
/-- The **contrapositive**: from `p → q`, conclude `¬q → ¬p`. In Lean `¬q` means `q → False`,
so given `hnq : ¬q` and `hp : p` we produce `False` as `hnq (hpq hp)`. -/
theorem contrapositive (p q : Prop) (hpq : p → q) : ¬q → ¬p :=
  fun hnq hp => hnq (hpq hp)
-- @endregion

-- @region intro_lean.double_negation
-- @provenance library
/-- **Double negation elimination**, `¬¬p → p`, is a truth-table tautology, but it cannot be
proved from the constructive rules used above. Lean proves it with the classical principle
`Classical.byContradiction` (which rests on the axiom of choice), and `#print axioms` reports
this: compare its axiom list with that of `contrapositive`. -/
theorem double_negation (p : Prop) (h : ¬¬p) : p :=
  Classical.byContradiction h
-- @endregion

/-! ### Rewriting -/

-- @region intro_lean.rw_chain
-- @provenance independent
/-- **Rewriting** with equations: `rw [h₁]` replaces `a` by `b` in the goal `a = c`, giving
`b = c`; `rw [h₂]` turns it into `c = c`, which `rw` closes automatically. -/
theorem rw_chain (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁, h₂]
-- @endregion

-- @region intro_lean.rw_library
-- @provenance independent
/-- Rewriting with **library lemmas**: `Nat.add_comm a b : a + b = b + a` and
`Nat.mul_comm`. After both rewrites the two sides are identical. -/
theorem rw_library (a b : ℕ) : (a + b) * 2 = 2 * (b + a) := by
  rw [Nat.add_comm a b, Nat.mul_comm]
-- @endregion

-- @region intro_lean.simp_example
-- @provenance independent
/-- `simp` rewrites with a large collection of simplification lemmas (`x + 0 = x`,
`x * 1 = x`, `x * 0 = 0`, …) until nothing more applies. -/
theorem simp_example (a b : ℕ) : (a + 0) * 1 + b * 0 = a := by
  simp
-- @endregion

/-! ### Natural numbers and induction -/

-- @region intro_lean.add_zero_rfl
-- @provenance independent
/-- `n + 0 = n` holds **by definition**: Lean defines addition by recursion on the second
argument, with `n + 0 = n` as the first rule. So `rfl` works, for every `n`. -/
theorem add_zero_rfl (n : ℕ) : n + 0 = n := rfl
-- @endregion

-- @region intro_lean.zero_add_induction
-- @provenance independent
/-- `0 + n = n` is **not** true by definition (the recursion is on the second argument, here
the unknown `n`), so `rfl` fails and we prove it by **induction** on `n`:
* `n = 0`: `0 + 0 = 0` holds by definition;
* `n = k + 1`: `0 + (k + 1) = (0 + k) + 1` by the second rule of addition (`Nat.add_succ`),
  `= k + 1` by the induction hypothesis `ih : 0 + k = k`. -/
theorem zero_add_induction (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
-- @endregion

-- @region intro_lean.zero_add_library
-- @provenance library
/-- The same fact, obtained by *applying* core Lean's theorem `Nat.zero_add`. Both versions are
machine-checked; only the previous one proves it here from the definition. -/
theorem zero_add_library (n : ℕ) : 0 + n = n :=
  Nat.zero_add n
-- @endregion

-- @region intro_lean.sum_up_to
-- @provenance definition
/-- `sumUpTo n = 0 + 1 + 2 + ⋯ + n`, defined by recursion. -/
def sumUpTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumUpTo n + (n + 1)
-- @endregion

-- @region intro_lean.two_mul_sum_up_to
-- @provenance independent
/-- **Gauss's formula** `2 · (0 + 1 + ⋯ + n) = n(n + 1)`, by induction. In the step, unfold
`sumUpTo (k + 1) = sumUpTo k + (k + 1)`, distribute, use the induction hypothesis, and let
`ring` finish the algebra `k(k + 1) + 2(k + 1) = (k + 1)(k + 2)`. -/
theorem two_mul_sumUpTo (n : ℕ) : 2 * sumUpTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumUpTo, Nat.mul_add, ih]
    ring
-- @endregion

/-! ### Reading and using Mathlib -/

-- @region intro_lean.prime_97
-- @provenance library
/-- `97` is prime, certified by Mathlib's `norm_num` extension for primality (it checks that no
number from 2 up to √97 divides 97, and produces a proof term that Lean's kernel re-checks). -/
theorem prime_97 : Nat.Prime 97 := by
  norm_num
-- @endregion

-- @region intro_lean.infinitely_many_primes
-- @provenance library
/-- **Euclid's theorem**, read off Mathlib: for every `n` there is a prime `p` with `n ≤ p`.
This applies `Nat.exists_infinite_primes`, whose statement is exactly this. -/
theorem infinitely_many_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n
-- @endregion

-- @region intro_lean.sqrt_two_irrational
-- @provenance library
/-- `√2` is irrational: Mathlib's `irrational_sqrt_two`. Here `Irrational x` means that `x`
is not equal to any rational number. -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two
-- @endregion

/-! ### What a machine check does *not* guarantee -/

-- @region intro_lean.no_nat_sqrt_two
-- @provenance independent
/-- **A correct proof of a weaker statement.** No *natural number* squares to 2: if `q ≤ 1`
then `q · q ≤ 1`, and if `q ≥ 2` then `q · q ≥ 4`. Lean checks this proof perfectly — but
the statement does **not** say that `√2` is irrational (it says nothing about fractions).
A formal proof is only as meaningful as its formal statement. -/
theorem no_nat_sqrt_two : ¬ ∃ q : ℕ, q * q = 2 := by
  rintro ⟨q, hq⟩
  rcases Nat.lt_or_ge q 2 with h | h
  · have h1 : q * q ≤ 1 * 1 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · have h4 : 2 * 2 ≤ q * q := Nat.mul_le_mul h h
    omega
-- @endregion

-- @region intro_lean.nat_sub_truncates
-- @provenance independent
/-- In Lean, subtraction of natural numbers **stops at zero**: `3 - 5 = 0`, because there is no
natural number `-2`. A statement such as `∀ n : ℕ, n - 1 + 1 = n` is therefore *false* (it
fails at `n = 0`). -/
theorem nat_sub_truncates : (3 : ℕ) - 5 = 0 := rfl
-- @endregion

-- @region intro_lean.nat_div_rounds_down
-- @provenance independent
/-- Division of natural numbers **rounds down**: `7 / 2 = 3`. -/
theorem nat_div_rounds_down : (7 : ℕ) / 2 = 3 := rfl
-- @endregion

-- @region intro_lean.real_div_zero
-- @provenance library
/-- In Mathlib, `x / 0 = 0` for real numbers — a convention that makes division a total
function. So `1 / 0 = 0` is a theorem (`div_zero`), and a statement like "`x / x = 1`" needs
the hypothesis `x ≠ 0` to be true. -/
theorem real_div_zero : (1 : ℝ) / 0 = 0 :=
  div_zero 1
-- @endregion

-- @region intro_lean.vacuous
-- @provenance independent
/-- **A vacuous theorem.** If `n + 1 = 0` then `n = 37`. The hypothesis can never hold (a
successor is never zero), so the theorem is true — and useless. Impossible hypotheses make
anything provable; always check that a formal statement's hypotheses can actually happen. -/
theorem vacuous (n : ℕ) (h : n + 1 = 0) : n = 37 :=
  absurd h (Nat.succ_ne_zero n)
-- @endregion

end Lumenary.IntroLean
