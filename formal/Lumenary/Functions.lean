/-
The Lumenary — formal mathematics
Functions: injective ("one-to-one"), surjective ("onto") and bijective functions, with
examples and non-examples on the integers, plus the set-theoretic view of a function as its
graph.

Core Lean 4 already defines `Function.Injective` and `Function.Surjective`, and we use those:
  `Injective f  :=  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`
  `Surjective f :=  ∀ b, ∃ a, f a = b`
Core has no `Bijective`, so we define it below exactly as Mathlib does
(Mathlib analogue: `Function.Bijective`).
-/
import Lumenary.Integers

namespace Lumenary.Functions

open Function

universe u v

variable {α : Type u} {β : Type v}

-- @region functions.bijective
-- @provenance definition
/-- A function is **bijective** when it is both injective and surjective: every element of
the target is hit by exactly one input. -/
def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f
-- @endregion

/-! ### Examples and non-examples -/

-- @region functions.injective_two_mul_add_one
-- @provenance independent
/-- `n ↦ 2n + 1` is injective: if `2a + 1 = 2b + 1`, subtract 1 and divide by 2. -/
theorem injective_two_mul_add_one : Injective (fun n : Int => 2 * n + 1) := by
  intro a b h
  -- `h : 2 * a + 1 = 2 * b + 1`
  have h1 : 2 * a = 2 * b := (Int.add_left_inj 1).mp h      -- subtract 1
  exact Int.eq_of_mul_eq_mul_left (by decide) h1           -- divide by 2 (and 2 ≠ 0)
-- @endregion

-- @region functions.not_injective_square
-- @provenance independent
/-- `n ↦ n²` is **not** injective on the integers: `1² = (-1)²` but `1 ≠ -1`. -/
theorem not_injective_square : ¬ Injective (fun n : Int => n * n) := by
  intro h
  have h1 : (1 : Int) = -1 := h (by decide)   -- the hypothesis needed is `1 * 1 = -1 * -1`
  exact absurd h1 (by decide)
-- @endregion

-- @region functions.surjective_add_one
-- @provenance independent
/-- `n ↦ n + 1` is surjective on the integers: to hit `y`, start from `y - 1`. -/
theorem surjective_add_one : Surjective (fun n : Int => n + 1) := by
  intro y
  exact ⟨y - 1, Int.sub_add_cancel y 1⟩
-- @endregion

-- @region functions.not_surjective_two_mul
-- @provenance independent
/-- `n ↦ 2n` is **not** surjective on the integers: nothing is sent to `1`, because there is
no integer half (`Lumenary.Integers.no_int_half`). -/
theorem not_surjective_two_mul : ¬ Surjective (fun n : Int => 2 * n) := by
  intro h
  obtain ⟨x, hx⟩ := h 1          -- `hx : 2 * x = 1`
  exact Lumenary.Integers.no_int_half ⟨x, hx⟩
-- @endregion

-- @region functions.bijective_neg
-- @provenance independent
/-- Negation `n ↦ -n` is a bijection of the integers (it is its own inverse). -/
theorem bijective_neg : Bijective (fun n : Int => -n) := by
  constructor
  · -- Injective: from `-a = -b`, negate both sides.
    intro a b h
    exact Int.neg_inj.mp h
  · -- Surjective: `-(-y) = y`.
    intro y
    exact ⟨-y, Int.neg_neg y⟩
-- @endregion

/-! ### The set-theoretic view: a function is its graph -/

-- @region functions.graph
-- @provenance definition
/-- The **graph** of `f`: the set of pairs `(a, b)` with `f a = b`, written as a predicate on
pairs (in `Lumenary.Sets` this is a `Set (α × β)`). In set theory a function *is* such a set
of pairs. -/
def graph (f : α → β) : α × β → Prop := fun p => f p.1 = p.2
-- @endregion

-- @region functions.graph_functional
-- @provenance independent
/-- A graph is **functional**: each input `a` is paired with `f a`, and with nothing else. -/
theorem graph_functional (f : α → β) (a : α) :
    graph f (a, f a) ∧ ∀ b, graph f (a, b) → b = f a := by
  constructor
  · -- `graph f (a, f a)` says `f a = f a`.
    rfl
  · intro b h
    -- `h : f a = b`
    exact Eq.symm h
-- @endregion

end Lumenary.Functions
