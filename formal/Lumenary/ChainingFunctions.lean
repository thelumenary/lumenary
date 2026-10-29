/-
The Lumenary — formal mathematics
Function machines in sequence: chaining functions, the identity function, and undoing.

"Do `f`, then `g`" is the function `a ↦ g (f a)`. Lean only accepts the chain when the output
type of `f` is the input type of `g` — the formal version of "every output of the first machine
must be an allowed input of the second". We call the chain `andThen f g`, so that it reads in
the order the machines run; Lean's library writes the same function as `g ∘ f` ("`g` after
`f`"), the notation of the next lesson on composition.

What is formalised: computing chains, that the order of a chain matters (and exactly when
"add `a`" and "multiply by `m`" can be swapped), that identity functions change nothing, what it
means for one function to undo another, the "socks and shoes" rule for undoing a chain (applied
to converting °C to °F and back), and that a function which can be undone never sends two inputs
to the same output — so `x ↦ x²` on ℤ cannot be undone. Core Lean only; fractions use core
Lean's `Rat`.
-/

namespace Lumenary.ChainingFunctions

/-! ### Chains -/

-- @region chaining_functions.and_then
-- @provenance definition
/-- "Do `f`, then `g`": the function that sends `a` to `g (f a)`. It can only be formed when the
outputs of `f` (of type `β`) are inputs that `g` accepts. -/
def andThen {α β γ : Type} (f : α → β) (g : β → γ) : α → γ := fun a => g (f a)
-- @endregion

-- @region chaining_functions.and_then_eq_comp
-- @provenance independent
/-- Our `andThen f g` is the function Lean's library writes `g ∘ f`, read "`g` after `f`".
They agree by definition, so `rfl` proves it. -/
theorem and_then_eq_comp {α β γ : Type} (f : α → β) (g : β → γ) : andThen f g = g ∘ f := rfl
-- @endregion

-- @region chaining_functions.add_then_double
-- @provenance independent
/-- "Add 3, then double" sends `x` to `2(x + 3) = 2x + 6`. -/
theorem add_then_double (x : Int) : andThen (fun n => n + 3) (fun n => 2 * n) x = 2 * x + 6 := by
  show 2 * (x + 3) = 2 * x + 6
  omega
-- @endregion

-- @region chaining_functions.double_then_add
-- @provenance independent
/-- "Double, then add 3" sends `x` to `2x + 3`. -/
theorem double_then_add (x : Int) : andThen (fun n => 2 * n) (fun n => n + 3) x = 2 * x + 3 := by
  show 2 * x + 3 = 2 * x + 3
  rfl
-- @endregion

-- @region chaining_functions.order_matters
-- @provenance independent
/-- **Order matters**: "add 3, then double" and "double, then add 3" are different functions.
One input is enough to tell them apart: at `0` they give `6` and `3`. -/
theorem order_matters :
    andThen (fun n : Int => n + 3) (fun n => 2 * n) ≠ andThen (fun n : Int => 2 * n) (fun n => n + 3) := by
  intro h
  have h0 := congrFun h 0
  rw [add_then_double, double_then_add] at h0
  omega
-- @endregion

-- @region chaining_functions.add_mul_swap_iff
-- @provenance independent
/-- **When can "add `a`" and "multiply by `m`" be swapped?** "Add `a`, then multiply by `m`" gives
`m(x + a) = mx + ma`, while "multiply by `m`, then add `a`" gives `mx + a`. They agree for every
`x` exactly when `ma = a`, that is, when `a = 0` or `m = 1`. -/
theorem add_mul_swap_iff (a m : Int) :
    (∀ x, andThen (fun n => n + a) (fun n => m * n) x = andThen (fun n => m * n) (fun n => n + a) x)
      ↔ a = 0 ∨ m = 1 := by
  constructor
  · intro h
    -- At `x = 0` the two chains give `m · a` and `a`.
    have h0 : m * (0 + a) = m * 0 + a := h 0
    have hma : (m - 1) * a = 0 := by
      rw [Int.sub_mul, Int.one_mul]
      rw [Int.zero_add, Int.mul_zero, Int.zero_add] at h0
      omega
    cases Int.mul_eq_zero.mp hma with
    | inl hm => exact Or.inr (by omega)
    | inr ha => exact Or.inl ha
  · intro h x
    show m * (x + a) = m * x + a
    cases h with
    | inl ha => rw [ha, Int.add_zero, Int.add_zero]
    | inr hm => rw [hm, Int.one_mul, Int.one_mul]
-- @endregion

/-! ### The identity function -/

-- @region chaining_functions.id_and_then
-- @provenance independent
/-- Doing nothing first changes nothing: "identity, then `f`" is `f`. -/
theorem id_and_then {α β : Type} (f : α → β) : andThen id f = f := rfl
-- @endregion

-- @region chaining_functions.and_then_id
-- @provenance independent
/-- Doing nothing afterwards changes nothing: "`f`, then identity" is `f`. -/
theorem and_then_id {α β : Type} (f : α → β) : andThen f id = f := rfl
-- @endregion

/-! ### Undoing -/

-- @region chaining_functions.undoes
-- @provenance definition
/-- `g` **undoes** `f` if doing `f` and then `g` always gives back the input: `g (f a) = a`. -/
def Undoes {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ a, g (f a) = a
-- @endregion

-- @region chaining_functions.sub_undoes_add
-- @provenance independent
/-- "Subtract 3" undoes "add 3" … -/
theorem sub_undoes_add : Undoes (fun x : Int => x - 3) (fun x => x + 3) := by
  intro a
  show a + 3 - 3 = a
  omega
-- @endregion

-- @region chaining_functions.add_undoes_sub
-- @provenance independent
/-- … and "add 3" undoes "subtract 3". Each undoes the other: they are **inverse** functions. -/
theorem add_undoes_sub : Undoes (fun x : Int => x + 3) (fun x => x - 3) := by
  intro a
  show a - 3 + 3 = a
  omega
-- @endregion

-- @region chaining_functions.halve_undoes_double
-- @provenance independent
/-- On the rational numbers, "halve" undoes "double" and "double" undoes "halve": `x ↦ 2x` and
`x ↦ x / 2` are inverse functions of `ℚ`. -/
theorem halve_undoes_double :
    Undoes (fun x : Rat => x / 2) (fun x => 2 * x) ∧ Undoes (fun x : Rat => 2 * x) (fun x => x / 2) := by
  constructor
  · intro a
    show 2 * a / 2 = a
    grind
  · intro a
    show 2 * (a / 2) = a
    grind
-- @endregion

-- @region chaining_functions.int_halve_undoes_double
-- @provenance library
/-- On the integers, halving *with rounding down* (Lean's `y / 2`) still undoes doubling:
`(2x) / 2 = x`. This applies core Lean's `Int.mul_ediv_cancel_left`. -/
theorem int_halve_undoes_double : Undoes (fun y : Int => y / 2) (fun x => 2 * x) :=
  fun x => Int.mul_ediv_cancel_left x (by decide)
-- @endregion

-- @region chaining_functions.int_double_not_undoes_halve
-- @provenance independent
/-- … but on the integers doubling does **not** undo halving: `1` is halved (rounding down) to
`0`, and doubling `0` gives `0`, not `1`. So `x ↦ 2x` has no inverse function `ℤ → ℤ`: odd
numbers are never outputs, so nothing can be sent back to them. -/
theorem int_double_not_undoes_halve : ¬ Undoes (fun x : Int => 2 * x) (fun y => y / 2) := by
  intro h
  have h1 : 2 * (1 / 2 : Int) = 1 := h 1
  exact absurd h1 (by decide)
-- @endregion

-- @region chaining_functions.undo_chain
-- @provenance independent
/-- **Socks and shoes.** If `f'` undoes `f` and `g'` undoes `g`, then "`f`, then `g`" is undone by
"`g'`, then `f'`": undo the **last** step **first**. The calculation:
`f' (g' (g (f a))) = f' (f a) = a`. -/
theorem undo_chain {α β γ : Type} {f : α → β} {g : β → γ} {f' : β → α} {g' : γ → β}
    (hf : Undoes f' f) (hg : Undoes g' g) : Undoes (andThen g' f') (andThen f g) := by
  intro a
  calc andThen g' f' (andThen f g a) = f' (g' (g (f a))) := rfl
    _ = f' (f a) := by rw [hg (f a)]
    _ = a := hf a
-- @endregion

/-! ### Converting temperatures, and undoing in the right order -/

-- @region chaining_functions.to_fahrenheit
-- @provenance definition
/-- Celsius to Fahrenheit: multiply by `9/5`, then add `32`. -/
def toFahrenheit : Rat → Rat := andThen (fun c => 9 / 5 * c) (fun x => x + 32)
-- @endregion

-- @region chaining_functions.to_celsius
-- @provenance definition
/-- Fahrenheit to Celsius: subtract `32`, then multiply by `5/9` — the undoing steps, in reverse
order. -/
def toCelsius : Rat → Rat := andThen (fun f => f - 32) (fun x => 5 / 9 * x)
-- @endregion

-- @region chaining_functions.thirty_degrees
-- @provenance independent
/-- A warm day: `30 °C` is `86 °F`, and converting back gives `30 °C` again. Lean checks the
fraction arithmetic exactly (`decide +kernel` evaluates both sides). -/
theorem thirty_degrees : toFahrenheit 30 = 86 ∧ toCelsius 86 = 30 := by
  decide +kernel
-- @endregion

-- @region chaining_functions.to_celsius_undoes
-- @provenance independent
/-- `toCelsius` undoes `toFahrenheit` for **every** temperature. This is the socks-and-shoes rule
`undo_chain` applied to the two steps: `× 5/9` undoes `× 9/5`, and `− 32` undoes `+ 32`. -/
theorem to_celsius_undoes : Undoes toCelsius toFahrenheit := by
  apply undo_chain
  · intro c
    show 5 / 9 * (9 / 5 * c) = c
    grind
  · intro x
    show x + 32 - 32 = x
    grind
-- @endregion

-- @region chaining_functions.wrong_order_fails
-- @provenance independent
/-- Undoing the steps in the **wrong** order fails: "multiply by `5/9`, then subtract `32`" does
not undo `toFahrenheit`. At `0 °C`: `toFahrenheit 0 = 32`, and `5/9 · 32 − 32 = −128/9 ≠ 0`. -/
theorem wrong_order_fails :
    ¬ Undoes (andThen (fun x : Rat => 5 / 9 * x) (fun x => x - 32)) toFahrenheit := by
  intro h
  have h0 := h 0
  revert h0
  decide +kernel
-- @endregion

/-! ### Which functions can be undone? -/

-- @region chaining_functions.injective_of_undoes
-- @provenance independent
/-- If `f` can be undone, then different inputs always give different outputs: from
`f a = f b`, apply the undoing function `g` to both sides to get `a = g (f a) = g (f b) = b`. -/
theorem injective_of_undoes {α β : Type} {f : α → β} {g : β → α} (h : Undoes g f) (a b : α)
    (hab : f a = f b) : a = b :=
  calc a = g (f a) := (h a).symm
    _ = g (f b) := by rw [hab]
    _ = b := h b
-- @endregion

-- @region chaining_functions.injective_of_undoes_library
-- @provenance library
/-- The same fact from core Lean's library, where "`g` undoes `f`" is called
`Function.LeftInverse g f` (it is defined exactly like our `Undoes g f`) and "never sends two
inputs to the same output" is `Function.Injective f`. This applies
`Function.LeftInverse.injective`. -/
theorem injective_of_undoes_library {α β : Type} {f : α → β} {g : β → α} (h : Undoes g f) :
    Function.Injective f :=
  Function.LeftInverse.injective h
-- @endregion

-- @region chaining_functions.square_cannot_be_undone
-- @provenance independent
/-- **Squaring on ℤ cannot be undone**: `2² = (−2)² = 4`, so an undoing function would have to
send `4` back to both `2` and `−2`. -/
theorem square_cannot_be_undone : ¬ ∃ g : Int → Int, Undoes g (fun x => x * x) := by
  intro ⟨g, hg⟩
  have h : (2 : Int) = -2 := injective_of_undoes hg 2 (-2) (by decide)
  exact absurd h (by decide)
-- @endregion

end Lumenary.ChainingFunctions
