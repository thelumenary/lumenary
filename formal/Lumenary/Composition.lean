/-
The Lumenary — formal mathematics
Composition of functions: associativity, identities, and how composition interacts with
injective, surjective and bijective functions.

`g ∘ f` means "first `f`, then `g`": `(g ∘ f) x = g (f x)` (core Lean's `Function.comp`).
Core Lean and Mathlib already contain several of these facts (`Function.comp_id`,
`Function.id_comp`, `Function.Injective.comp`, `Function.Surjective.comp`, Mathlib's
`Function.Bijective.comp`); here we prove them ourselves so the reasoning is visible.
-/
import Lumenary.Functions

namespace Lumenary.Composition

open Function
open Lumenary.Functions (Bijective)

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

-- @region composition.comp_assoc
-- @provenance independent
/-- Composition is **associative**: `h ∘ (g ∘ f) = (h ∘ g) ∘ f`.

Why does `rfl` prove it? By definition `(g ∘ f) = fun x => g (f x)`. Unfolding the
definition on both sides, each one becomes `fun x => h (g (f x))` — literally the same
function. Lean accepts `rfl` ("both sides are the same by definition") because its kernel
unfolds definitions and simplifies `(fun x => …) a` automatically. -/
theorem comp_assoc (f : α → β) (g : β → γ) (h : γ → δ) : h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl
-- @endregion

-- @region composition.id_comp
-- @provenance independent
/-- Doing nothing first changes nothing: `id ∘ f = f`. Both sides send `x` to `f x`, and
Lean identifies `fun x => f x` with `f` (η-conversion), so `rfl` works. -/
theorem id_comp (f : α → β) : id ∘ f = f := rfl
-- @endregion

-- @region composition.comp_id
-- @provenance independent
/-- Doing nothing afterwards changes nothing: `f ∘ id = f`. -/
theorem comp_id (f : α → β) : f ∘ id = f := rfl
-- @endregion

-- @region composition.injective_comp
-- @provenance independent
/-- A composite of injective functions is injective.
If `g (f a) = g (f b)`, injectivity of `g` gives `f a = f b`, and then injectivity of `f`
gives `a = b`. (Core analogue: `Function.Injective.comp`.) -/
theorem injective_comp {f : α → β} {g : β → γ} (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by
  intro a b h
  -- `h : g (f a) = g (f b)`
  have hfab : f a = f b := hg h
  exact hf hfab
-- @endregion

-- @region composition.surjective_comp
-- @provenance independent
/-- A composite of surjective functions is surjective.
To hit `c`, first find `b` with `g b = c`, then `a` with `f a = b`; then `g (f a) = c`.
(Core analogue: `Function.Surjective.comp`.) -/
theorem surjective_comp {f : α → β} {g : β → γ} (hg : Surjective g) (hf : Surjective f) :
    Surjective (g ∘ f) := by
  intro c
  obtain ⟨b, hb⟩ := hg c      -- `hb : g b = c`
  obtain ⟨a, ha⟩ := hf b      -- `ha : f a = b`
  refine ⟨a, ?_⟩
  show g (f a) = c
  rw [ha, hb]
-- @endregion

-- @region composition.bijective_comp
-- @provenance independent
/-- A composite of bijections is a bijection: combine the two previous results.
(Mathlib analogue: `Function.Bijective.comp`.) -/
theorem bijective_comp {f : α → β} {g : β → γ} (hg : Bijective g) (hf : Bijective f) :
    Bijective (g ∘ f) :=
  ⟨injective_comp hg.1 hf.1, surjective_comp hg.2 hf.2⟩
-- @endregion

-- @region composition.comp_not_comm
-- @provenance independent
/-- Composition is **not commutative**: "double, then add 1" differs from
"add 1, then double". At `0` the first gives `1` and the second gives `2`. -/
theorem comp_not_comm :
    (fun n : Int => n + 1) ∘ (fun n : Int => 2 * n) ≠ (fun n : Int => 2 * n) ∘ (fun n : Int => n + 1) := by
  intro h
  -- Evaluate both sides at `0`.
  have h0 : (2 * 0 + 1 : Int) = 2 * (0 + 1) := congrFun h 0
  -- But `2 * 0 + 1 = 1` and `2 * (0 + 1) = 2`.
  exact absurd h0 (by decide)
-- @endregion

end Lumenary.Composition
