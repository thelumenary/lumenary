/-
The Lumenary — formal mathematics
Modular (clock) arithmetic: wrapping around, inverses that exist and inverses that don't,
and congruence modulo `k` as an equivalence relation.

Small concrete facts are checked by computation (`decide` makes Lean evaluate both sides).
Mathlib analogue: `ZMod n` for the integers modulo `n`, and `Int.ModEq` (which has exactly
the definition of `ModEq` used below).
-/

namespace Lumenary.Modular

/-! ### Clock arithmetic -/

-- @region modular.clock_wraps
-- @provenance independent
/-- On a 12-hour clock, 5 hours after 9 o'clock is 2 o'clock: `(9 + 5) mod 12 = 2`. -/
theorem clock_wraps : (9 + 5) % 12 = 2 := by decide
-- @endregion

-- @region modular.three_inv_mod_seven
-- @provenance independent
/-- Modulo 7, the number 3 has an inverse, namely 5: `3 · 5 = 15 = 2 · 7 + 1`. -/
theorem three_inv_mod_seven : (3 * 5) % 7 = 1 := by decide
-- @endregion

-- @region modular.two_no_inv_mod_four
-- @provenance independent
/-- Modulo 4, the number 2 has **no** inverse: `2 · x` is always even, so it is never `1`
more than a multiple of 4. `decide` checks all four possibilities `x = 0, 1, 2, 3`. -/
theorem two_no_inv_mod_four : ∀ x : Fin 4, (2 * x.val) % 4 ≠ 1 := by decide
-- @endregion

-- @region modular.inverses_mod_five
-- @provenance independent
/-- Modulo 5 (a prime), every non-zero number has an inverse:
`1·1 = 1`, `2·3 = 6`, `3·2 = 6`, `4·4 = 16`, and each of these leaves remainder 1.
`decide` checks every `a` and searches for each `b`. -/
theorem inverses_mod_five : ∀ a : Fin 5, a.val ≠ 0 → ∃ b : Fin 5, (a.val * b.val) % 5 = 1 := by
  decide
-- @endregion

-- @region modular.mod_add_mod
-- @provenance library
/-- You may reduce before or after adding: `(a mod k + b mod k) mod k = (a + b) mod k`.
This applies core Lean's `Nat.add_mod`. -/
theorem mod_add_mod (a b k : Nat) : (a % k + b % k) % k = (a + b) % k :=
  (Nat.add_mod a b k).symm
-- @endregion

/-! ### Congruence modulo `k` -/

-- @region modular.mod_eq
-- @provenance definition
/-- `ModEq k a b` ("`a ≡ b (mod k)`"): `a` and `b` leave the same remainder on division by `k`.
(Mathlib analogue: `Int.ModEq`, defined the same way.) -/
def ModEq (k a b : Int) : Prop := a % k = b % k
-- @endregion

-- @region modular.mod_eq_refl
-- @provenance independent
/-- Every integer is congruent to itself. -/
theorem modEq_refl (k a : Int) : ModEq k a a := rfl
-- @endregion

-- @region modular.mod_eq_symm
-- @provenance independent
/-- If `a ≡ b` then `b ≡ a`. -/
theorem modEq_symm {k a b : Int} (h : ModEq k a b) : ModEq k b a := Eq.symm h
-- @endregion

-- @region modular.mod_eq_trans
-- @provenance independent
/-- If `a ≡ b` and `b ≡ c` then `a ≡ c`: equal remainders chain together. -/
theorem modEq_trans {k a b c : Int} (h₁ : ModEq k a b) (h₂ : ModEq k b c) : ModEq k a c :=
  Eq.trans h₁ h₂
-- @endregion

-- @region modular.mod_eq_equivalence
-- @provenance independent
/-- Congruence modulo `k` is an **equivalence relation** (reflexive, symmetric, transitive).
Its equivalence classes are the "hours" on a `k`-hour clock. -/
theorem modEq_equivalence (k : Int) : Equivalence (ModEq k) :=
  ⟨modEq_refl k, modEq_symm, modEq_trans⟩
-- @endregion

end Lumenary.Modular
