/-
The Lumenary — Lean exercises: Polynomials.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Polynomials.lean`.
-/
import Lumenary.Polynomials

namespace LumenaryExercises.Polynomials

-- @region ex.polynomials.sub_dvd_pow_sub_pow
-- @solution Lumenary.Polynomials.sub_dvd_pow_sub_pow'
/-- Show that `x − a` divides `xⁿ − aⁿ` in every commutative ring.
Hint: `induction n with`, and in the successor case use the identity
`xⁿ⁺¹ − aⁿ⁺¹ = x(xⁿ − aⁿ) + aⁿ(x − a)`; `obtain ⟨q, hq⟩ := ih` unpacks the divisibility. -/
theorem sub_dvd_pow_sub_pow' {R : Type*} [CommRing R] (x a : R) (n : ℕ) :
    x - a ∣ x ^ n - a ^ n := by
  sorry
-- @endregion

-- @region ex.polynomials.two_roots_mod_seven
-- @solution Lumenary.Polynomials.two_roots_mod_seven
/-- Show that modulo 7 the polynomial `x² − 1` has exactly the roots `1` and `6`.
Hint: there are only seven cases, and Lean can check them all for you. -/
theorem two_roots_mod_seven : ∀ x : ZMod 7, x ^ 2 - 1 = 0 ↔ x = 1 ∨ x = 6 := by
  sorry
-- @endregion

end LumenaryExercises.Polynomials
