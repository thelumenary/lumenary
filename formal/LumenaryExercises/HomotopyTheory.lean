/-
The Lumenary — Lean exercises: Homotopy theory.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/HomotopyTheory.lean`.
-/
import Lumenary.HomotopyTheory

namespace LumenaryExercises.HomotopyTheory

-- @region ex.homotopy_theory.eckmann_hilton_units
-- @solution Lumenary.HomotopyTheory.eckmann_hilton
/-- The first step of the Eckmann–Hilton argument: the two units agree.
Hint: `e₁ = m₁ e₁ e₁ = m₁ (m₂ e₂ e₁) (m₂ e₁ e₂)`; now use the interchange law and the unit laws
once more. A `calc` block works well. -/
theorem eckmann_hilton_units {M : Type*} (m₁ m₂ : M → M → M) (e₁ e₂ : M)
    (h₁l : ∀ a, m₁ e₁ a = a) (h₁r : ∀ a, m₁ a e₁ = a)
    (h₂l : ∀ a, m₂ e₂ a = a) (h₂r : ∀ a, m₂ a e₂ = a)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    e₁ = e₂ := by
  sorry
-- @endregion

-- @region ex.homotopy_theory.hopf_circle_invariant
-- @solution Lumenary.HomotopyTheory.hopf_circle_invariant
/-- Show that the Hopf map is constant on the circle through `(z, w)`.
Hint: `Complex.mul_conj l : l * conj l = ↑(Complex.normSq l)`. After `unfold Lumenary.HomotopyTheory.hopf`
and `ext`, the first component is a `linear_combination` and the second is `Complex.normSq_mul`. -/
theorem hopf_circle_invariant (l z w : ℂ) (hl : Complex.normSq l = 1) :
    Lumenary.HomotopyTheory.hopf (l * z, l * w) = Lumenary.HomotopyTheory.hopf (z, w) := by
  sorry
-- @endregion

end LumenaryExercises.HomotopyTheory
