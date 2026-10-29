/-
The Lumenary — Lean exercises: Quotients.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/Quotients.lean`.
-/
import Lumenary.Quotients

namespace LumenaryExercises.Quotients

-- @region ex.quotients.ideal_mul_well_defined
-- @solution Lumenary.Quotients.ideal_mul_well_defined
/-- Multiplication of residues modulo an ideal is well defined.
Hint: `a * b - a' * b' = a * (b - b') + (a - a') * b'` (prove it with `ring`), then use
`I.add_mem`, `I.mul_mem_left` and `I.mul_mem_right`. -/
theorem ideal_mul_well_defined {R : Type*} [CommRing R] (I : Ideal R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) : a * b - a' * b' ∈ I := by
  sorry
-- @endregion

-- @region ex.quotients.normal_of_coset_mul_well_defined
-- @solution Lumenary.Quotients.normal_of_coset_mul_well_defined
/-- If coset multiplication is well defined, the subgroup is normal.
Hint: to show `g * n * g⁻¹ ∈ H`, apply `h` with `a = 1`, `a' = n` and `b = b' = g⁻¹`. -/
theorem normal_of_coset_mul_well_defined {G : Type*} [Group G] (H : Subgroup G)
    (h : ∀ a a' b b' : G, a⁻¹ * a' ∈ H → b⁻¹ * b' ∈ H → (a * b)⁻¹ * (a' * b') ∈ H) :
    H.Normal := by
  sorry
-- @endregion

end LumenaryExercises.Quotients
