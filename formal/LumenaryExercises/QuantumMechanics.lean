/-
The Lumenary — Lean exercises: Mathematical foundations of quantum mechanics.
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/QuantumMechanics.lean`.
-/
import Lumenary.QuantumMechanics

namespace LumenaryExercises.QuantumMechanics

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- @region ex.quantum_mechanics.eigenvectors_orthogonal
-- @solution Lumenary.QuantumMechanics.eigenvectors_orthogonal
/-- **Eigenvectors for different eigenvalues are orthogonal.** Hint: rewrite `hA v w` with `hv`,
`hw`, `inner_smul_left`, `inner_smul_right` and `Complex.conj_ofReal` to get
`lv * ⟪v, w⟫ = lw * ⟪v, w⟫`, then use `mul_eq_zero` on `(lv - lw) * ⟪v, w⟫ = 0`. -/
theorem eigenvectors_orthogonal {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {v w : E} {lv lw : ℝ}
    (hv : A v = (lv : ℂ) • v) (hw : A w = (lw : ℂ) • w) (hne : lv ≠ lw) : ⟪v, w⟫_ℂ = 0 := by
  sorry
-- @endregion

-- @region ex.quantum_mechanics.number_raise
-- @solution Lumenary.QuantumMechanics.number_raise
/-- **`[N, a†] = a†`.** Hint: `N a† − a† N = a† (a a† − a† a)` holds in any ring (`noncomm_ring`);
then rewrite with `h` and `mul_one`. -/
theorem number_raise {R : Type*} [Ring R] (a ad : R) (h : a * ad - ad * a = 1) :
    (ad * a) * ad - ad * (ad * a) = ad := by
  sorry
-- @endregion

end LumenaryExercises.QuantumMechanics
