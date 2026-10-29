/-
The Lumenary — formal mathematics
Numerical analysis: the condition number and the perturbation bound for linear systems, LU
factorisation with and without pivoting, Euler's method (one-step error, discrete Gronwall
inequality, first-order global error bound), and the stability of explicit and implicit Euler
on the test equation `y' = λ y`.

What is proved here and what Mathlib provides. Mathlib has operator norms of continuous linear
maps (`‖A‖` for `A : E →L[ℝ] F`, with `ContinuousLinearMap.le_opNorm`), matrices and determinants
(`Matrix.det_mul`), and the inequality `x + 1 ≤ eˣ`. It has no model of floating-point
arithmetic and no library of numerical algorithms, so statements about rounding errors and
backward stability are not formalised. The *independent* declarations prove: `κ(A) ≥ 1`; the
relative error bound `‖δx‖/‖x‖ ≤ κ(A) ‖δb‖/‖b‖` (in multiplied-out form); exact LU factorisations
of a 3 × 3 example and of the 2 × 2 pivoting example, with and without a row swap; the error
recursion for Euler's method, the discrete Gronwall inequality, and the global bound
`|eₙ| ≤ C h · T e^{L T}` (`T = n h`), which says Euler's method has order 1; and the stability
facts for the test equation: explicit Euler multiplies by `1 + hλ`, which is stable exactly when
`h |λ| < 2`, while backward Euler multiplies by `1/(1 - hλ) ∈ (0, 1)` for every step `h > 0`.
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs

namespace Lumenary.NumericalAnalysis

open Matrix

/-! ### Conditioning of linear systems -/

-- @region numerical_analysis.cond_num
-- @provenance definition
/-- The **condition number** `κ(A) = ‖A‖ ‖A⁻¹‖` of an invertible bounded linear map between normed
spaces (for matrices, with the operator norm induced by the chosen vector norm). -/
noncomputable def condNum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) : ℝ :=
  ‖(A : E →L[ℝ] F)‖ * ‖(A.symm : F →L[ℝ] E)‖
-- @endregion

-- @region numerical_analysis.op_norm_bound
-- @provenance library
/-- The defining property of the operator norm: `‖A x‖ ≤ ‖A‖ ‖x‖`. This applies Mathlib's
`ContinuousLinearMap.le_opNorm`. -/
theorem op_norm_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (x : E) : ‖A x‖ ≤ ‖A‖ * ‖x‖ :=
  A.le_opNorm x
-- @endregion

-- @region numerical_analysis.one_le_cond_num
-- @provenance independent
/-- **`κ(A) ≥ 1`.** For `x ≠ 0`, `‖x‖ = ‖A⁻¹(A x)‖ ≤ ‖A⁻¹‖ ‖A‖ ‖x‖`; divide by `‖x‖`. A condition
number near `1` (an orthogonal matrix in the 2-norm) is as good as it gets. -/
theorem one_le_condNum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) {x : E} (hx : x ≠ 0) :
    1 ≤ condNum A := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : ‖x‖ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖A x‖ := by
    have := (A.symm : F →L[ℝ] E).le_opNorm (A x)
    simpa using this
  have h2 : ‖A x‖ ≤ ‖(A : E →L[ℝ] F)‖ * ‖x‖ := (A : E →L[ℝ] F).le_opNorm x
  have h3 : ‖x‖ ≤ condNum A * ‖x‖ := by
    calc ‖x‖ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖A x‖ := h1
      _ ≤ ‖(A.symm : F →L[ℝ] E)‖ * (‖(A : E →L[ℝ] F)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = condNum A * ‖x‖ := by unfold condNum; ring
  nlinarith
-- @endregion

-- @region numerical_analysis.relative_error_bound
-- @provenance independent
/-- **The perturbation bound.** If `A x = b` and `A (x + δx) = b + δb`, then
`‖δx‖ · ‖b‖ ≤ κ(A) · ‖δb‖ · ‖x‖`, i.e. `‖δx‖/‖x‖ ≤ κ(A) ‖δb‖/‖b‖`: the relative error in the
solution is at most the condition number times the relative error in the data. Proof: by
linearity `A δx = δb`, so `δx = A⁻¹ δb` and `‖δx‖ ≤ ‖A⁻¹‖ ‖δb‖`; and `‖b‖ = ‖A x‖ ≤ ‖A‖ ‖x‖`.
Multiply the two inequalities. -/
theorem relative_error_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) {x δx : E} {b δb : F}
    (hb : A x = b) (hpert : A (x + δx) = b + δb) :
    ‖δx‖ * ‖b‖ ≤ condNum A * ‖δb‖ * ‖x‖ := by
  have hAδ : A δx = δb := by
    rw [map_add, hb] at hpert
    exact add_left_cancel hpert
  have h1 : ‖δx‖ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖δb‖ := by
    have := (A.symm : F →L[ℝ] E).le_opNorm δb
    rw [← hAδ] at this ⊢
    simpa using this
  have h2 : ‖b‖ ≤ ‖(A : E →L[ℝ] F)‖ * ‖x‖ := by
    rw [← hb]; exact (A : E →L[ℝ] F).le_opNorm x
  calc ‖δx‖ * ‖b‖ ≤ (‖(A.symm : F →L[ℝ] E)‖ * ‖δb‖) * (‖(A : E →L[ℝ] F)‖ * ‖x‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = condNum A * ‖δb‖ * ‖x‖ := by unfold condNum; ring
-- @endregion

/-! ### LU factorisation -/

-- @region numerical_analysis.lu_example
-- @provenance independent
/-- **An LU factorisation**, as produced by Gaussian elimination: subtract `2 ×` row 1 from row 2
and `4 ×` row 1 from row 3, then `3 ×` the new row 2 from row 3. The multipliers `2, 4, 3` fill
the unit lower triangular factor `L`; the result of elimination is the upper triangular `U`.
Checked by exact rational arithmetic. -/
theorem lu_example :
    !![(2 : ℚ), 1, 1; 4, 3, 3; 8, 7, 9] = !![(1 : ℚ), 0, 0; 2, 1, 0; 4, 3, 1] * !![(2 : ℚ), 1, 1; 0, 1, 1; 0, 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
-- @endregion

-- @region numerical_analysis.det_mul_lu
-- @provenance library
/-- `det (L U) = det L · det U`. This applies Mathlib's `Matrix.det_mul`. With `L` unit lower
triangular (`det L = 1`) and `U` upper triangular, `det A` is the product of the pivots — the
cheapest way to compute a determinant (about `2n³/3` operations instead of `n!` terms). -/
theorem det_mul_lu {n : ℕ} (L U : Matrix (Fin n) (Fin n) ℚ) : (L * U).det = L.det * U.det :=
  Matrix.det_mul L U
-- @endregion

-- @region numerical_analysis.det_via_lu
-- @provenance independent
/-- The determinant of the example matrix is the product of the pivots `2 · 1 · 2 = 4`, computed
through the factorisation `lu_example` (`det L = 1` and `det U = 4`, each by the formula for a
3 × 3 determinant). -/
theorem det_via_lu : (!![(2 : ℚ), 1, 1; 4, 3, 3; 8, 7, 9]).det = 4 := by
  rw [lu_example, Matrix.det_mul, Matrix.det_fin_three, Matrix.det_fin_three]
  simp
  norm_num
-- @endregion

-- @region numerical_analysis.no_pivot_lu
-- @provenance independent
/-- **Why pivot: elimination without a row swap.** For `ε ≠ 0`,
`[[ε, 1], [1, 1]] = [[1, 0], [1/ε, 1]] · [[ε, 1], [0, 1 - 1/ε]]`. When `ε` is tiny the multiplier
`1/ε` and the entry `1 - 1/ε` are huge, and in floating point `1 - 1/ε` rounds to `-1/ε`,
destroying the information in the `(2, 2)` entry: the computed solution can be completely wrong
although the matrix is perfectly well conditioned. -/
theorem no_pivot_lu {ε : ℝ} (hε : ε ≠ 0) :
    !![ε, 1; 1, 1] = !![1, 0; 1 / ε, 1] * !![ε, 1; 0, 1 - 1 / ε] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp
-- @endregion

-- @region numerical_analysis.pivot_lu
-- @provenance independent
/-- **With partial pivoting.** Swapping the rows first (`P A` with `P` the swap) gives
`[[1, 1], [ε, 1]] = [[1, 0], [ε, 1]] · [[1, 1], [0, 1 - ε]]`: the multiplier is `ε`, at most `1`
in absolute value, and no entry grows. Partial pivoting always chooses the largest available
pivot, so every multiplier satisfies `|ℓᵢⱼ| ≤ 1`. -/
theorem pivot_lu (ε : ℝ) :
    !![1, 1; ε, 1] = !![1, 0; ε, 1] * !![(1 : ℝ), 1; 0, 1 - ε] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
-- @endregion

/-! ### Euler's method: error analysis -/

-- @region numerical_analysis.euler_error_step
-- @provenance independent
/-- **One step of the error recursion.** Let `yₙ₊₁ = yₙ + h f(tₙ, yₙ)` (Euler) and let the exact
solution satisfy `y(tₙ₊₁) = y(tₙ) + h f(tₙ, y(tₙ)) + τₙ` (`τₙ` is the local truncation error).
If `f` is `L`-Lipschitz in `y`, the error `eₙ = y(tₙ) - yₙ` satisfies
`|eₙ₊₁| ≤ (1 + h L) |eₙ| + |τₙ|`. -/
theorem euler_error_step {f : ℝ → ℝ → ℝ} {L h t yn Y τ : ℝ} (hh : 0 ≤ h)
    (hlip : ∀ s u v, |f s u - f s v| ≤ L * |u - v|) :
    |(Y + h * f t Y + τ) - (yn + h * f t yn)| ≤ (1 + h * L) * |Y - yn| + |τ| := by
  have hf := hlip t Y yn
  calc |(Y + h * f t Y + τ) - (yn + h * f t yn)|
      = |(Y - yn) + h * (f t Y - f t yn) + τ| := by ring_nf
    _ ≤ |Y - yn| + |h * (f t Y - f t yn)| + |τ| := abs_add_three _ _ _
    _ = |Y - yn| + h * |f t Y - f t yn| + |τ| := by rw [abs_mul, abs_of_nonneg hh]
    _ ≤ |Y - yn| + h * (L * |Y - yn|) + |τ| := by gcongr
    _ = (1 + h * L) * |Y - yn| + |τ| := by ring
-- @endregion

-- @region numerical_analysis.discrete_gronwall
-- @provenance independent
/-- **Discrete Gronwall inequality.** If `eₙ₊₁ ≤ (1 + h L) eₙ + τ` with `h L ≥ 0` and `τ ≥ 0`,
then `eₙ ≤ (1 + h L)ⁿ e₀ + n τ (1 + h L)ⁿ`. Errors committed at each step are amplified by at most
`(1 + h L)` per subsequent step. Induction on `n`. -/
theorem discrete_gronwall {e : ℕ → ℝ} {h L τ : ℝ} (hhL : 0 ≤ h * L) (hτ : 0 ≤ τ)
    (hstep : ∀ n, e (n + 1) ≤ (1 + h * L) * e n + τ) (n : ℕ) :
    e n ≤ (1 + h * L) ^ n * e 0 + n * τ * (1 + h * L) ^ n := by
  have hq : 1 ≤ 1 + h * L := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : 1 ≤ (1 + h * L) ^ (n + 1) := one_le_pow₀ hq
    calc e (n + 1) ≤ (1 + h * L) * e n + τ := hstep n
      _ ≤ (1 + h * L) * ((1 + h * L) ^ n * e 0 + n * τ * (1 + h * L) ^ n) + τ := by
          gcongr
      _ = (1 + h * L) ^ (n + 1) * e 0 + n * τ * (1 + h * L) ^ (n + 1) + τ := by ring
      _ ≤ (1 + h * L) ^ (n + 1) * e 0 + n * τ * (1 + h * L) ^ (n + 1)
            + τ * (1 + h * L) ^ (n + 1) := by nlinarith
      _ = (1 + h * L) ^ (n + 1) * e 0 + ((n + 1 : ℕ) : ℝ) * τ * (1 + h * L) ^ (n + 1) := by
          push_cast; ring
-- @endregion

-- @region numerical_analysis.one_add_le_exp
-- @provenance library
/-- `1 + x ≤ eˣ` for every real `x`, so `(1 + h L)ⁿ ≤ e^{n h L}`. This applies Mathlib's
`Real.add_one_le_exp`. -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  rw [add_comm]; exact Real.add_one_le_exp x
-- @endregion

-- @region numerical_analysis.euler_global_error
-- @provenance independent
/-- **Euler's method has order 1.** Suppose the errors satisfy `e₀ = 0` and
`eₙ₊₁ ≤ (1 + h L) eₙ + C h²` (the recursion of `euler_error_step`, with local truncation error
`|τₙ| ≤ C h²`, e.g. `C = max |y''| / 2`). Then at time `T = n h`,
`eₙ ≤ C h · T · e^{L T}`. For fixed `T`, the error is `O(h)`: halving the step halves the error. -/
theorem euler_global_error {e : ℕ → ℝ} {h L C : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (h0 : e 0 = 0) (hstep : ∀ n, e (n + 1) ≤ (1 + h * L) * e n + C * h ^ 2) (n : ℕ) :
    e n ≤ C * h * (n * h) * Real.exp (L * (n * h)) := by
  have hhL : 0 ≤ h * L := mul_nonneg hh hL
  have hg := discrete_gronwall hhL (by positivity) hstep n
  rw [h0, mul_zero, zero_add] at hg
  have hpow : (1 + h * L) ^ n ≤ Real.exp (L * (n * h)) := by
    calc (1 + h * L) ^ n ≤ Real.exp (h * L) ^ n :=
          pow_le_pow_left₀ (by linarith) (one_add_le_exp _) n
      _ = Real.exp (L * (n * h)) := by rw [← Real.exp_nat_mul]; ring_nf
  calc e n ≤ n * (C * h ^ 2) * (1 + h * L) ^ n := hg
    _ ≤ n * (C * h ^ 2) * Real.exp (L * (n * h)) := by
        apply mul_le_mul_of_nonneg_left hpow; positivity
    _ = C * h * (n * h) * Real.exp (L * (n * h)) := by ring
-- @endregion

/-! ### Stability on the test equation `y' = λ y` -/

-- @region numerical_analysis.explicit_euler_iterate
-- @provenance independent
/-- **Explicit Euler on `y' = λ y`** is `yₙ₊₁ = yₙ + h λ yₙ = (1 + hλ) yₙ`, so after `n` steps
`yₙ = (1 + hλ)ⁿ y₀`. The exact solution is `e^{λ n h} y₀`. -/
theorem explicit_euler_iterate (h lam y₀ : ℝ) (n : ℕ) :
    (fun y => y + h * (lam * y))^[n] y₀ = (1 + h * lam) ^ n * y₀ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih]; ring
-- @endregion

-- @region numerical_analysis.explicit_euler_stable_iff
-- @provenance independent
/-- **Stability of explicit Euler.** For a decaying equation (`λ < 0`) and step `h > 0`, the
numerical solution decays (`|1 + hλ| < 1`) exactly when `h |λ| < 2`. For a stiff equation with
`λ = -1000` this forces `h < 0.002`, whatever accuracy is wanted. -/
theorem explicit_euler_stable_iff {h lam : ℝ} (hh : 0 < h) (hlam : lam < 0) :
    |1 + h * lam| < 1 ↔ h * (-lam) < 2 := by
  have : 0 < h * (-lam) := mul_pos hh (by linarith)
  rw [abs_lt]
  constructor
  · rintro ⟨h1, -⟩; linarith
  · intro h2; constructor <;> nlinarith
-- @endregion

-- @region numerical_analysis.backward_euler_contracts
-- @provenance independent
/-- **Backward Euler is unconditionally stable on decaying modes.** The implicit step
`yₙ₊₁ = yₙ + h λ yₙ₊₁` gives `yₙ₊₁ = yₙ / (1 - hλ)`, and for `λ < 0` and every `h > 0` the factor
`1/(1 - hλ)` lies strictly between `0` and `1`: the numerical solution decays, like the true
one, with no restriction on the step size (A-stability, on the negative real axis). -/
theorem backward_euler_contracts {h lam : ℝ} (hh : 0 < h) (hlam : lam < 0) :
    0 < 1 / (1 - h * lam) ∧ 1 / (1 - h * lam) < 1 := by
  have hpos : 1 < 1 - h * lam := by nlinarith
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; exact hpos
-- @endregion

end Lumenary.NumericalAnalysis
