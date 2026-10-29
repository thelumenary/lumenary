/-
The Lumenary — formal mathematics
Differential topology: Sard's theorem in equal dimensions, the ingredients of the hairy ball
theorem (a nowhere-vanishing tangent field on odd spheres, the rotation homotopy from the
identity to the antipodal map, the sign of the antipodal map), the one-dimensional no-retraction
and Brouwer theorems, and the parity of level crossings — the one-dimensional shadow of the
mod 2 degree.

What is proved here and what Mathlib provides. Mathlib proves Sard's theorem for maps between
spaces of the same finite dimension (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`):
the image of the set where the derivative is singular has measure zero. We cite it and deduce
that the critical values of a differentiable map `E → E` form a null set. Degree theory, the
Brouwer fixed-point theorem in dimensions `≥ 2`, the hairy ball theorem and the Poincaré–Hopf
theorem are not in Mathlib. The *independent* declarations below formalise the explicit
constructions in their proofs: the vector field `z ↦ i z` on `S^{2n-1} ⊂ ℂⁿ`, the homotopy
`cos(πt) x + sin(πt) v(x)` that stays on the sphere and joins `x` to `-x`, the determinant
`(-1)^{n+1}` of the antipodal map, the retraction argument for `[-1, 1]`, and the parity lemma
for crossings of a level.
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Lumenary.DifferentialTopology

open Set

/-! ### Sard's theorem in equal dimensions -/

-- @region differential_topology.sard_equidimensional
-- @provenance library
/-- **Sard's theorem (equal dimensions).** If `f : E → E` has derivative `f' x` at each point of
`s` and `f' x` is singular (`det = 0`) on `s`, then `f(s)` has measure zero for any Haar measure
(for instance Lebesgue measure on `ℝⁿ`). This is Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`; note that it needs only
differentiability, not `C¹`. -/
theorem sard_equidimensional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hsing : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) = 0 :=
  MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hf' hsing
-- @endregion

-- @region differential_topology.critical_values_null
-- @provenance independent
/-- **The critical values of a differentiable map `E → E` form a null set**, so almost every
value is regular. Apply `sard_equidimensional` to the set of critical points
`{x | det Df(x) = 0}`. (It does *not* say there are no critical values: a fold `x ↦ x²` has the
critical value `0`.) -/
theorem critical_values_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {f : E → E}
    (hf : Differentiable ℝ f) :
    μ (f '' {x | (fderiv ℝ f x).det = 0}) = 0 :=
  sard_equidimensional μ (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) fun _ hx => hx
-- @endregion

/-! ### Odd spheres carry a nowhere-vanishing tangent field -/

-- @region differential_topology.dot
-- @provenance definition
/-- The Euclidean inner product on `ℂⁿ = ℝ²ⁿ`: `⟨z, w⟩ = Σₖ (Re zₖ Re wₖ + Im zₖ Im wₖ)`. -/
def dot {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  ∑ k, ((z k).re * (w k).re + (z k).im * (w k).im)
-- @endregion

-- @region differential_topology.hopf_field
-- @provenance definition
/-- The **Hopf vector field** `v(z) = i z` on `ℂⁿ`. In real coordinates it is
`(x₁, y₁, …, xₙ, yₙ) ↦ (-y₁, x₁, …, -yₙ, xₙ)`. -/
def hopfField {n : ℕ} (z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => Complex.I * z k
-- @endregion

-- @region differential_topology.hopf_field_tangent
-- @provenance independent
/-- The Hopf field is **tangent** to every sphere centred at `0`: `⟨z, iz⟩ = 0`. Termwise,
`x·(-y) + y·x = 0`. -/
theorem hopfField_tangent {n : ℕ} (z : Fin n → ℂ) : dot z (hopfField z) = 0 := by
  simp only [dot, hopfField, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  apply Finset.sum_eq_zero
  intro k _
  ring
-- @endregion

-- @region differential_topology.hopf_field_length
-- @provenance independent
/-- The Hopf field has the same length as `z`: `⟨iz, iz⟩ = ⟨z, z⟩`. So on the unit sphere
`S^{2n-1}` it has length `1` and **vanishes nowhere**: odd-dimensional spheres are not hairy. -/
theorem hopfField_length {n : ℕ} (z : Fin n → ℂ) :
    dot (hopfField z) (hopfField z) = dot z z := by
  simp only [dot, hopfField, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  apply Finset.sum_congr rfl
  intro k _
  ring
-- @endregion

/-! ### The rotation homotopy and the antipodal map -/

-- @region differential_topology.rotation_homotopy
-- @provenance independent
/-- **The key homotopy in the hairy ball theorem.** If `x` and `v` are orthogonal unit vectors,
then `cos t • x + sin t • v` is a unit vector for every `t`; it equals `x` at `t = 0` and `-x`
at `t = π`. Applied pointwise to a unit tangent field `v(x)` on `Sⁿ`, this is a homotopy on the
sphere from the identity to the antipodal map. -/
theorem rotation_homotopy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x v : E} (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) (hxv : inner ℝ x v = 0) (t : ℝ) :
    ‖Real.cos t • x + Real.sin t • v‖ = 1 ∧
      Real.cos 0 • x + Real.sin 0 • v = x ∧
      Real.cos Real.pi • x + Real.sin Real.pi • v = -x := by
  refine ⟨?_, by simp, by simp⟩
  have hsq : ‖Real.cos t • x + Real.sin t • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      hxv, hx, hv, Real.norm_eq_abs, Real.norm_eq_abs]
    have := Real.cos_sq_add_sin_sq t
    nlinarith [sq_abs (Real.cos t), sq_abs (Real.sin t)]
  have hnn : 0 ≤ ‖Real.cos t • x + Real.sin t • v‖ := norm_nonneg _
  nlinarith [hsq, hnn]
-- @endregion

-- @region differential_topology.antipodal_det
-- @provenance independent
/-- The antipodal map of `Sⁿ` is the restriction of `-I` on `ℝⁿ⁺¹`, whose determinant is
`(-1)^{n+1}`. So it preserves orientation exactly when `n` is odd, and its degree is
`(-1)^{n+1}`. -/
theorem antipodal_det (n : ℕ) :
    (-1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det = (-1) ^ (n + 1) := by
  rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
-- @endregion

-- @region differential_topology.antipodal_det_even
-- @provenance independent
/-- On an **even**-dimensional sphere the antipodal map reverses orientation: `det(-I) = -1`
on `ℝⁿ⁺¹` when `n` is even. Since a homotopy cannot change the degree, the identity (degree `1`)
is not homotopic to the antipodal map (degree `-1`), and by `rotation_homotopy` there is no
unit tangent field on `Sⁿ`. -/
theorem antipodal_det_even {n : ℕ} (hn : Even n) :
    (-1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det = -1 := by
  rw [antipodal_det, pow_succ, hn.neg_one_pow, one_mul]
-- @endregion

/-! ### Dimension one: no retraction, and Brouwer -/

-- @region differential_topology.no_retraction_interval
-- @provenance independent
/-- **No retraction of `[-1, 1]` onto its boundary `{-1, 1}`.** A continuous map on `[-1, 1]`
taking only the values `±1` and fixing both endpoints would, by the intermediate value theorem,
take the value `0`. This is the one-dimensional case of the no-retraction theorem
`Dⁿ → Sⁿ⁻¹`. -/
theorem no_retraction_interval :
    ¬ ∃ r : ℝ → ℝ, ContinuousOn r (Icc (-1) 1) ∧ (∀ x ∈ Icc (-1 : ℝ) 1, r x = 1 ∨ r x = -1) ∧
      r (-1) = -1 ∧ r 1 = 1 := by
  rintro ⟨r, hcont, hval, hm, hp⟩
  have hivt := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont
  rw [hm, hp] at hivt
  obtain ⟨x, hx, hrx⟩ := hivt (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
  rcases hval x hx with h | h <;> linarith
-- @endregion

-- @region differential_topology.brouwer_interval
-- @provenance independent
/-- **Brouwer's fixed-point theorem in dimension one**, proved as in every dimension: a
continuous `f : [-1, 1] → [-1, 1]` without fixed points would give the retraction
`r(x) = (x - f(x)) / |x - f(x)|` onto `{-1, 1}`, contradicting `no_retraction_interval`. -/
theorem brouwer_interval {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hmaps : MapsTo f (Icc (-1) 1) (Icc (-1) 1)) : ∃ x ∈ Icc (-1 : ℝ) 1, f x = x := by
  by_contra hno
  push Not at hno
  have hne : ∀ x ∈ Icc (-1 : ℝ) 1, x - f x ≠ 0 := fun x hx =>
    sub_ne_zero.mpr fun h => hno x hx h.symm
  apply no_retraction_interval
  refine ⟨fun x => (x - f x) / |x - f x|, ?_, ?_, ?_, ?_⟩
  · exact (continuousOn_id.sub hf).div (continuousOn_id.sub hf).abs fun x hx =>
      abs_ne_zero.mpr (hne x hx)
  · intro x hx
    dsimp only
    rcases abs_choice (x - f x) with h | h <;> rw [h]
    · exact Or.inl (div_self (hne x hx))
    · exact Or.inr (by rw [div_neg, div_self (hne x hx)])
  · have hm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hlt : -1 - f (-1) < 0 := by
      have h1 := (hmaps hm).1
      have h2 := hne (-1) hm
      exact lt_of_le_of_ne (by linarith) h2
    dsimp only
    rw [abs_of_neg hlt, div_neg, div_self hlt.ne]
  · have hp : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hpos : 0 < 1 - f 1 := by
      have h1 := (hmaps hp).2
      have h2 := hne 1 hp
      exact lt_of_le_of_ne (by linarith) h2.symm
    dsimp only
    rw [abs_of_pos hpos, div_self hpos.ne']
-- @endregion

/-! ### Crossings of a level: degree mod 2 in dimension one -/

-- @region differential_topology.crossings
-- @provenance definition
/-- The number of times the finite sequence `a 0, a 1, …, a N` crosses the level `c`: the
number of steps `i < N` at which `a i < c` and `a (i+1) < c` disagree. -/
noncomputable def crossings (a : ℕ → ℝ) (c : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun i => decide (a i < c) ≠ decide (a (i + 1) < c)).card
-- @endregion

-- @region differential_topology.crossings_parity
-- @provenance independent
/-- **Parity of crossings.** The number of crossings of the level `c` is even exactly when the
two ends `a 0` and `a N` lie on the same side of `c`. The number itself depends on `c` and on the
wiggles of the sequence; its parity depends only on the ends. This is the one-dimensional
heart of the mod 2 degree: the count of preimages changes in pairs. -/
theorem crossings_parity (a : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    Even (crossings a c N) ↔ decide (a 0 < c) = decide (a N < c) := by
  induction N with
  | zero => simp [crossings]
  | succ N ih =>
    have hstep : crossings a c (N + 1) = crossings a c N +
        if decide (a N < c) ≠ decide (a (N + 1) < c) then 1 else 0 := by
      unfold crossings
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    rw [hstep]
    generalize decide (a 0 < c) = p at *
    generalize decide (a N < c) = q at *
    generalize decide (a (N + 1) < c) = s
    split_ifs with h
    · rw [Nat.even_add_one, ih]
      cases p <;> cases q <;> cases s <;> simp_all
    · rw [add_zero, ih]
      cases p <;> cases q <;> cases s <;> simp_all
-- @endregion

-- @region differential_topology.odd_crossings
-- @provenance independent
/-- If the sequence starts below the level `c` and ends above it, it crosses `c` an **odd**
number of times, whatever `c` between the ends. -/
theorem odd_crossings {a : ℕ → ℝ} {c : ℝ} {N : ℕ} (h0 : a 0 < c) (hN : c < a N) :
    Odd (crossings a c N) := by
  rw [← Nat.not_even_iff_odd, crossings_parity]
  simp [h0, not_lt.mpr hN.le]
-- @endregion

end Lumenary.DifferentialTopology
