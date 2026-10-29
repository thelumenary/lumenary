/-
The Lumenary — formal mathematics
Symplectic geometry: Hamiltonian flows conserve energy, the linear algebra of symplectic forms
(even dimension, area in the plane, divergence-free linear Hamiltonian fields), and a complete
proof of the *linear* non-squeezing theorem in ℝ⁴, contrasted with a volume-preserving map that
does squeeze.

What is proved here and what Mathlib provides. Mathlib has the symplectic group
`Matrix.symplecticGroup l R` of matrices `A` with `A * J * Aᵀ = J` (for `J` indexed by `l ⊕ l`),
with the deep fact that every symplectic matrix has determinant `1` (`SymplecticGroup.det_eq_one`,
the linear Liouville theorem) and that the transpose of a symplectic matrix is symplectic. The
*independent* declarations prove: conservation of the Hamiltonian along any flow line of a vector
field `X` with `ι_X ω = dH` for an alternating `ω`; `Aᵀ J A = det A • J` for 2 × 2 matrices, so
that "symplectic" means "area- and orientation-preserving" in the plane; that a skew-symmetric
matrix of odd size is singular (so symplectic forms live in even dimension); that linear
Hamiltonian vector fields have trace zero (infinitesimal Liouville); a Wirtinger-type inequality
`ω(a, b)² + ⟨a, b⟩² ≤ |a|² |b|²` in ℝ⁴; and from it linear non-squeezing. Not formalised:
symplectic manifolds, Darboux's theorem and Moser's trick (Mathlib has smooth manifolds and
differential forms on normed spaces, but no symplectic manifolds yet), Gromov's non-linear
non-squeezing theorem, which needs pseudo-holomorphic curves, and Floer homology.
-/
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt

namespace Lumenary.SymplecticGeometry

open Matrix

/-! ### Hamiltonian flows conserve energy -/

-- @region symplectic_geometry.hamiltonian_energy_conserved
-- @provenance independent
/-- **Hamiltonian flows conserve the Hamiltonian.** Let `ω` be any alternating form on a real
normed space `V` (`ω v v = 0`), `H : V → ℝ` differentiable with derivative `dH z` at `z`, and `X`
the Hamiltonian vector field, defined by `ι_{X} ω = dH`, i.e. `ω (X z) w = dH z w`. Along any
flow line `γ' = X(γ)` the value `H(γ t)` is constant. Proof: by the chain rule
`(H ∘ γ)' = dH(γ)(X(γ)) = ω(X(γ), X(γ)) = 0`. Non-degeneracy of `ω` is what makes `X` exist and
be unique; it is not needed for conservation. -/
theorem hamiltonian_energy_conserved {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ω : V → V → ℝ) (hω : ∀ v, ω v v = 0)
    {H : V → ℝ} {dH : V → V →L[ℝ] ℝ} (hH : ∀ z, HasFDerivAt H (dH z) z)
    {X : V → V} (hX : ∀ z w, ω (X z) w = dH z w)
    {γ : ℝ → V} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) (s t : ℝ) :
    H (γ s) = H (γ t) := by
  have hd : ∀ τ, HasDerivAt (fun τ => H (γ τ)) 0 τ := by
    intro τ
    have h := (hH (γ τ)).comp_hasDerivAt τ (hγ τ)
    have h0 : dH (γ τ) (X (γ τ)) = 0 := by rw [← hX, hω]
    rw [h0] at h
    exact h
  exact is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv) s t
-- @endregion

/-! ### Linear algebra in the plane: symplectic = area-preserving -/

-- @region symplectic_geometry.j2
-- @provenance definition
/-- The standard symplectic matrix on ℝ² = {(q, p)}: `ω₀(u, v) = uᵀ J v = u₁ v₂ - u₂ v₁`, the
signed area of the parallelogram spanned by `u` and `v`. -/
def J2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
-- @endregion

-- @region symplectic_geometry.transpose_mul_j2_mul
-- @provenance independent
/-- For every real 2 × 2 matrix, `Aᵀ J A = (det A) J`: a linear map of the plane multiplies the
symplectic form, i.e. signed area, by its determinant. Proved entry by entry. -/
theorem transpose_mul_J2_mul (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Aᵀ * J2 * A = A.det • J2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring
-- @endregion

-- @region symplectic_geometry.symplectic_iff_det_eq_one
-- @provenance independent
/-- **In dimension two, symplectic means area- and orientation-preserving**: `Aᵀ J A = J` if
and only if `det A = 1`. In dimension four and higher this fails (see `squeeze`). -/
theorem symplectic_iff_det_eq_one (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Aᵀ * J2 * A = J2 ↔ A.det = 1 := by
  rw [transpose_mul_J2_mul]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simpa [J2] using this
  · intro h
    rw [h, one_smul]
-- @endregion

-- @region symplectic_geometry.shear_symplectic
-- @provenance independent
/-- A shear `(q, p) ↦ (q + t p, p)` is symplectic: its determinant is `1`. (Solution of the Lean
exercise; it also describes the exact flow of the free particle `H = p²/2` for time `t`.) -/
theorem shear_symplectic (t : ℝ) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * J2 * !![1, t; 0, 1] = J2 := by
  rw [symplectic_iff_det_eq_one, Matrix.det_fin_two_of]
  ring
-- @endregion

/-! ### Why symplectic forms live in even dimension -/

-- @region symplectic_geometry.det_eq_zero_of_skew_odd
-- @provenance independent
/-- A skew-symmetric real matrix of odd size is singular: `det A = det Aᵀ = det (-A) =
(-1)ⁿ det A = -det A`. So an alternating bilinear form on an odd-dimensional space is always
degenerate, and a symplectic vector space (or manifold) has even dimension. -/
theorem det_eq_zero_of_skew_odd {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = -A) : A.det = 0 := by
  have h1 : A.det = (-A).det := by rw [← hA, det_transpose]
  rw [det_neg, Fintype.card_fin, hn.neg_one_pow] at h1
  linarith
-- @endregion

/-! ### Liouville's theorem, infinitesimally and linearly -/

-- @region symplectic_geometry.trace_skew_mul_symm
-- @provenance independent
/-- **Linear Hamiltonian vector fields are divergence-free.** For a quadratic Hamiltonian
`H(z) = ½ zᵀ S z` the Hamiltonian vector field is linear, `X(z) = J S z` with `J` skew and `S`
symmetric, and its divergence is `trace (J S)`, which vanishes:
`tr(JS) = tr((JS)ᵀ) = tr(Sᵀ Jᵀ) = -tr(S J) = -tr(J S)`. This is Liouville's theorem at the level
of vector fields: the flow `exp(t J S)` has determinant `exp(t · tr(JS)) = 1`. -/
theorem trace_skew_mul_symm {n : ℕ} (J S : Matrix (Fin n) (Fin n) ℝ)
    (hJ : Jᵀ = -J) (hS : Sᵀ = S) : (J * S).trace = 0 := by
  have h : (J * S).trace = -(J * S).trace := by
    calc (J * S).trace = (J * S)ᵀ.trace := (trace_transpose _).symm
      _ = (Sᵀ * Jᵀ).trace := by rw [transpose_mul]
      _ = (S * -J).trace := by rw [hS, hJ]
      _ = -(S * J).trace := by rw [Matrix.mul_neg, trace_neg]
      _ = -(J * S).trace := by rw [trace_mul_comm]
  linarith
-- @endregion

-- @region symplectic_geometry.symplectic_det_eq_one
-- @provenance library
/-- **Linear Liouville theorem**: every symplectic matrix (over any commutative ring) has
determinant `1`, so linear symplectic maps preserve volume. This applies Mathlib's
`SymplecticGroup.det_eq_one`, whose proof reduces to local rings and builds an invertible block
by hand; Mathlib's convention is `A * J * Aᵀ = J` with `J = !![0, -1; 1, 0]` in blocks. -/
theorem symplectic_det_eq_one {l : Type*} [DecidableEq l] [Fintype l]
    {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticGroup l ℝ) : A.det = 1 :=
  SymplecticGroup.det_eq_one hA
-- @endregion

-- @region symplectic_geometry.symplectic_transpose_mem
-- @provenance library
/-- The transpose of a symplectic matrix is symplectic (so `A * J * Aᵀ = J` and `Aᵀ * J * A = J`
define the same group). This applies Mathlib's `SymplecticGroup.transpose_mem`. It is why the
*rows* of a symplectic matrix pair up under `ω`, which the non-squeezing proof below uses. -/
theorem symplectic_transpose_mem {l : Type*} [DecidableEq l] [Fintype l]
    {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticGroup l ℝ) :
    Aᵀ ∈ symplecticGroup l ℝ :=
  SymplecticGroup.transpose_mem hA
-- @endregion

/-! ### Linear non-squeezing in ℝ⁴ = {(x₁, y₁, x₂, y₂)} -/

-- @region symplectic_geometry.j4
-- @provenance definition
/-- The standard symplectic matrix on ℝ⁴ with coordinates ordered `(x₁, y₁, x₂, y₂)`, so that
`ω₀ = dx₁ ∧ dy₁ + dx₂ ∧ dy₂`. -/
def J4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]
-- @endregion

-- @region symplectic_geometry.omega4
-- @provenance definition
/-- The standard symplectic form on ℝ⁴: the sum of the signed areas of the projections of the
parallelogram spanned by `u` and `v` to the `(x₁, y₁)`- and `(x₂, y₂)`-planes. -/
def omega4 (u v : Fin 4 → ℝ) : ℝ :=
  u 0 * v 1 - u 1 * v 0 + u 2 * v 3 - u 3 * v 2
-- @endregion

-- @region symplectic_geometry.mul_j4_mul_transpose_apply
-- @provenance independent
/-- The entries of `A J Aᵀ` are the symplectic pairings of the rows of `A`:
`(A J Aᵀ)ᵢⱼ = ω₀(rowᵢ A, rowⱼ A)`. -/
theorem mul_J4_mul_transpose_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (A * J4 * Aᵀ) i j = omega4 (A i) (A j) := by
  simp [J4, omega4, Matrix.mul_apply, Fin.sum_univ_four]
  ring
-- @endregion

-- @region symplectic_geometry.wirtinger4
-- @provenance independent
/-- **A Wirtinger-type inequality in ℝ⁴**: `ω₀(a, b)² + ⟨a, b⟩² ≤ |a|² |b|²`. The symplectic area
of a parallelogram never exceeds its Euclidean area. Proof: the difference is the sum of squares
`(p₀₂ - p₁₃)² + (p₀₃ + p₁₂)²` of Plücker coordinates `pᵢⱼ = aᵢ bⱼ - aⱼ bᵢ` (an identity checked
by `ring`). -/
theorem wirtinger4 (a b : Fin 4 → ℝ) :
    omega4 a b ^ 2 + (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  have key : (a ⬝ᵥ a) * (b ⬝ᵥ b) - (omega4 a b ^ 2 + (a ⬝ᵥ b) ^ 2) =
      ((a 0 * b 2 - a 2 * b 0) - (a 1 * b 3 - a 3 * b 1)) ^ 2 +
      ((a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1)) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_four, omega4]
    ring
  nlinarith [sq_nonneg ((a 0 * b 2 - a 2 * b 0) - (a 1 * b 3 - a 3 * b 1)),
    sq_nonneg ((a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1))]
-- @endregion

-- @region symplectic_geometry.dot_self_nonneg
-- @provenance independent
/-- `|a|² = ⟨a, a⟩ ≥ 0` in ℝ⁴: a sum of four squares. -/
theorem dot_self_nonneg (a : Fin 4 → ℝ) : 0 ≤ a ⬝ᵥ a := by
  simp only [dotProduct, Fin.sum_univ_four]
  nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1), mul_self_nonneg (a 2),
    mul_self_nonneg (a 3)]
-- @endregion

-- @region symplectic_geometry.exists_long_shadow
-- @provenance independent
/-- If `|a| ≥ 1`, the linear function `u ↦ ⟨a, u⟩` takes a value of size at least `r` on the
sphere of radius `r`: take `u = (r / |a|) a`, for which `⟨a, u⟩² = r² |a|² ≥ r²`. -/
theorem exists_long_shadow {a : Fin 4 → ℝ} (ha : 1 ≤ a ⬝ᵥ a) {r : ℝ} :
    ∃ u : Fin 4 → ℝ, u ⬝ᵥ u = r ^ 2 ∧ r ^ 2 ≤ (a ⬝ᵥ u) ^ 2 := by
  set s := Real.sqrt (a ⬝ᵥ a) with hs
  have hs2 : s ^ 2 = a ⬝ᵥ a := Real.sq_sqrt (by linarith)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  refine ⟨(r / s) • a, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hs2]
    field_simp
  · rw [dotProduct_smul, smul_eq_mul, mul_pow, div_pow, hs2]
    have h0 : 0 < a ⬝ᵥ a := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h0]
    nlinarith [mul_nonneg (sq_nonneg r) (mul_nonneg h0.le (sub_nonneg.mpr ha))]
-- @endregion

-- @region symplectic_geometry.linear_nonsqueezing
-- @provenance independent
/-- **Linear non-squeezing in ℝ⁴.** If a symplectic matrix `A` (here `A J Aᵀ = J`) maps the ball
`B⁴(r)` into the cylinder `Z(R) = {x₁² + y₁² ≤ R²}`, then `r ≤ R`. Proof: the first two rows
`a, b` of `A` satisfy `ω₀(a, b) = 1`, so by `wirtinger4` `|a|² |b|² ≥ 1` and one of them has
length at least `1`; `exists_long_shadow` then gives a point of `B⁴(r)` whose image lies at
distance at least `r` from the axis of the cylinder. Gromov's theorem says the same for all
symplectic *diffeomorphisms*; that needs pseudo-holomorphic curves and is not formalised. -/
theorem linear_nonsqueezing (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A * J4 * Aᵀ = J4)
    {r R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ u : Fin 4 → ℝ, u ⬝ᵥ u ≤ r ^ 2 → (A *ᵥ u) 0 ^ 2 + (A *ᵥ u) 1 ^ 2 ≤ R ^ 2) :
    r ≤ R := by
  -- the rows `a = A 0` and `b = A 1` satisfy `ω(a, b) = 1`
  have hab : omega4 (A 0) (A 1) = 1 := by
    rw [← mul_J4_mul_transpose_apply, hA]; simp [J4]
  have hw := wirtinger4 (A 0) (A 1)
  rw [hab] at hw
  have ha0 := dot_self_nonneg (A 0)
  have hb0 := dot_self_nonneg (A 1)
  -- one of the two rows has length at least one
  have hlong : 1 ≤ A 0 ⬝ᵥ A 0 ∨ 1 ≤ A 1 ⬝ᵥ A 1 := by
    rcases le_or_gt 1 (A 0 ⬝ᵥ A 0) with h | h
    · exact Or.inl h
    · rcases le_or_gt 1 (A 1 ⬝ᵥ A 1) with h' | h'
      · exact Or.inr h'
      · nlinarith [sq_nonneg (A 0 ⬝ᵥ A 1), mul_le_mul h.le h'.le hb0 zero_le_one]
  -- so some point of the ball lands at distance ≥ r from the axis
  have hr2 : r ^ 2 ≤ R ^ 2 := by
    rcases hlong with h | h
    · obtain ⟨u, hu, hshadow⟩ := exists_long_shadow h (r := r)
      have := hsub u hu.le
      simp only [mulVec] at this
      nlinarith [sq_nonneg (A 1 ⬝ᵥ u)]
    · obtain ⟨u, hu, hshadow⟩ := exists_long_shadow h (r := r)
      have := hsub u hu.le
      simp only [mulVec] at this
      nlinarith [sq_nonneg (A 0 ⬝ᵥ u)]
  nlinarith
-- @endregion

/-! ### A volume-preserving map that squeezes -/

-- @region symplectic_geometry.squeeze
-- @provenance definition
/-- The squeeze `(x₁, y₁, x₂, y₂) ↦ (x₁/2, y₁/2, 2x₂, 2y₂)`: it shrinks the first symplectic
plane and stretches the second. -/
noncomputable def squeeze : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1 / 2, 1 / 2, 2, 2]
-- @endregion

-- @region symplectic_geometry.squeeze_det
-- @provenance independent
/-- The squeeze preserves volume: `det = ½ · ½ · 2 · 2 = 1`. -/
theorem squeeze_det : squeeze.det = 1 := by
  simp [squeeze, Matrix.det_diagonal, Fin.prod_univ_four]
-- @endregion

-- @region symplectic_geometry.squeeze_not_symplectic
-- @provenance independent
/-- The squeeze is not symplectic: it multiplies `ω₀(e₁, e₂) = 1` by `¼`. -/
theorem squeeze_not_symplectic : squeeze * J4 * squeezeᵀ ≠ J4 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [squeeze, J4, Matrix.mul_apply, Fin.sum_univ_four] at this
  norm_num at this
-- @endregion

-- @region symplectic_geometry.squeeze_ball
-- @provenance independent
/-- The squeeze maps the unit ball `B⁴(1)` into the thin cylinder `Z(1/2)`. Together with
`linear_nonsqueezing` this shows that volume preservation is far weaker than being symplectic:
no symplectic matrix can do this. -/
theorem squeeze_ball (u : Fin 4 → ℝ) (hu : u ⬝ᵥ u ≤ 1) :
    (squeeze *ᵥ u) 0 ^ 2 + (squeeze *ᵥ u) 1 ^ 2 ≤ (1 / 2) ^ 2 := by
  simp only [squeeze, mulVec_diagonal]
  simp only [dotProduct, Fin.sum_univ_four] at hu
  simp
  nlinarith [sq_nonneg (u 2), sq_nonneg (u 3)]
-- @endregion

end Lumenary.SymplecticGeometry
