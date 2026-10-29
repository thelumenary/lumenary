/-
The Lumenary — formal mathematics
Mathematical foundations of quantum mechanics: observables as symmetric operators, the
uncertainty relation, ladder operators, and why the canonical commutation relation needs
unbounded operators.

Mathlib has inner product spaces, symmetric (self-adjoint) operators and the spectral theorem in
finite dimensions (real eigenvalues, an orthonormal basis of eigenvectors), C*-algebras and the
exponential map from self-adjoint to unitary elements. It does not yet have unbounded
self-adjoint operators, the spectral theorem for them, or Stone's theorem. Proved here from more
basic facts: that expectation values of symmetric operators are real and that eigenvectors for
different eigenvalues are orthogonal; the Robertson–Heisenberg uncertainty inequality; the
commutator algebra of the harmonic oscillator's ladder operators and the positivity of the number
operator; and two no-go theorems — no matrices (trace argument) and no bounded operators
(Wintner–Wielandt) satisfy `[X, P] = iℏ`.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped InnerProductSpace ComplexConjugate

namespace Lumenary.QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Observables: real expectations, real eigenvalues, orthogonal eigenvectors -/

-- @region quantum_mechanics.expectation_real
-- @provenance independent
/-- **Expectation values of observables are real.** If `A` is symmetric (`⟪A x, y⟫ = ⟪x, A y⟫`),
then `⟪ψ, A ψ⟫` equals its own complex conjugate. Proof: `conj ⟪ψ, Aψ⟫ = ⟪Aψ, ψ⟫ = ⟪ψ, Aψ⟫`, by
conjugate symmetry of the inner product and then symmetry of `A`. -/
theorem expectation_real {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    conj ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := by
  rw [inner_conj_symm, hA]
-- @endregion

-- @region quantum_mechanics.eigenvalue_real
-- @provenance library
/-- **Eigenvalues of a symmetric operator are real** (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`):
measured values of an observable are real numbers. -/
theorem eigenvalue_real {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {ev : ℂ}
    (h : Module.End.HasEigenvalue A ev) : conj ev = ev :=
  hA.conj_eigenvalue_eq_self h
-- @endregion

-- @region quantum_mechanics.eigenvectors_orthogonal
-- @provenance independent
/-- **Eigenvectors of an observable for different eigenvalues are orthogonal.** If `A v = λ v`
and `A w = μ w` with real `λ ≠ μ`, then `⟪v, w⟫ = 0`. Proof:
`λ ⟪v, w⟫ = ⟪A v, w⟫ = ⟪v, A w⟫ = μ ⟪v, w⟫`, so `(λ − μ) ⟪v, w⟫ = 0`. Distinct measurement
outcomes are perfectly distinguishable states. -/
theorem eigenvectors_orthogonal {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {v w : E} {lv lw : ℝ}
    (hv : A v = (lv : ℂ) • v) (hw : A w = (lw : ℂ) • w) (hne : lv ≠ lw) : ⟪v, w⟫_ℂ = 0 := by
  have h := hA v w
  rw [hv, hw, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h' : ((lv : ℂ) - lw) * ⟪v, w⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h0) hne
  · exact h0
-- @endregion

-- @region quantum_mechanics.spectral_theorem_finite
-- @provenance library
/-- **The spectral theorem in finite dimensions.** A symmetric operator on an `n`-dimensional
complex inner product space has an orthonormal basis `e₀, …, e_{n−1}` of eigenvectors with real
eigenvalues `λᵢ`: `A eᵢ = λᵢ eᵢ`. In a state `ψ`, a measurement of `A` gives `λᵢ` with probability
`|⟪eᵢ, ψ⟫|²` (Born's rule). This is Mathlib's `LinearMap.IsSymmetric.apply_eigenvectorBasis`. -/
theorem spectral_theorem_finite [FiniteDimensional ℂ E] {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℂ E = n) (i : Fin n) :
    A (hA.eigenvectorBasis hn i) = (hA.eigenvalues hn i : ℂ) • hA.eigenvectorBasis hn i :=
  hA.apply_eigenvectorBasis hn i
-- @endregion

/-! ### The uncertainty relation -/

-- @region quantum_mechanics.robertson
-- @provenance independent
/-- **Robertson's inequality, core estimate.** For symmetric `A, B` and any vector `ψ`,
`|⟪ψ, [A, B] ψ⟫| ≤ 2 ‖Aψ‖ ‖Bψ‖`, where `[A, B] = AB − BA`. Proof: by symmetry
`⟪ψ, ABψ⟫ = ⟪Aψ, Bψ⟫` and `⟪ψ, BAψ⟫ = ⟪Bψ, Aψ⟫`; then the triangle inequality and the
Cauchy–Schwarz inequality `|⟪u, v⟫| ≤ ‖u‖ ‖v‖`. -/
theorem robertson {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) :
    ‖⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ‖ ≤ 2 * ‖A ψ‖ * ‖B ψ‖ := by
  have h1 : ⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ - ⟪B ψ, A ψ⟫_ℂ := by
    rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply, LinearMap.comp_apply,
      ← hA ψ (B ψ), ← hB ψ (A ψ)]
  rw [h1]
  calc ‖⟪A ψ, B ψ⟫_ℂ - ⟪B ψ, A ψ⟫_ℂ‖ ≤ ‖⟪A ψ, B ψ⟫_ℂ‖ + ‖⟪B ψ, A ψ⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖A ψ‖ * ‖B ψ‖ + ‖B ψ‖ * ‖A ψ‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = 2 * ‖A ψ‖ * ‖B ψ‖ := by ring
-- @endregion

-- @region quantum_mechanics.uncertainty
-- @provenance independent
/-- **The Robertson–Heisenberg uncertainty relation.** For symmetric `A, B`, any `ψ` and any real
numbers `a, b`: `½ |⟪ψ, [A, B] ψ⟫| ≤ ‖(A − a)ψ‖ · ‖(B − b)ψ‖`. For a unit vector `ψ` and
`a = ⟨A⟩ = ⟪ψ, Aψ⟫`, `b = ⟨B⟩`, the right side is the product of standard deviations `σ_A σ_B`.
Proof: shifting by real scalars does not change the commutator, and the shifted operators are
still symmetric; the cross terms `a ⟪ψ, Bψ⟫` and `b ⟪Aψ, ψ⟫` cancel in pairs, leaving
`⟪Aψ, Bψ⟫ − ⟪Bψ, Aψ⟫`, which is bounded as in `robertson`. -/
theorem uncertainty {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E)
    (a b : ℝ) :
    ‖⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ‖ / 2 ≤ ‖A ψ - (a : ℂ) • ψ‖ * ‖B ψ - (b : ℂ) • ψ‖ := by
  set u := A ψ - (a : ℂ) • ψ
  set w := B ψ - (b : ℂ) • ψ
  have hAψ : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA ψ ψ
  have hBψ : ⟪B ψ, ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ := hB ψ ψ
  have h1 : ⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ = ⟪u, w⟫_ℂ - ⟪w, u⟫_ℂ := by
    simp only [u, w, LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right, inner_sub_left,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← hA ψ (B ψ), ← hB ψ (A ψ), hAψ,
      hBψ]
    ring
  rw [h1]
  have h2 : ‖⟪u, w⟫_ℂ - ⟪w, u⟫_ℂ‖ ≤ 2 * (‖u‖ * ‖w‖) :=
    calc ‖⟪u, w⟫_ℂ - ⟪w, u⟫_ℂ‖ ≤ ‖⟪u, w⟫_ℂ‖ + ‖⟪w, u⟫_ℂ‖ := norm_sub_le _ _
      _ ≤ ‖u‖ * ‖w‖ + ‖w‖ * ‖u‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ = 2 * (‖u‖ * ‖w‖) := by ring
  linarith
-- @endregion

/-! ### The harmonic oscillator: ladder operators -/

-- @region quantum_mechanics.number_raise
-- @provenance independent
/-- **The number operator raises with the creation operator.** In any ring, if `a a† − a† a = 1`
and `N = a† a`, then `N a† − a† N = a†`. Proof: `N a† − a† N = a† (a a† − a† a) = a†`. -/
theorem number_raise {R : Type*} [Ring R] (a ad : R) (h : a * ad - ad * a = 1) :
    (ad * a) * ad - ad * (ad * a) = ad :=
  calc (ad * a) * ad - ad * (ad * a) = ad * (a * ad - ad * a) := by noncomm_ring
    _ = ad := by rw [h, mul_one]
-- @endregion

-- @region quantum_mechanics.number_lower
-- @provenance independent
/-- **…and lowers with the annihilation operator:** `N a − a N = −a`, because
`N a − a N = −(a a† − a† a) a`. -/
theorem number_lower {R : Type*} [Ring R] (a ad : R) (h : a * ad - ad * a = 1) :
    (ad * a) * a - a * (ad * a) = -a :=
  calc (ad * a) * a - a * (ad * a) = -((a * ad - ad * a) * a) := by noncomm_ring
    _ = -a := by rw [h, one_mul]
-- @endregion

-- @region quantum_mechanics.raise_eigenvector
-- @provenance independent
/-- **Ladder operators move between eigenvectors.** If `a a† − a† a = 1` on a complex vector space
and `N v = λ v` for `N = a† a`, then `N (a† v) = (λ + 1) a† v` and `N (a v) = (λ − 1) a v`. Each
application of `a†` adds one quantum `ℏω` of energy and each application of `a` removes one. -/
theorem raise_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V] (a ad : Module.End ℂ V)
    (h : a * ad - ad * a = 1) {v : V} {l : ℂ} (hv : (ad * a) v = l • v) :
    (ad * a) (ad v) = (l + 1) • ad v ∧ (ad * a) (a v) = (l - 1) • a v := by
  have hv' : ad (a v) = l • v := by simpa only [Module.End.mul_apply] using hv
  have hr := congrArg (fun T : Module.End ℂ V => T v) (number_raise a ad h)
  have hl := congrArg (fun T : Module.End ℂ V => T v) (number_lower a ad h)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] at hr hl
  rw [hv', map_smul] at hr hl
  simp only [Module.End.mul_apply]
  rw [sub_eq_iff_eq_add] at hr hl
  constructor
  · rw [hr, add_smul, one_smul]
    abel
  · rw [hl, sub_smul, one_smul]
    abel
-- @endregion

-- @region quantum_mechanics.number_nonneg
-- @provenance independent
/-- **The number operator is positive, so the ladder must stop.** If `a†` is the adjoint of `a`
(`⟪a† x, y⟫ = ⟪x, a y⟫`), then `⟪v, a† a v⟫ = ‖a v‖²`. Hence an eigenvalue `λ` of `N = a† a` with
eigenvector `v ≠ 0` satisfies `λ ‖v‖² = ‖a v‖² ≥ 0`: repeated lowering must end at a vector with
`a v₀ = 0`, the ground state, and the eigenvalues of `N` are `0, 1, 2, …`. -/
theorem number_nonneg (a ad : E →ₗ[ℂ] E) (hadj : ∀ x y, ⟪ad x, y⟫_ℂ = ⟪x, a y⟫_ℂ) (v : E) :
    ⟪v, ad (a v)⟫_ℂ = ((‖a v‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_conj_symm, hadj, inner_self_eq_norm_sq_to_K]
  simp
-- @endregion

/-! ### The canonical commutation relation needs unbounded operators -/

-- @region quantum_mechanics.no_finite_ccr
-- @provenance independent
/-- **No matrices satisfy `[X, P] = c · 1` with `c ≠ 0`.** Taking traces: `tr(XP) = tr(PX)`, so the
left side has trace `0`, while `tr(c · 1) = c n ≠ 0` for `n ≥ 1`. Hence position and momentum
(`[X, P] = iℏ`) cannot be represented on a finite-dimensional Hilbert space. -/
theorem no_finite_ccr {n : ℕ} (hn : 0 < n) (X P : Matrix (Fin n) (Fin n) ℂ) {c : ℂ}
    (hc : c ≠ 0) : X * P - P * X ≠ c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at ht
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact mul_ne_zero hc hn' ht.symm
-- @endregion

-- @region quantum_mechanics.wintner_wielandt
-- @provenance independent
/-- **The Wintner–Wielandt theorem.** In a nontrivial normed algebra (for example the bounded
operators on a nonzero Banach space), no elements satisfy `x p − p x = c · 1` with `c ≠ 0`.
Wielandt's proof: by induction `x pⁿ⁺¹ − pⁿ⁺¹ x = (n + 1) c pⁿ`; hence no power of `p` vanishes
(otherwise the next lower one would too, down to `p⁰ = 1`); taking norms,
`(n + 1) |c| ‖pⁿ‖ ≤ 2 ‖x‖ ‖p‖ ‖pⁿ‖`, so `(n + 1) |c| ≤ 2 ‖x‖ ‖p‖` for every `n`, which is absurd. -/
theorem wintner_wielandt {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [Nontrivial A]
    (x p : A) {c : ℂ} (hc : c ≠ 0) : x * p - p * x ≠ c • (1 : A) := by
  intro h
  -- The commutator with a power of `p`.
  have key : ∀ n : ℕ, x * p ^ (n + 1) - p ^ (n + 1) * x = (((n : ℂ) + 1) * c) • p ^ n := by
    intro n
    induction n with
    | zero => simp [h]
    | succ n ih =>
      have e : x * p ^ (n + 1 + 1) - p ^ (n + 1 + 1) * x =
          (x * p ^ (n + 1) - p ^ (n + 1) * x) * p + p ^ (n + 1) * (x * p - p * x) := by
        rw [pow_succ p (n + 1)]
        noncomm_ring
      rw [e, ih, h, smul_mul_assoc, mul_smul_comm, mul_one, ← pow_succ, ← add_smul]
      congr 1
      push_cast
      ring
  -- No power of `p` is zero.
  have hne : ∀ n : ℕ, p ^ n ≠ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hp
      have hk := key n
      rw [hp, mul_zero, zero_mul, sub_zero] at hk
      have hcoef : ((n : ℂ) + 1) * c ≠ 0 := mul_ne_zero (by exact_mod_cast n.succ_ne_zero) hc
      exact ih ((smul_eq_zero.mp hk.symm).resolve_left hcoef)
  -- The norm estimate.
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * ‖c‖ ≤ 2 * ‖x‖ * ‖p‖ := by
    intro n
    have hpos : 0 < ‖p ^ n‖ := norm_pos_iff.mpr (hne n)
    have hp1 : ‖p ^ (n + 1)‖ ≤ ‖p ^ n‖ * ‖p‖ := by rw [pow_succ]; exact norm_mul_le _ _
    have hlhs : ‖(((n : ℂ) + 1) * c) • p ^ n‖ = ((n : ℝ) + 1) * ‖c‖ * ‖p ^ n‖ := by
      rw [norm_smul, norm_mul]
      congr 2
      exact_mod_cast Complex.norm_natCast (n + 1)
    have hrhs : ‖x * p ^ (n + 1) - p ^ (n + 1) * x‖ ≤ 2 * ‖x‖ * ‖p‖ * ‖p ^ n‖ :=
      calc ‖x * p ^ (n + 1) - p ^ (n + 1) * x‖
          ≤ ‖x * p ^ (n + 1)‖ + ‖p ^ (n + 1) * x‖ := norm_sub_le _ _
        _ ≤ ‖x‖ * ‖p ^ (n + 1)‖ + ‖p ^ (n + 1)‖ * ‖x‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ‖x‖ * (‖p ^ n‖ * ‖p‖) + (‖p ^ n‖ * ‖p‖) * ‖x‖ := by gcongr
        _ = 2 * ‖x‖ * ‖p‖ * ‖p ^ n‖ := by ring
    rw [key n, hlhs] at hrhs
    exact le_of_mul_le_mul_right hrhs hpos
  -- Contradiction with the Archimedean property.
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖x‖ * ‖p‖ / ‖c‖)
  rw [div_lt_iff₀ hcpos] at hn
  have := hbound n
  nlinarith
-- @endregion

-- @region quantum_mechanics.no_bounded_ccr
-- @provenance independent
/-- **Position and momentum cannot both be bounded.** On a nonzero complex normed space there
are no bounded operators `X, P` with `XP − PX = iℏ · 1` for `ℏ ≠ 0`. This is Wintner–Wielandt
applied to the normed algebra of bounded operators; so at least one of `X, P` is unbounded, and
then (by the Hellinger–Toeplitz theorem) it cannot be defined on the whole Hilbert space. -/
theorem no_bounded_ccr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (X P : F →L[ℂ] F) {ℏ : ℝ} (hℏ : ℏ ≠ 0) :
    X * P - P * X ≠ (Complex.I * ℏ) • (1 : F →L[ℂ] F) :=
  wintner_wielandt X P (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hℏ))
-- @endregion

/-! ### Time evolution -/

-- @region quantum_mechanics.evolution_group
-- @provenance library
/-- **Time evolution is a one-parameter unitary group** (bounded case). For a self-adjoint
element `H` of a C*-algebra (e.g. a Hermitian matrix), `U(t) = exp(i t H)` is unitary
(`selfAdjoint.expUnitary`) and `U(s + t) = U(s) U(t)`, because `sH` and `tH` commute
(`Commute.expUnitary_add`). The physicists' `e^{−itH/ℏ}` is `U(−t/ℏ)`. Stone's theorem — every
strongly continuous unitary group arises this way from a possibly unbounded self-adjoint
generator — is not yet in Mathlib. -/
theorem evolution_group {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
    [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A] (H : selfAdjoint A) (s t : ℝ) :
    selfAdjoint.expUnitary ((s + t) • H) =
      selfAdjoint.expUnitary (s • H) * selfAdjoint.expUnitary (t • H) := by
  rw [add_smul]
  exact Commute.expUnitary_add (((Commute.refl (H : A)).smul_left s).smul_right t)
-- @endregion

end Lumenary.QuantumMechanics
