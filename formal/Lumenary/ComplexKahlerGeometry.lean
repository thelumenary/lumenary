/-
The Lumenary — formal mathematics
Complex and Kähler geometry: the compatible triple (metric, complex structure, Kähler form) at a
point, the combinatorial core of "odd Betti numbers of compact Kähler manifolds are even", the
Hodge numbers of complex tori, and the rigidity of holomorphic functions on compact manifolds.

What is proved here and what Mathlib provides. On a complex inner product space (a tangent space
of a Hermitian manifold, with Mathlib's convention that `inner ℂ u v` is conjugate-linear in `u`)
the *independent* declarations define the Riemannian metric `g = Re h` and the fundamental form
`ω = Im h` of the Hermitian form `h`, and prove `ω(u, v) = g(Ju, v)` with `J = i·`, that `J` is an
isometry preserving `ω`, that `ω` is alternating, and that it is non-degenerate because
`ω(u, Ju) = |u|²`. They also prove that a symmetric array of Hodge numbers has even sums along odd
antidiagonals, the arithmetic step from Hodge symmetry to "b_odd is even", and its consequence for
the Hopf surface. The *library* declarations apply Vandermonde's identity (`Nat.add_choose_eq`,
the Hodge numbers of a complex torus add up to its Betti numbers) and Mathlib's theorem that a
holomorphic function on a compact connected complex manifold is constant
(`MDifferentiable.apply_eq_of_compactSpace`). Not formalised: Kähler manifolds themselves, the
Dolbeault complex, harmonic forms and the Hodge decomposition (Mathlib has complex manifolds but no
Hodge theory yet), Yau's theorem, and of course the Hodge conjecture.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals

namespace Lumenary.ComplexKahlerGeometry

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The compatible triple at a point -/

-- @region complex_kahler_geometry.metric
-- @provenance definition
/-- The Riemannian metric `g(u, v) = Re h(u, v)` underlying a Hermitian inner product `h`. -/
noncomputable def metric (u v : E) : ℝ := (inner ℂ u v).re
-- @endregion

-- @region complex_kahler_geometry.kahler_form
-- @provenance definition
/-- The fundamental (Kähler) form `ω(u, v) = Im h(u, v)` of a Hermitian inner product `h`. On `ℂ`
with `h(u, v) = conj(u) v` it is `dx ∧ dy`: `ω(1, i) = Im(i) = 1`. -/
noncomputable def kahlerForm (u v : E) : ℝ := (inner ℂ u v).im
-- @endregion

-- @region complex_kahler_geometry.kahler_form_eq_metric_j
-- @provenance independent
/-- **The triple is compatible**: `ω(u, v) = g(Ju, v)` with `J = i·`. Proof:
`h(iu, v) = conj(i) h(u, v) = -i h(u, v)`, and `Re(-i z) = Im z`. -/
theorem kahler_form_eq_metric_J (u v : E) :
    kahlerForm u v = metric (Complex.I • u) v := by
  simp [kahlerForm, metric, inner_smul_left]
-- @endregion

-- @region complex_kahler_geometry.metric_j_invariant
-- @provenance independent
/-- The complex structure is an isometry: `g(Ju, Jv) = g(u, v)`, because
`h(iu, iv) = conj(i) · i · h(u, v) = h(u, v)`. -/
theorem metric_J_invariant (u v : E) :
    metric (Complex.I • u) (Complex.I • v) = metric u v := by
  simp [metric, inner_smul_left, inner_smul_right, ← mul_assoc]
-- @endregion

-- @region complex_kahler_geometry.kahler_form_j_invariant
-- @provenance independent
/-- The Kähler form is `J`-invariant: `ω(Ju, Jv) = ω(u, v)`. So `ω` has type `(1, 1)`. -/
theorem kahler_form_J_invariant (u v : E) :
    kahlerForm (Complex.I • u) (Complex.I • v) = kahlerForm u v := by
  simp [kahlerForm, inner_smul_left, inner_smul_right, ← mul_assoc]
-- @endregion

-- @region complex_kahler_geometry.kahler_form_antisymm
-- @provenance independent
/-- The Kähler form is skew: `ω(v, u) = -ω(u, v)`, because `h(v, u) = conj h(u, v)` and
conjugation negates imaginary parts. -/
theorem kahler_form_antisymm (u v : E) : kahlerForm v u = -kahlerForm u v := by
  rw [kahlerForm, kahlerForm, ← inner_conj_symm u v, Complex.conj_im, neg_neg]
-- @endregion

-- @region complex_kahler_geometry.kahler_form_self
-- @provenance independent
/-- The Kähler form is alternating: `ω(u, u) = 0`. (Solution of the Lean exercise: it follows
from skew-symmetry, since a real number equal to its negative is zero.) -/
theorem kahler_form_self (u : E) : kahlerForm u u = 0 := by
  have h := kahler_form_antisymm u u
  linarith
-- @endregion

-- @region complex_kahler_geometry.kahler_form_j_self
-- @provenance independent
/-- **Taming**: `ω(u, Ju) = |u|²`. The Kähler form is positive on every complex line, which is
why complex submanifolds of a Kähler manifold are volume-minimising and have positive volume. -/
theorem kahler_form_J_self (u : E) : kahlerForm u (Complex.I • u) = ‖u‖ ^ 2 := by
  simp [kahlerForm, inner_smul_right, inner_self_eq_norm_sq_to_K]
  norm_cast
-- @endregion

-- @region complex_kahler_geometry.kahler_form_nondegenerate
-- @provenance independent
/-- The Kähler form is non-degenerate: if `ω(u, v) = 0` for all `v`, then
`|u|² = ω(u, Ju) = 0`. With closedness (`dω = 0`, the Kähler condition) this makes every Kähler
manifold symplectic. -/
theorem kahler_form_nondegenerate {u : E} (h : ∀ v, kahlerForm u v = 0) : u = 0 := by
  have := h (Complex.I • u)
  rw [kahler_form_J_self] at this
  simpa using this
-- @endregion

/-! ### Hodge symmetry and Betti numbers -/

-- @region complex_kahler_geometry.odd_betti_even
-- @provenance independent
/-- **The arithmetic behind "odd Betti numbers are even".** If `h p q = h q p` (Hodge symmetry),
then for odd `k = 2m + 1` the sum `b_k = ∑_{p + q = k} h^{p,q}` is even: split the sum at the middle
and reflect the second half, `p ↦ k - p`, which has no fixed point when `k` is odd. On a compact
Kähler manifold the Hodge decomposition gives `b_k = ∑_{p+q=k} h^{p,q}`; that analytic input is not
formalised. -/
theorem odd_betti_even {h : ℕ → ℕ → ℕ} (hs : ∀ p q, h p q = h q p) (m : ℕ) :
    Even (∑ p ∈ range (2 * m + 2), h p (2 * m + 1 - p)) := by
  set f : ℕ → ℕ := fun p => h p (2 * m + 1 - p) with hf
  have hsplit : ∑ p ∈ range (2 * m + 2), f p =
      ∑ p ∈ range (m + 1), f p + ∑ p ∈ range (m + 1), f (m + 1 + p) := by
    rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, Finset.sum_range_add]
  have hrefl : ∑ p ∈ range (m + 1), f (m + 1 + p) = ∑ p ∈ range (m + 1), f p := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < m + 1 := mem_range.mp hp
    simp only [hf]
    rw [hs]
    congr 1 <;> omega
  rw [hsplit, hrefl]
  exact ⟨_, rfl⟩
-- @endregion

-- @region complex_kahler_geometry.hopf_obstruction
-- @provenance independent
/-- **Why the Hopf surface is not Kähler.** With Hodge symmetry, `b₁ = h^{1,0} + h^{0,1}` is twice
`h^{1,0}`, so it can never be `1`. The Hopf surface `S¹ × S³` has `b₁ = 1`. -/
theorem hopf_obstruction {h : ℕ → ℕ → ℕ} (hs : ∀ p q, h p q = h q p) :
    h 1 0 + h 0 1 ≠ 1 := by
  rw [hs 1 0]
  omega
-- @endregion

-- @region complex_kahler_geometry.torus_betti
-- @provenance library
/-- **Hodge numbers of a complex torus.** For `X = ℂⁿ/Λ`, `h^{p,q} = C(n, p) C(n, q)` (translation-
invariant forms `dz_I ∧ dz̄_J`), and they add up to the Betti numbers `b_k = C(2n, k)` of the real
torus `T^{2n}`: `C(n + n, k) = ∑_{p + q = k} C(n, p) C(n, q)`. This applies Mathlib's Vandermonde
identity `Nat.add_choose_eq`. -/
theorem torus_betti (n k : ℕ) :
    (n + n).choose k = ∑ pq ∈ antidiagonal k, n.choose pq.1 * n.choose pq.2 :=
  Nat.add_choose_eq n n k
-- @endregion

/-! ### Holomorphic functions on compact complex manifolds -/

-- @region complex_kahler_geometry.holomorphic_const_of_compact
-- @provenance library
/-- **Holomorphic functions on a compact connected complex manifold are constant** (maximum
modulus principle). This is why complex geometry studies sections of line bundles, sheaves and
forms instead of functions. It applies Mathlib's `MDifferentiable.apply_eq_of_compactSpace`;
`MDifferentiable I 𝓘(ℂ, F) f` is holomorphy for a manifold modelled on `I`. -/
theorem holomorphic_const_of_compact {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E' H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [CompactSpace M] [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I (modelWithCornersSelf ℂ F) f) (a b : M) : f a = f b :=
  hf.apply_eq_of_compactSpace a b
-- @endregion

end Lumenary.ComplexKahlerGeometry
