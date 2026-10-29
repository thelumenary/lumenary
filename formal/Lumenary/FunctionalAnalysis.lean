/-
The Lumenary — formal mathematics
Functional analysis: bounded operators, the Riesz representation theorem, the "big three"
theorems on Banach spaces, Hahn–Banach, non-compactness of the unit ball in infinite dimensions,
and the spectral theorem for compact self-adjoint operators.

Mathlib has all the theorems of a first course: `InnerProductSpace.toDual` (Fréchet–Riesz),
`banach_steinhaus`, `ContinuousLinearMap.isOpenMap` (open mapping),
`LinearMap.continuous_of_isClosed_graph`, `exists_extension_norm_eq` (Hahn–Banach),
`FiniteDimensional.of_isCompact_closedBall` (F. Riesz) and, for compact symmetric operators,
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. Proved here from more basic
facts: that a bounded linear map is continuous, the uniqueness half of the Riesz representation,
and that an orthonormal sequence has no Cauchy subsequence, so that the closed unit ball of a
Hilbert space with an infinite orthonormal sequence is not compact.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Topology.Sequences

open Filter Topology Metric
open scoped InnerProductSpace

namespace Lumenary.FunctionalAnalysis

/-! ### Bounded operators -/

-- @region functional_analysis.continuous_of_bound
-- @provenance independent
/-- **Bounded linear maps are continuous.** If `‖T x‖ ≤ C ‖x‖` for all `x`, then
`‖T y − T x‖ = ‖T (y − x)‖ ≤ C ‖y − x‖`, so `T` is (Lipschitz) continuous: given `ε > 0`,
take `δ = ε / (|C| + 1)`. (Mathlib: `LinearMap.continuous_of_bound`; the converse, that a
continuous linear map is bounded, is `ContinuousLinearMap.le_opNorm`.) -/
theorem continuous_of_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) (C : ℝ)
    (h : ∀ x, ‖T x‖ ≤ C * ‖x‖) : Continuous T := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hC : 0 < |C| + 1 := by positivity
  refine ⟨ε / (|C| + 1), by positivity, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  rw [← map_sub]
  calc ‖T (y - x)‖ ≤ C * ‖y - x‖ := h (y - x)
    _ ≤ (|C| + 1) * ‖y - x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith [le_abs_self C]
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left hy hC
    _ = ε := by field_simp
-- @endregion

/-! ### Hilbert spaces: the Riesz representation theorem -/

-- @region functional_analysis.riesz_representation
-- @provenance library
/-- **Riesz representation theorem** (Fréchet–Riesz). On a Hilbert space `E` over `𝕜 = ℝ` or `ℂ`,
every bounded linear functional `ℓ` is an inner product with a fixed vector:
`ℓ x = ⟪y, x⟫` for some `y`. (Mathlib's inner product is conjugate-linear in the *first*
slot.) This applies Mathlib's isometric equivalence `InnerProductSpace.toDual`. -/
theorem riesz_representation {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (ℓ : StrongDual 𝕜 E) :
    ∃ y : E, ∀ x, ℓ x = ⟪y, x⟫_𝕜 :=
  ⟨(InnerProductSpace.toDual 𝕜 E).symm ℓ, fun _ => InnerProductSpace.toDual_symm_apply.symm⟩
-- @endregion

-- @region functional_analysis.riesz_unique
-- @provenance independent
/-- **Uniqueness of the representing vector.** If `⟪y₁, x⟫ = ⟪y₂, x⟫` for every `x`, then
`y₁ = y₂`: take `x = y₁ − y₂` to get `⟪y₁ − y₂, y₁ − y₂⟫ = 0`, and an inner product is
definite. (This does not need completeness; existence does.) -/
theorem riesz_unique {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {y₁ y₂ : E} (h : ∀ x, ⟪y₁, x⟫_𝕜 = ⟪y₂, x⟫_𝕜) : y₁ = y₂ := by
  have h0 : ⟪y₁ - y₂, y₁ - y₂⟫_𝕜 = 0 := by
    rw [inner_sub_left, h (y₁ - y₂), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
-- @endregion

/-! ### The three pillars of Banach space theory, and Hahn–Banach -/

-- @region functional_analysis.uniform_boundedness
-- @provenance library
/-- **Uniform boundedness principle** (Banach–Steinhaus). A family of bounded operators on a
Banach space that is bounded at each point is bounded in operator norm. Proved in Mathlib
(`banach_steinhaus`) from the Baire category theorem, as in the lesson. -/
theorem uniform_boundedness {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {T : ι → E →L[ℝ] F}
    (h : ∀ x, ∃ C, ∀ i, ‖T i x‖ ≤ C) : ∃ C', ∀ i, ‖T i‖ ≤ C' :=
  banach_steinhaus h
-- @endregion

-- @region functional_analysis.open_mapping
-- @provenance library
/-- **Open mapping theorem** (Banach–Schauder). A surjective bounded operator between Banach
spaces maps open sets to open sets. This is Mathlib's `ContinuousLinearMap.isOpenMap`. -/
theorem open_mapping {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : IsOpenMap T :=
  T.isOpenMap hT
-- @endregion

-- @region functional_analysis.closed_graph
-- @provenance library
/-- **Closed graph theorem.** A linear map between Banach spaces whose graph is closed in
`E × F` is continuous. This is Mathlib's `LinearMap.continuous_of_isClosed_graph`. -/
theorem closed_graph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →ₗ[ℝ] F)
    (hT : IsClosed (T.graph : Set (E × F))) : Continuous T :=
  T.continuous_of_isClosed_graph hT
-- @endregion

-- @region functional_analysis.hahn_banach
-- @provenance library
/-- **Hahn–Banach theorem** (normed version). A bounded linear functional on a subspace extends
to the whole space *with the same norm*. Mathlib proves it (`exists_extension_norm_eq`) from
the sublinear-functional version, which uses Zorn's lemma. -/
theorem hahn_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : Subspace ℝ E)
    (f : StrongDual ℝ p) : ∃ g : StrongDual ℝ E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f
-- @endregion

/-! ### The unit ball in infinite dimensions -/

-- @region functional_analysis.orthonormal_dist_sq
-- @provenance independent
/-- Distinct members of an orthonormal family are at distance `√2`:
`‖eᵢ − eⱼ‖² = ‖eᵢ‖² − 2⟪eᵢ, eⱼ⟫ + ‖eⱼ‖² = 1 − 0 + 1 = 2` (Pythagoras). -/
theorem orthonormal_dist_sq {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ι → E} (he : Orthonormal ℝ e) {i j : ι} (hij : i ≠ j) : ‖e i - e j‖ ^ 2 = 2 := by
  rw [norm_sub_sq_real, he.1 i, he.1 j, he.2 hij]
  norm_num
-- @endregion

-- @region functional_analysis.closed_ball_not_compact
-- @provenance independent
/-- **The closed unit ball of an infinite-dimensional Hilbert space is not compact.** If `E` has
an orthonormal sequence `e₀, e₁, …` (every infinite-dimensional Hilbert space does, by
Gram–Schmidt), the `eₙ` lie in the closed unit ball but no subsequence is Cauchy, because
distinct terms are `√2 > 1` apart. A compact metric space would contain a convergent, hence
Cauchy, subsequence. -/
theorem closedBall_not_compact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : ℕ → E} (he : Orthonormal ℝ e) : ¬ IsCompact (closedBall (0 : E) 1) := by
  intro hK
  have hmem : ∀ n, e n ∈ closedBall (0 : E) 1 := fun n => by
    rw [mem_closedBall, dist_zero_right, he.1 n]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  -- A convergent sequence is Cauchy: eventually all terms are within `1` of each other.
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have hlt : dist (e (φ (N + 1))) (e (φ N)) < 1 := hN (N + 1) (Nat.le_succ N)
  have hne : φ (N + 1) ≠ φ N := (hφ (Nat.lt_succ_self N)).ne'
  have h2 := orthonormal_dist_sq he hne
  rw [dist_eq_norm] at hlt
  nlinarith [norm_nonneg (e (φ (N + 1)) - e (φ N))]
-- @endregion

-- @region functional_analysis.riesz_compact_ball
-- @provenance library
/-- **F. Riesz's theorem.** Conversely, in any normed space, a compact closed ball of positive
radius forces finite dimension. This is Mathlib's `FiniteDimensional.of_isCompact_closedBall`,
proved from Riesz's lemma. -/
theorem riesz_compact_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ}
    (hr : 0 < r) (h : IsCompact (closedBall (0 : E) r)) : FiniteDimensional ℝ E :=
  FiniteDimensional.of_isCompact_closedBall ℝ hr h
-- @endregion

/-! ### The spectral theorem for compact self-adjoint operators -/

-- @region functional_analysis.spectral_compact_symmetric
-- @provenance library
/-- **Spectral theorem for compact self-adjoint operators**, completeness part. For a compact
symmetric operator `T` on a Hilbert space, the eigenspaces span a dense subspace: the orthogonal
complement of their span is `0`. Choosing an orthonormal basis of each (finite-dimensional, for
non-zero eigenvalues) eigenspace gives an orthonormal basis of eigenvectors. This is Mathlib's
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. -/
theorem spectral_compact_symmetric {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ :=
  T.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT'
-- @endregion

-- @region functional_analysis.eigenspace_finite_dimensional
-- @provenance library
/-- The eigenspace of a compact operator for a non-zero eigenvalue is finite-dimensional
(its unit ball is the image of a bounded set under `μ⁻¹ T`, hence compact). This is Mathlib's
`ContinuousLinearMap.finite_dimensional_eigenspace`. -/
theorem eigenspace_finite_dimensional {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (μ : 𝕜) (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (Module.End.eigenspace T.toLinearMap μ) :=
  T.finite_dimensional_eigenspace hT μ hμ
-- @endregion

end Lumenary.FunctionalAnalysis
