/-
The Lumenary — formal mathematics
Vector bundles and characteristic classes: the Möbius line bundle has no nowhere-zero section,
odd-dimensional spheres carry a nowhere-zero tangent vector field, `S³` is parallelisable, and
the mod-2 polynomial arithmetic behind the Stiefel–Whitney classes of projective spaces.

What is proved here and what Mathlib provides. Mathlib has fibre bundles and topological vector
bundles (`FiberBundle`, `VectorBundle`, trivialisations), the trivial bundle, pullbacks, fibrewise
products (Whitney sums) and the tangent bundle of a manifold. The *library* declarations cite
these instances, and the Frobenius identity `(a + b)^(2^k) = a^(2^k) + b^(2^k)` in characteristic
two. The *independent* declarations prove: a continuous section of the Möbius bundle, written as
an antiperiodic function `s(t + 1) = -s(t)`, must vanish somewhere (so the bundle is not
trivial); the field `v(z) = i z` is tangent to every odd-dimensional sphere and never zero; three
explicit tangent fields on `S³ ⊂ ℝ⁴` are orthonormal at every point; and the total Stiefel–Whitney
class `(1 + a)³` of `ℝP²` is `1 + a + a²` (given `a³ = 0`).

Not formalised here: Stiefel–Whitney and Chern classes themselves (Mathlib has no singular
cohomology ring yet), classifying spaces, the identification of the sections of the Möbius bundle
with antiperiodic functions (done on paper in the lesson), the hairy ball theorem, Chern–Weil
theory and the Gauss–Bonnet–Chern theorem.
-/
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic

namespace Lumenary.VectorBundlesCharacteristicClasses

/-! ### The Möbius line bundle -/

-- @region vector_bundles_characteristic_classes.mobius_section_vanishes
-- @provenance independent
/-- **Every section of the Möbius bundle vanishes somewhere.** The Möbius line bundle over
`S¹ = ℝ/ℤ` is the quotient of `ℝ × ℝ` by `(t, v) ~ (t + 1, -v)`, so its continuous sections are
the continuous functions with `s(t + 1) = -s(t)`. Then `s(0)` and `s(1) = -s(0)` have opposite
signs (or vanish), and the intermediate value theorem gives a zero in `[0, 1]`. -/
theorem mobius_section_vanishes (s : ℝ → ℝ) (hs : Continuous s) (anti : ∀ t, s (t + 1) = -s t) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, s t = 0 := by
  have h1 : s 1 = -s 0 := by simpa using anti 0
  rcases le_total (s 0) 0 with h0 | h0
  · -- `s 0 ≤ 0 ≤ s 1`
    exact intermediate_value_Icc zero_le_one hs.continuousOn ⟨h0, by linarith⟩
  · -- `s 1 ≤ 0 ≤ s 0`
    exact intermediate_value_Icc' zero_le_one hs.continuousOn ⟨by linarith, h0⟩
-- @endregion

-- @region vector_bundles_characteristic_classes.mobius_not_trivial
-- @provenance independent
/-- **The Möbius bundle is not trivial.** A trivial line bundle `S¹ × ℝ` has the nowhere-zero
section `t ↦ 1`; the Möbius bundle has no nowhere-zero section at all. (Contrast: the constant
function `1` is periodic, `s(t + 1) = s(t)`, i.e. a section of the trivial bundle.) -/
theorem mobius_not_trivial :
    ¬ ∃ s : ℝ → ℝ, Continuous s ∧ (∀ t, s (t + 1) = -s t) ∧ ∀ t, s t ≠ 0 := by
  rintro ⟨s, hs, anti, hne⟩
  obtain ⟨t, -, ht⟩ := mobius_section_vanishes s hs anti
  exact hne t ht
-- @endregion

/-! ### Vector fields on spheres -/

open ComplexConjugate

-- @region vector_bundles_characteristic_classes.re_inner
-- @provenance definition
/-- The real (Euclidean) inner product on `ℂⁿ = ℝ²ⁿ`: `⟨z, w⟩ = Σₖ Re(z̄ₖ wₖ)`. -/
def reInner {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  ∑ k, (conj (z k) * w k).re
-- @endregion

-- @region vector_bundles_characteristic_classes.odd_sphere_vector_field
-- @provenance independent
/-- **Odd-dimensional spheres can be combed.** On `S²ⁿ⁻¹ ⊂ ℂⁿ` the field `v(z) = i z` is tangent
(`⟨z, i z⟩ = 0`) and has the same length as `z`, so it never vanishes on the sphere. In real
coordinates it is `(x₁, y₁, …) ↦ (-y₁, x₁, …)`. -/
theorem odd_sphere_vector_field {n : ℕ} (z : Fin n → ℂ) :
    reInner z (fun k => Complex.I * z k) = 0 ∧
      reInner (fun k => Complex.I * z k) (fun k => Complex.I * z k) = reInner z z := by
  constructor
  · -- each term `Re(z̄ · i z) = Re(i |z|²)` is zero
    apply Finset.sum_eq_zero
    intro k _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  · -- `|i z| = |z|` term by term
    apply Finset.sum_congr rfl
    intro k _
    simp only [map_mul, Complex.conj_I, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
-- @endregion

-- @region vector_bundles_characteristic_classes.dot4
-- @provenance definition
/-- The dot product on `ℝ⁴`. -/
def dot4 (x y : Fin 4 → ℝ) : ℝ := ∑ i, x i * y i
-- @endregion

-- @region vector_bundles_characteristic_classes.frame_i
-- @provenance definition
/-- Three vector fields on `ℝ⁴`: left multiplication of `x = x₀ + x₁ i + x₂ j + x₃ k` by the
quaternion units `i`, `j`, `k`. -/
def frameI (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![-x 1, x 0, -x 3, x 2]
-- @endregion

-- @region vector_bundles_characteristic_classes.frame_j
-- @provenance definition
/-- Left multiplication by `j`. -/
def frameJ (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![-x 2, x 3, x 0, -x 1]
-- @endregion

-- @region vector_bundles_characteristic_classes.frame_k
-- @provenance definition
/-- Left multiplication by `k`. -/
def frameK (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![-x 3, -x 2, x 1, x 0]
-- @endregion

-- @region vector_bundles_characteristic_classes.s3_parallelizable
-- @provenance independent
/-- **`S³` is parallelisable.** At every point `x` the vectors `i x`, `j x`, `k x` are tangent to
the sphere through `x` (orthogonal to `x`), pairwise orthogonal, and as long as `x`; on the unit
sphere they form an orthonormal basis of the tangent space, so `TS³ ≅ S³ × ℝ³`. -/
theorem s3_parallelizable (x : Fin 4 → ℝ) :
    dot4 x (frameI x) = 0 ∧ dot4 x (frameJ x) = 0 ∧ dot4 x (frameK x) = 0 ∧
    dot4 (frameI x) (frameJ x) = 0 ∧ dot4 (frameI x) (frameK x) = 0 ∧
    dot4 (frameJ x) (frameK x) = 0 ∧
    dot4 (frameI x) (frameI x) = dot4 x x ∧ dot4 (frameJ x) (frameJ x) = dot4 x x ∧
    dot4 (frameK x) (frameK x) = dot4 x x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [dot4, frameI, frameJ, frameK, Fin.sum_univ_four] <;> ring
-- @endregion

/-! ### Stiefel–Whitney arithmetic in `ℤ/2[a]` -/

open Polynomial

-- @region vector_bundles_characteristic_classes.frobenius_two
-- @provenance library
/-- In characteristic two, `(1 + a)^(2^k) = 1 + a^(2^k)`. Since `w(TℝPⁿ) = (1 + a)ⁿ⁺¹` with
`aⁿ⁺¹ = 0`, this shows `w(TℝPⁿ) = 1` when `n + 1 = 2^k` (e.g. `ℝP³`, `ℝP⁷`). This applies
Mathlib's `add_pow_char_pow`. -/
theorem frobenius_two (k : ℕ) : ((1 + X) ^ (2 ^ k) : (ZMod 2)[X]) = 1 + X ^ (2 ^ k) := by
  simpa using add_pow_char_pow (1 : (ZMod 2)[X]) X (p := 2) (n := k)
-- @endregion

-- @region vector_bundles_characteristic_classes.sw_rp2
-- @provenance independent
/-- The total Stiefel–Whitney class of `ℝP²` is `(1 + a)³ = 1 + a + a² + a³ = 1 + a + a²` in
`H*(ℝP²; ℤ/2) = ℤ/2[a]/(a³)`. As a polynomial identity mod 2: squaring is additive, so
`(1 + a)³ = (1 + a²)(1 + a)`. Since `w₁ = a ≠ 0`, `ℝP²` is non-orientable, and since `w₂ = a² ≠ 0`
its tangent bundle is not trivial. -/
theorem sw_rp2 : ((1 + X) ^ 3 : (ZMod 2)[X]) = 1 + X + X ^ 2 + X ^ 3 := by
  have hsq : ((1 + X) ^ 2 : (ZMod 2)[X]) = 1 + X ^ 2 := by
    simpa using add_pow_char (1 : (ZMod 2)[X]) X (p := 2)
  rw [pow_succ, hsq]
  ring
-- @endregion

/-! ### What Mathlib provides -/

open Bundle in
-- @region vector_bundles_characteristic_classes.trivial_bundle
-- @provenance library
/-- The product `B × ℝᵏ`, as Mathlib's `Bundle.Trivial B F`, is a vector bundle. This applies
the instance `Bundle.Trivial.vectorBundle`. -/
theorem trivial_bundle (B F : Type*) [TopologicalSpace B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : VectorBundle ℝ F (Bundle.Trivial B F) :=
  inferInstance
-- @endregion

open Bundle in
-- @region vector_bundles_characteristic_classes.pullback_bundle
-- @provenance library
/-- **Pullbacks.** If `E → B` is a vector bundle and `f : B' → B` is continuous, then `f*E → B'`
(fibre `E_{f(b')}` over `b'`) is a vector bundle. This applies Mathlib's instance
`VectorBundle.pullback`. Characteristic classes are, by definition, natural under pullback. -/
theorem pullback_bundle {B B' F : Type*} [TopologicalSpace B] [TopologicalSpace B']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type*} [∀ x, AddCommMonoid (E x)]
    [∀ x, Module ℝ (E x)] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℝ F E] (f : C(B', B)) :
    VectorBundle ℝ F ((f : B' → B) *ᵖ E) :=
  inferInstance
-- @endregion

open Bundle in
-- @region vector_bundles_characteristic_classes.whitney_sum
-- @provenance library
/-- **Whitney sum.** The fibrewise direct sum `E₁ ⊕ E₂` of two vector bundles over the same base
(Mathlib's `E₁ ×ᵇ E₂`) is a vector bundle. This applies Mathlib's instance `VectorBundle.prod`. -/
theorem whitney_sum {B F₁ F₂ : Type*} [TopologicalSpace B]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {E₁ E₂ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module ℝ (E₁ x)]
    [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module ℝ (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] :
    VectorBundle ℝ (F₁ × F₂) (E₁ ×ᵇ E₂) :=
  inferInstance
-- @endregion

-- @region vector_bundles_characteristic_classes.tangent_bundle
-- @provenance library
/-- **The tangent bundle** of a (once differentiable) manifold `M` modelled on a normed space `E`
is a vector bundle with fibre `E`. This applies Mathlib's instance `TangentSpace.vectorBundle`,
built from the derivatives of the chart transition maps — a cocycle of transition functions. -/
theorem tangent_bundle {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] : VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  inferInstance
-- @endregion

end Lumenary.VectorBundlesCharacteristicClasses
