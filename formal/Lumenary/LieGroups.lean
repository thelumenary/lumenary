/-
The Lumenary — formal mathematics
Lie groups and Lie algebras: the commutator bracket and the Jacobi identity, one-parameter
subgroups `t ↦ exp(tX)`, the exponential of a skew-symmetric matrix is orthogonal, the Lie
algebras `so(3)` and `su(2)` have the same structure constants, the relations of `sl(2)`, the
key commutator identity behind the classification of `sl(2, ℂ)`-representations and its
consequence that highest weights are natural numbers, and `X² = -det(X) I` on `sl(2)`.

What is proved here and what Mathlib provides. Mathlib defines Lie groups (`LieGroup I n G`), proves
that the units of a complete normed algebra (such as `GL(n, ℝ)`) and the circle are Lie groups,
equips the tangent space at the identity of a Lie group with its Lie algebra structure
(`GroupLieAlgebra`), defines abstract Lie algebras and their representations, the matrix
exponential (`NormedSpace.exp`, with `Matrix.exp_add_of_commute` and `Matrix.exp_transpose`) and
`sl₂`-triples with the theory of primitive vectors (`IsSl2Triple`). We cite several of these.
The *independent* declarations prove lesson results from them or from scratch.

Not formalised here: the Lie correspondence and Lie's third theorem, the closed subgroup
theorem, Haar measure on compact groups (Mathlib has Haar measure on locally compact groups, but
not the Peter–Weyl theory), the double cover `SU(2) → SO(3)`, the non-surjectivity of `exp` on
`SL(2, ℝ)` (we formalise its algebraic core), `det(exp X) = e^{tr X}` (a TODO in Mathlib), and root
systems.
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace Lumenary.LieGroups

open Matrix
open scoped Manifold ContDiff

/- Mathlib does not make the commutator bracket on an associative ring a global instance (it
would clash with other brackets); we switch it on for this file, as Mathlib's own
`Algebra.Lie.Classical` does. -/
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Lie groups in Mathlib -/

-- @region lie_groups.units_lie_group
-- @provenance library
/-- **`GL` is a Lie group.** The group of units `Rˣ` of a complete normed algebra `R` is a Lie
group, modelled on `R` itself (it is an open subset of `R`). For `R = Mₙ(ℝ)` with an operator
norm, this is `GL(n, ℝ)`. Mathlib's instance from `UnitsOfNormedAlgebra`. -/
theorem units_lie_group {𝕜 : Type*} [NontriviallyNormedField 𝕜] {R : Type*} [NormedRing R]
    [CompleteSpace R] [NormedAlgebra 𝕜 R] (n : WithTop ℕ∞) :
    LieGroup (modelWithCornersSelf 𝕜 R) n Rˣ :=
  inferInstance
-- @endregion

-- @region lie_groups.circle_lie_group
-- @provenance library
/-- **The circle group `U(1)` is a Lie group** (indeed analytic, `ω`), with the charts of the
`1`-sphere. Mathlib's instance in `Instances.Sphere`. -/
theorem circle_lie_group : LieGroup (𝓡 1) ω Circle :=
  inferInstance
-- @endregion

/-! ### Lie algebras of matrices -/

-- @region lie_groups.commutator_jacobi
-- @provenance independent
/-- **The commutator satisfies the Jacobi identity.** In any associative ring, with
`[X, Y] = XY - YX`: `[X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0` — expand the twelve products and
they cancel in pairs. So every associative algebra, in particular `Mₙ(ℝ)`, is a Lie algebra. -/
theorem commutator_jacobi {A : Type*} [Ring A] (X Y Z : A) :
    X * (Y * Z - Z * Y) - (Y * Z - Z * Y) * X + (Y * (Z * X - X * Z) - (Z * X - X * Z) * Y) +
      (Z * (X * Y - Y * X) - (X * Y - Y * X) * Z) = 0 := by
  noncomm_ring
-- @endregion

-- @region lie_groups.lie_jacobi_library
-- @provenance library
/-- The same identity for Mathlib's Lie bracket on a ring (`⁅X, Y⁆ = XY - YX`, `Ring.lie_def`):
Mathlib's `lie_jacobi`, valid in every Lie ring. -/
theorem lie_jacobi_library {A : Type*} [Ring A] (X Y Z : A) :
    ⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆ = 0 :=
  lie_jacobi X Y Z
-- @endregion

/-! ### The exponential map -/

section Exponential

variable {n : Type*} [Fintype n] [DecidableEq n]

-- @region lie_groups.exp_one_parameter
-- @provenance independent
/-- **`t ↦ exp(tX)` is a one-parameter subgroup**: `exp((s + t)X) = exp(sX) exp(tX)`. The two
exponents commute (both are multiples of `X`), so Mathlib's `Matrix.exp_add_of_commute` applies. -/
theorem exp_one_parameter (X : Matrix n n ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)
-- @endregion

-- @region lie_groups.exp_skew_orthogonal
-- @provenance independent
/-- **The exponential of a skew-symmetric matrix is orthogonal**: if `Aᵀ = -A` then
`(exp A)ᵀ exp A = exp(Aᵀ) exp(A) = exp(-A) exp(A) = exp(0) = I`. So `exp` maps `so(n)` into
`O(n)` (indeed into `SO(n)`, by connectedness). -/
theorem exp_skew_orthogonal {A : Matrix n n ℝ} (hA : Aᵀ = -A) :
    (NormedSpace.exp A)ᵀ * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_transpose, hA,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_left), neg_add_cancel,
    NormedSpace.exp_zero]
-- @endregion

end Exponential

/-! ### `so(3)` and `su(2)` -/

-- @region lie_groups.hat
-- @provenance definition
/-- The **hat map** `ℝ³ → so(3)`: `â` is the skew-symmetric matrix with `â v = a × v`. -/
def hat (a : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -a 2, a 1; a 2, 0, -a 0; -a 1, a 0, 0]
-- @endregion

-- @region lie_groups.hat_bracket
-- @provenance independent
/-- **`so(3)` is `ℝ³` with the cross product**: `[â, b̂] = (a × b)^`. With the basis
`Lᵢ = êᵢ` this reads `[L₁, L₂] = L₃`, `[L₂, L₃] = L₁`, `[L₃, L₁] = L₂`. -/
theorem hat_bracket (a b : Fin 3 → ℝ) :
    hat a * hat b - hat b * hat a = hat (crossProduct a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hat, cross_apply] <;> ring
-- @endregion

-- @region lie_groups.su2_basis
-- @provenance definition
/-- A basis of `su(2)`, the trace-zero skew-Hermitian `2 × 2` matrices: `Xₖ = -(i/2) σₖ` for the
Pauli matrices `σ₁, σ₂, σ₃`. -/
noncomputable def su2Basis : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, -Complex.I / 2; -Complex.I / 2, 0],
    !![0, -1 / 2; 1 / 2, 0],
    !![-Complex.I / 2, 0; 0, Complex.I / 2]]
-- @endregion

-- @region lie_groups.su2_brackets
-- @provenance independent
/-- **`su(2)` has the same structure constants as `so(3)`**: `[X₁, X₂] = X₃`, `[X₂, X₃] = X₁`,
`[X₃, X₁] = X₂`. Hence `Xₖ ↦ Lₖ` is a Lie algebra isomorphism `su(2) ≅ so(3)`, although the
groups `SU(2)` and `SO(3)` are not isomorphic. -/
theorem su2_brackets :
    su2Basis 0 * su2Basis 1 - su2Basis 1 * su2Basis 0 = su2Basis 2 ∧
      su2Basis 1 * su2Basis 2 - su2Basis 2 * su2Basis 1 = su2Basis 0 ∧
      su2Basis 2 * su2Basis 0 - su2Basis 0 * su2Basis 2 = su2Basis 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2Basis] <;> ring_nf <;>
      simp [Complex.ext_iff] <;> norm_num
-- @endregion

-- @region lie_groups.neg_one_mem_su2
-- @provenance independent
/-- `-I` lies in `SU(2)` (it is unitary with determinant `(-1)² = 1`) and is central but not the
identity; so the centre of `SU(2)` is non-trivial, whereas that of `SO(3)` is trivial — one way to
see that the two groups are not isomorphic. -/
theorem neg_one_mem_su2 :
    (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      (-1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    simp [Matrix.det_neg]
  · intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this
-- @endregion

/-! ### `sl(2)`: relations and representations -/

-- @region lie_groups.sl2_e
-- @provenance definition
/-- The standard basis of `sl(2)`: `e = [[0, 1], [0, 0]]`. -/
def sl2E : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
-- @endregion

-- @region lie_groups.sl2_f
-- @provenance definition
/-- `f = [[0, 0], [1, 0]]`. -/
def sl2F : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
-- @endregion

-- @region lie_groups.sl2_h
-- @provenance definition
/-- `h = [[1, 0], [0, -1]]`. -/
def sl2H : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]
-- @endregion

-- @region lie_groups.sl2_triple
-- @provenance independent
/-- **The relations of `sl(2)`**: `[h, e] = 2e`, `[h, f] = -2f`, `[e, f] = h`. In Mathlib's language,
`(h, e, f)` is an `sl₂`-triple in the Lie algebra of `2 × 2` matrices. -/
theorem sl2_triple : IsSl2Triple sl2H sl2E sl2F where
  h_ne_zero := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [sl2H] at this
  lie_e_f := by
    rw [Ring.lie_def]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2E, sl2F, sl2H]
  lie_h_e_nsmul := by
    rw [Ring.lie_def]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sl2E, sl2H]
  lie_h_f_nsmul := by
    rw [Ring.lie_def]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sl2F, sl2H]
-- @endregion

-- @region lie_groups.e_f_pow
-- @provenance independent
/-- **The key identity for `sl(2)`-representations.** In any ring (for instance the operators on a
representation) in which `hf - fh = -2f` and `ef - fe = h`,
`e fᵏ⁺¹ - fᵏ⁺¹ e = (k + 1) fᵏ (h - k)`. Induction on `k`: commute `e` past one `f` at a time, and
use `(h - k) f = f (h - k - 2)`. -/
theorem e_f_pow {A : Type*} [Ring A] {e f h : A} (hhf : h * f - f * h = -2 * f)
    (hef : e * f - f * e = h) (k : ℕ) :
    e * f ^ (k + 1) - f ^ (k + 1) * e = ((k : A) + 1) * f ^ k * (h - k) := by
  have hcomm : ∀ m : ℕ, (m : A) * f = f * m := fun m => (Nat.cast_commute m f)
  have h2 : (2 : A) * f = f * 2 := by
    rw [show (2 : A) = ((2 : ℕ) : A) by norm_num]
    exact hcomm 2
  have h1 : h * f = f * h + -2 * f := by rw [← hhf]; abel
  have hshift : ∀ m : ℕ, (h - m) * f = f * (h - m - 2) := by
    intro m
    calc (h - m) * f = h * f - m * f := sub_mul _ _ _
      _ = (f * h + -2 * f) - f * m := by rw [h1, hcomm]
      _ = f * (h - m - 2) := by rw [neg_mul, h2]; noncomm_ring
  induction k with
  | zero => simpa using hef
  | succ k ih =>
    calc e * f ^ (k + 1 + 1) - f ^ (k + 1 + 1) * e
        = (e * f ^ (k + 1) - f ^ (k + 1) * e) * f + f ^ (k + 1) * (e * f - f * e) := by
          rw [pow_succ f (k + 1)]
          noncomm_ring
      _ = ((k : A) + 1) * f ^ k * ((h - k) * f) + f ^ (k + 1) * h := by
          rw [ih, hef]
          noncomm_ring
      _ = ((k : A) + 1) * (f ^ k * f) * (h - k - 2) + f ^ (k + 1) * h := by
          rw [hshift k]
          noncomm_ring
      _ = f ^ (k + 1) * (((k : A) + 1) * (h - k - 2) + h) := by
          rw [← pow_succ]
          have hc : ((k : A) + 1) * f ^ (k + 1) = f ^ (k + 1) * ((k : A) + 1) :=
            ((Nat.cast_commute k _).add_left (Commute.one_left _))
          rw [mul_add, ← mul_assoc, hc, mul_assoc]
      _ = (((k + 1 : ℕ) : A) + 1) * f ^ (k + 1) * (h - ((k + 1 : ℕ) : A)) := by
          have hc : (((k + 1 : ℕ) : A) + 1) * f ^ (k + 1) =
              f ^ (k + 1) * (((k + 1 : ℕ) : A) + 1) :=
            ((Nat.cast_commute (k + 1) _).add_left (Commute.one_left _))
          rw [hc, mul_assoc]
          congr 1
          push_cast
          noncomm_ring
-- @endregion

-- @region lie_groups.highest_weight_nat
-- @provenance independent
/-- **Highest weights are natural numbers.** Let `E, F, H` act on a complex vector space with the
`sl(2)` relations, and let `v` be a highest weight vector: `E v = 0`, `H v = λ v`. If the string
`v, Fv, F²v, …` stops after `Fⁿ v ≠ 0` (that is, `Fⁿ⁺¹ v = 0`), then `λ = n`. Apply `e_f_pow` to
`v`: `0 = E Fⁿ⁺¹ v - Fⁿ⁺¹ E v = (n + 1)(λ - n) Fⁿ v`. -/
theorem highest_weight_nat {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E F H : Module.End ℂ M} (hhf : H * F - F * H = -2 * F) (hef : E * F - F * E = H)
    {v : M} {μ : ℂ} (hE : E v = 0) (hH : H v = μ • v) {n : ℕ}
    (hn : (F ^ n) v ≠ 0) (hn1 : (F ^ (n + 1)) v = 0) : μ = n := by
  have key := LinearMap.congr_fun (e_f_pow hhf hef n) v
  have hl : (E * F ^ (n + 1) - F ^ (n + 1) * E) v = 0 := by
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hn1, hE, map_zero,
      map_zero, sub_zero]
  have hv : (H - (n : Module.End ℂ M)) v = (μ - n) • v := by
    rw [LinearMap.sub_apply, hH, Module.End.natCast_apply, sub_smul, Nat.cast_smul_eq_nsmul]
  have hr : (((n : Module.End ℂ M) + 1) * F ^ n * (H - n)) v =
      (((n : ℂ) + 1) * (μ - n)) • (F ^ n) v := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_smul, LinearMap.add_apply,
      Module.End.natCast_apply, Module.End.one_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      ← add_smul]
    congr 1
    ring
  rw [hl, hr] at key
  have hscalar : ((n : ℂ) + 1) * (μ - n) = 0 := by
    by_contra hne
    exact hn (smul_eq_zero.mp key.symm |>.resolve_left hne)
  rcases mul_eq_zero.mp hscalar with h | h
  · exfalso
    have : ((n + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h
    exact Nat.succ_ne_zero n (Nat.cast_eq_zero.mp this)
  · exact sub_eq_zero.mp h
-- @endregion

-- @region lie_groups.primitive_vector_nat
-- @provenance library
/-- Mathlib's version, for any finite-dimensional (Noetherian, torsion-free) representation of a
Lie algebra over a field of characteristic `0` with an `sl₂`-triple: the eigenvalue of a primitive
vector is a natural number. Mathlib's `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`. -/
theorem primitive_vector_nat {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [IsNoetherian K M] [Module.IsTorsionFree K M] {h e f : L} {t : IsSl2Triple h e f} {m : M} {μ : K}
    (P : t.HasPrimitiveVectorWith m μ) : ∃ n : ℕ, μ = n :=
  P.exists_nat
-- @endregion

-- @region lie_groups.sl2_sq_scalar
-- @provenance independent
/-- **On `sl(2)`, `X² = -det(X) I`** (Cayley–Hamilton for trace-zero `2 × 2` matrices). This is
the algebraic core of the computation `exp X = cosh(√δ) I + (sinh √δ / √δ) X` with `δ = -det X`,
which shows `tr(exp X) ≥ -2` for `X ∈ sl(2, ℝ)`, so that `diag(-2, -1/2) ∈ SL(2, ℝ)` is not an
exponential. -/
theorem sl2_sq_scalar {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.trace = 0) :
    X * X = -X.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.trace_fin_two] at hX
  have hd : X 1 1 = -X 0 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, hd] <;> ring
-- @endregion

/-! ### Haar measure -/

-- @region lie_groups.haar_measure
-- @provenance library
/-- **Haar measure exists.** Every locally compact topological group carries a left-invariant
Haar measure (finite on compact sets, positive on open sets). For a compact group it is finite,
and averaging an inner product against it produces an invariant one — the key to complete
reducibility. Mathlib's `MeasureTheory.Measure.haar` and its `IsHaarMeasure` instance. -/
theorem haar_measure {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    (MeasureTheory.Measure.haar : MeasureTheory.Measure G).IsHaarMeasure :=
  inferInstance
-- @endregion

-- @region lie_groups.haar_finite_compact
-- @provenance library
/-- On a **compact** group the Haar measure is finite, so it can be normalised to a probability
measure and used to average. A Mathlib instance (compact sets have finite Haar measure). -/
theorem haar_finite_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.haar : MeasureTheory.Measure G) :=
  inferInstance
-- @endregion

end Lumenary.LieGroups
