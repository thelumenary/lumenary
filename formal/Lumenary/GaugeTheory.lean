/-
The Lumenary — formal mathematics
Gauge theory: lattice gauge fields, gauge covariance of parallel transport and gauge invariance of
Wilson loops (for any structure group); the gauge invariance of the electromagnetic field strength
and the Bianchi identity (`F = dA`, `d(A + dχ) = dA`, `dF = 0`); and the pointwise algebra behind
the instanton bound `|F|² ≥ |F ∧ F|`, with equality exactly for self-dual or anti-self-dual forms.

What is proved here and what Mathlib provides. Mathlib has no principal bundles or connections yet,
so the *independent* declarations work with Wilson's lattice formulation: a connection on the square
lattice `ℤ²` assigns a group element (a parallel transporter) to each oriented edge, a gauge
transformation is a group element at each vertex, and parallel transport along a path is the
ordered product. We prove by induction on paths that transport transforms by the gauge
transformation at the two ends, so holonomies of closed loops change by conjugation; their traces
(Wilson loops) and, for abelian groups, the holonomies themselves are gauge invariant. In the
continuum, a `U(1)` gauge potential is a real `1`-form `A` and the field strength is `F = dA`;
using Mathlib's exterior derivative `extDeriv` on a normed space (`extDeriv_add`,
`extDeriv_extDeriv`) we prove that `F` is unchanged by `A ↦ A + dχ` and satisfies the Bianchi
identity `dF = 0` (the homogeneous Maxwell equations). Finally, writing a `2`-form on ℝ⁴ as a pair
`(a, b) ∈ ℝ³ × ℝ³` (`a = (F₀₁, F₀₂, F₀₃)`, `b = (F₂₃, F₃₁, F₁₂)`), on which the Hodge star swaps `a`
and `b`, we prove `|F ∧ F| ≤ |F|²` with equality iff `⋆F = ±F`. Not formalised: principal bundles,
non-abelian curvature `F = dA + A ∧ A`, Chern–Weil theory and the identification of `∫ F ∧ F`
with a characteristic number, the Yang–Mills equations, instanton moduli spaces and Donaldson's
theorem.
-/
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Group

namespace Lumenary.GaugeTheory

open Matrix

/-! ### Lattice gauge fields -/

-- @region gauge_theory.lattice_connection
-- @provenance definition
/-- A lattice gauge field (connection) on the square lattice `ℤ²` with structure group `G`:
`ux x` transports from `x + (1, 0)` back to `x` along the edge in the `x`-direction, and `uy x`
likewise in the `y`-direction. (Wilson, 1974.) -/
structure LatticeConnection (G : Type*) where
  /-- The link variable on the edge from `x` to `x + (1, 0)`. -/
  ux : ℤ × ℤ → G
  /-- The link variable on the edge from `x` to `x + (0, 1)`. -/
  uy : ℤ × ℤ → G
-- @endregion

-- @region gauge_theory.step
-- @provenance definition
/-- A step of a lattice path: one unit east (`xp`), west (`xm`), north (`yp`) or south (`ym`). -/
inductive Step
  | xp
  | xm
  | yp
  | ym
-- @endregion

-- @region gauge_theory.step_shift
-- @provenance definition
/-- The displacement of a step. -/
def Step.shift : Step → ℤ × ℤ
  | .xp => (1, 0)
  | .xm => (-1, 0)
  | .yp => (0, 1)
  | .ym => (0, -1)
-- @endregion

variable {G : Type*} [Group G]

-- @region gauge_theory.transport
-- @provenance definition
/-- Parallel transport along one step from `x`: the link variable, inverted when the edge is
traversed backwards. -/
def transport (A : LatticeConnection G) (x : ℤ × ℤ) : Step → G
  | .xp => A.ux x
  | .xm => (A.ux (x + (-1, 0)))⁻¹
  | .yp => A.uy x
  | .ym => (A.uy (x + (0, -1)))⁻¹
-- @endregion

-- @region gauge_theory.endpoint
-- @provenance definition
/-- The endpoint of the path that starts at `x` and takes the given steps. -/
def endpoint (x : ℤ × ℤ) : List Step → ℤ × ℤ
  | [] => x
  | s :: ss => endpoint (x + s.shift) ss
-- @endregion

-- @region gauge_theory.holonomy
-- @provenance definition
/-- Parallel transport (holonomy) along a path: the ordered product of the step transports. For a
closed path this is the holonomy of the loop; for the boundary of one square it is the discrete
curvature (the plaquette variable). -/
def holonomy (A : LatticeConnection G) (x : ℤ × ℤ) : List Step → G
  | [] => 1
  | s :: ss => transport A x s * holonomy A (x + s.shift) ss
-- @endregion

-- @region gauge_theory.gauge
-- @provenance definition
/-- A gauge transformation `g : ℤ² → G` (a change of frame at every vertex) acts on link variables
by `U(x → y) ↦ g(x) U(x → y) g(y)⁻¹`. -/
def gauge (g : ℤ × ℤ → G) (A : LatticeConnection G) : LatticeConnection G where
  ux x := g x * A.ux x * (g (x + (1, 0)))⁻¹
  uy x := g x * A.uy x * (g (x + (0, 1)))⁻¹
-- @endregion

-- @region gauge_theory.gauge_mul
-- @provenance independent
/-- Gauge transformations form a group acting on connections: doing `h` and then `g` is the same as
doing the pointwise product `g * h`. -/
theorem gauge_mul (g h : ℤ × ℤ → G) (A : LatticeConnection G) :
    gauge g (gauge h A) = gauge (g * h) A := by
  simp only [gauge, Pi.mul_apply, mul_inv_rev]
  congr 1 <;> funext x <;> group
-- @endregion

-- @region gauge_theory.transport_gauge
-- @provenance independent
/-- One step transforms covariantly: `transport (g • A) x s = g(x) · transport A x s · g(x + s)⁻¹`.
For backward steps this uses `(x - e) + e = x`. -/
theorem transport_gauge (g : ℤ × ℤ → G) (A : LatticeConnection G) (x : ℤ × ℤ) (s : Step) :
    transport (gauge g A) x s = g x * transport A x s * (g (x + s.shift))⁻¹ := by
  cases s
  · rfl
  · simp only [transport, gauge, Step.shift]
    have : x + (-1, 0) + (1, 0) = x := by ext <;> simp
    rw [this]; group
  · rfl
  · simp only [transport, gauge, Step.shift]
    have : x + (0, -1) + (0, 1) = x := by ext <;> simp
    rw [this]; group
-- @endregion

-- @region gauge_theory.holonomy_gauge
-- @provenance independent
/-- **Gauge covariance of parallel transport.** Along any path from `x` to `y`, the holonomy of the
transformed connection is `g(x) · hol · g(y)⁻¹`: the gauge transformations at intermediate
vertices cancel in pairs. Proof by induction on the path. -/
theorem holonomy_gauge (g : ℤ × ℤ → G) (A : LatticeConnection G) (p : List Step) :
    ∀ x, holonomy (gauge g A) x p = g x * holonomy A x p * (g (endpoint x p))⁻¹ := by
  induction p with
  | nil => intro x; simp [holonomy, endpoint]
  | cons s ss ih =>
    intro x
    simp only [holonomy, endpoint, transport_gauge, ih]
    group
-- @endregion

-- @region gauge_theory.holonomy_loop_conj
-- @provenance independent
/-- The holonomy of a closed loop based at `x` changes by conjugation by `g(x)`. So only its
conjugacy class — not the group element itself — is physical in a non-abelian theory. -/
theorem holonomy_loop_conj (g : ℤ × ℤ → G) (A : LatticeConnection G) (x : ℤ × ℤ)
    (p : List Step) (hp : endpoint x p = x) :
    holonomy (gauge g A) x p = g x * holonomy A x p * (g x)⁻¹ := by
  rw [holonomy_gauge, hp]
-- @endregion

-- @region gauge_theory.holonomy_loop_abelian
-- @provenance independent
/-- **Abelian gauge theory (electromagnetism on a lattice).** For a commutative structure group such
as `U(1)`, the holonomy of every closed loop is gauge invariant. Around a single square it is the
lattice field strength `exp(i · flux)`; around a large loop, `exp(i · enclosed flux)`. -/
theorem holonomy_loop_abelian {G : Type*} [CommGroup G] (g : ℤ × ℤ → G)
    (A : LatticeConnection G) (x : ℤ × ℤ) (p : List Step) (hp : endpoint x p = x) :
    holonomy (gauge g A) x p = holonomy A x p := by
  rw [holonomy_gauge, hp, mul_comm (g x), mul_assoc, mul_inv_cancel, mul_one]
-- @endregion

-- @region gauge_theory.plaquette
-- @provenance independent
/-- The holonomy around the unit square with corner `x` (the plaquette variable, Wilson's lattice
curvature): `U_x(x) U_y(x + e₁) U_x(x + e₂)⁻¹ U_y(x)⁻¹`. -/
theorem plaquette (A : LatticeConnection G) (x : ℤ × ℤ) :
    holonomy A x [.xp, .yp, .xm, .ym] =
      A.ux x * A.uy (x + (1, 0)) * (A.ux (x + (0, 1)))⁻¹ * (A.uy x)⁻¹ := by
  simp only [holonomy, transport, Step.shift]
  have h1 : x + (1, 0) + (0, 1) + (-1, 0) = x + (0, 1) := by ext <;> simp
  rw [h1]
  have h3 : x + (0, 1) + (0, -1) = x := by ext <;> simp
  rw [h3]
  group
-- @endregion

-- @region gauge_theory.trace_conj
-- @provenance library
/-- The trace of a matrix is invariant under conjugation by an invertible matrix,
`tr(g h g⁻¹) = tr(h)`. This applies Mathlib's `Matrix.trace_mul_cycle` (`tr(ABC) = tr(CAB)`). -/
theorem trace_conj {n : Type*} [Fintype n] [DecidableEq n] (g h : (Matrix n n ℂ)ˣ) :
    trace (↑(g * h * g⁻¹) : Matrix n n ℂ) = trace (↑h : Matrix n n ℂ) := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]
-- @endregion

-- @region gauge_theory.wilson_loop_gauge_invariant
-- @provenance independent
/-- **Wilson loops are gauge invariant.** For a lattice gauge field with values in invertible
complex matrices (for example `SU(2)` or `SU(3)`), the trace of the holonomy around any closed loop
is unchanged by every gauge transformation. -/
theorem wilson_loop_gauge_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (g : ℤ × ℤ → (Matrix n n ℂ)ˣ) (A : LatticeConnection (Matrix n n ℂ)ˣ) (x : ℤ × ℤ)
    (p : List Step) (hp : endpoint x p = x) :
    trace (↑(holonomy (gauge g A) x p) : Matrix n n ℂ) =
      trace (↑(holonomy A x p) : Matrix n n ℂ) := by
  rw [holonomy_loop_conj g A x p hp, trace_conj]
-- @endregion

/-! ### Electromagnetism: `F = dA` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @region gauge_theory.field_strength_gauge_invariant
-- @provenance independent
/-- **Gauge invariance of the electromagnetic field.** If the potential `1`-form `A` is changed by
the differential of a `C²` function `χ`, the field strength `F = dA` does not change:
`d(A + dχ) = dA + d(dχ) = dA`. Uses Mathlib's `extDeriv_add` and `extDeriv_extDeriv_apply`, plus
the differentiability of `dχ` (as the composite of `fderiv χ` with a continuous linear map). -/
theorem field_strength_gauge_invariant {A : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {χ : E → E [⋀^Fin 0]→L[ℝ] ℝ} (hχ : ContDiff ℝ 2 χ) {x : E}
    (hA : DifferentiableAt ℝ A x) :
    extDeriv (A + extDeriv χ) x = extDeriv A x := by
  have hdχ : DifferentiableAt ℝ (extDeriv χ) x := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ χ) := hχ.fderiv_right (by norm_num)
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).differentiableAt.comp x
      (h1.differentiable (by norm_num) x)
  rw [extDeriv_add hA hdχ, extDeriv_extDeriv_apply hχ.contDiffAt (by simp), add_zero]
-- @endregion

-- @region gauge_theory.bianchi
-- @provenance library
/-- **The Bianchi identity `dF = 0`** for `F = dA` with `A` of class `C²`. In space-time these are
the homogeneous Maxwell equations `div B = 0` and `∂B/∂t + curl E = 0`. This applies Mathlib's
`extDeriv_extDeriv` (`d ∘ d = 0`). -/
theorem bianchi {A : E → E [⋀^Fin 1]→L[ℝ] ℝ} (hA : ContDiff ℝ 2 A) :
    extDeriv (extDeriv A) = 0 :=
  extDeriv_extDeriv hA (by simp)
-- @endregion

/-! ### Self-duality and the instanton bound, pointwise -/

-- @region gauge_theory.hodge_star
-- @provenance definition
/-- A `2`-form on Euclidean ℝ⁴ as a pair `(a, b)` with `a = (F₀₁, F₀₂, F₀₃)` and
`b = (F₂₃, F₃₁, F₁₂)`. The Hodge star (`⋆(dx₀ ∧ dx₁) = dx₂ ∧ dx₃` and cyclically) swaps them. -/
def hodgeStar (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : (Fin 3 → ℝ) × (Fin 3 → ℝ) := (F.2, F.1)
-- @endregion

-- @region gauge_theory.norm_sq
-- @provenance definition
/-- The pointwise energy density `|F|² = Σ_{i<j} F_{ij}²`. -/
def normSq (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ := F.1 ⬝ᵥ F.1 + F.2 ⬝ᵥ F.2
-- @endregion

-- @region gauge_theory.wedge_self
-- @provenance definition
/-- The coefficient of `F ∧ F` with respect to `dx₀ ∧ dx₁ ∧ dx₂ ∧ dx₃`:
`2 (F₀₁ F₂₃ + F₀₂ F₃₁ + F₀₃ F₁₂)`, the topological charge density (up to normalisation). -/
def wedgeSelf (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ := 2 * (F.1 ⬝ᵥ F.2)
-- @endregion

-- @region gauge_theory.hodge_star_hodge_star
-- @provenance independent
/-- On `2`-forms in four Euclidean dimensions `⋆⋆ = 1`, so `Λ²` splits into the `±1` eigenspaces:
self-dual and anti-self-dual forms. -/
theorem hodge_star_hodge_star (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : hodgeStar (hodgeStar F) = F := rfl
-- @endregion

-- @region gauge_theory.abs_wedge_le
-- @provenance independent
/-- **The instanton bound, pointwise**: `|F ∧ F| ≤ |F|²`, from `|a ∓ b|² ≥ 0`. Integrated over a
closed `4`-manifold (and summed over Lie algebra components) this gives the Yang–Mills energy bound
`YM(A) ≥ 8π² |k|` for an `SU(2)` bundle with `c₂ = k`, in the usual normalisation. -/
theorem abs_wedge_le (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : |wedgeSelf F| ≤ normSq F := by
  obtain ⟨a, b⟩ := F
  simp only [wedgeSelf, normSq, dotProduct, Fin.sum_univ_three]
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (a 0 + b 0), sq_nonneg (a 1 + b 1), sq_nonneg (a 2 + b 2)]
  · nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]
-- @endregion

-- @region gauge_theory.self_dual_iff
-- @provenance independent
/-- **Equality holds exactly for self-dual forms**: `|F|² = F ∧ F` iff `⋆F = F`. (Instantons, in
the anti-self-dual convention, are the case `|F|² = -F ∧ F`, i.e. `⋆F = -F`.) -/
theorem self_dual_iff (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    normSq F = wedgeSelf F ↔ hodgeStar F = F := by
  obtain ⟨a, b⟩ := F
  simp only [wedgeSelf, normSq, hodgeStar, dotProduct, Fin.sum_univ_three, Prod.mk.injEq]
  constructor
  · intro h
    have e0 : a 0 = b 0 := by
      nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]
    have e1 : a 1 = b 1 := by
      nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]
    have e2 : a 2 = b 2 := by
      nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]
    have hab : a = b := by
      funext i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
    exact ⟨hab.symm, hab⟩
  · rintro ⟨h1, _⟩
    subst h1
    ring
-- @endregion

-- @region gauge_theory.anti_self_dual_iff
-- @provenance independent
/-- **Anti-self-duality**: `|F|² = -(F ∧ F)` iff `⋆F = -F`, i.e. `b = -a`. These are the
pointwise conditions satisfied by instantons. -/
theorem anti_self_dual_iff (F : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    normSq F = -wedgeSelf F ↔ hodgeStar F = -F := by
  obtain ⟨a, b⟩ := F
  simp only [wedgeSelf, normSq, hodgeStar, dotProduct, Fin.sum_univ_three, Prod.neg_mk,
    Prod.mk.injEq]
  constructor
  · intro h
    have e0 : b 0 = -a 0 := by
      nlinarith [sq_nonneg (a 0 + b 0), sq_nonneg (a 1 + b 1), sq_nonneg (a 2 + b 2)]
    have e1 : b 1 = -a 1 := by
      nlinarith [sq_nonneg (a 0 + b 0), sq_nonneg (a 1 + b 1), sq_nonneg (a 2 + b 2)]
    have e2 : b 2 = -a 2 := by
      nlinarith [sq_nonneg (a 0 + b 0), sq_nonneg (a 1 + b 1), sq_nonneg (a 2 + b 2)]
    have hab : b = -a := by
      funext i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
    refine ⟨hab, ?_⟩
    rw [hab, neg_neg]
  · rintro ⟨h1, _⟩
    subst h1
    simp only [Pi.neg_apply]
    ring
-- @endregion

end Lumenary.GaugeTheory
