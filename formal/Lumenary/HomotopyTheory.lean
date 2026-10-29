/-
The Lumenary — formal mathematics
Homotopy theory: the Eckmann–Hilton argument (why higher homotopy groups are abelian), the
Hopf map `S³ → S²` and its circle fibres, and the algebra of exact sequences used to compute
`π₃(S²)`.

What is proved here and what Mathlib provides. Mathlib defines the homotopy groups
`HomotopyGroup.Pi n X x` (written `π_ n X x`) as homotopy classes of maps of cubes sending the
boundary to the base point, gives them a group structure, proves (by Eckmann–Hilton) that they
are commutative from `n = 2` on, identifies `π_ 1` with the fundamental group, and identifies
loops of loops with higher loops. The *library* declarations below cite these. The
*independent* declarations prove the Eckmann–Hilton argument itself, the facts that the Hopf map
sends the unit sphere of `ℂ²` onto the unit sphere of `ℂ × ℝ ≅ ℝ³`, is constant on the circles
`λ · (z, w)` with `|λ| = 1`, and has *exactly* those circles as fibres, and the lemma that a
homomorphism in an exact sequence flanked by trivial groups is bijective.

Not formalised here: the long exact sequence of a fibration, the fact that the Hopf map is a
fibration, `πₙ(Sⁿ) ≅ ℤ`, and the theorems of Hurewicz, Whitehead and Freudenthal; none of these
is in Mathlib yet.
-/
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.Complex.Basic

namespace Lumenary.HomotopyTheory

/-! ### The Eckmann–Hilton argument -/

-- @region homotopy_theory.eckmann_hilton
-- @provenance independent
/-- **Eckmann–Hilton.** If a set carries two binary operations `m₁`, `m₂` with units `e₁`, `e₂`
that satisfy the interchange law `(a ·₂ b) ·₁ (c ·₂ d) = (a ·₁ c) ·₂ (b ·₁ d)`, then the units
agree, the operations agree, and the operation is commutative. For `πₙ` with `n ≥ 2`,
concatenation of cubes in two different coordinate directions gives two such operations. -/
theorem eckmann_hilton {M : Type*} (m₁ m₂ : M → M → M) (e₁ e₂ : M)
    (h₁l : ∀ a, m₁ e₁ a = a) (h₁r : ∀ a, m₁ a e₁ = a)
    (h₂l : ∀ a, m₂ e₂ a = a) (h₂r : ∀ a, m₂ a e₂ = a)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    e₁ = e₂ ∧ (∀ a b, m₁ a b = m₂ a b) ∧ (∀ a b, m₁ a b = m₁ b a) := by
  -- the units agree
  have he : e₁ = e₂ :=
    calc e₁ = m₁ e₁ e₁ := (h₁l e₁).symm
      _ = m₁ (m₂ e₂ e₁) (m₂ e₁ e₂) := by rw [h₂l, h₂r]
      _ = m₂ (m₁ e₂ e₁) (m₁ e₁ e₂) := interchange _ _ _ _
      _ = m₂ e₂ e₂ := by rw [h₁r, h₁l]
      _ = e₂ := h₂l e₂
  -- the operations agree
  have hm : ∀ a b, m₁ a b = m₂ a b := fun a b =>
    calc m₁ a b = m₁ (m₂ a e₂) (m₂ e₂ b) := by rw [h₂r, h₂l]
      _ = m₂ (m₁ a e₂) (m₁ e₂ b) := interchange _ _ _ _
      _ = m₂ a b := by rw [← he, h₁r, h₁l]
  refine ⟨he, hm, fun a b => ?_⟩
  -- and the operation is commutative
  calc m₁ a b = m₁ (m₂ e₂ a) (m₂ b e₂) := by rw [h₂l, h₂r]
    _ = m₂ (m₁ e₂ b) (m₁ a e₂) := interchange _ _ _ _
    _ = m₂ b a := by rw [← he, h₁l, h₁r]
    _ = m₁ b a := (hm b a).symm
-- @endregion

open Topology in
-- @region homotopy_theory.pi_comm
-- @provenance library
/-- **Higher homotopy groups are abelian:** `πₙ₊₂(X, x)` is commutative. This uses Mathlib's
instance `HomotopyGroup.commGroup`, which is built with `EckmannHilton.commGroup` from the
interchange law for concatenation in two different cube directions. -/
theorem pi_comm (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X)
    (a b : π_ (n + 2) X x) : a * b = b * a :=
  mul_comm a b
-- @endregion

open Topology in
-- @region homotopy_theory.pi_one
-- @provenance library
/-- `π₁(X, x)`, defined with cubes, is isomorphic as a group to the fundamental group of loops
up to homotopy. This applies Mathlib's `HomotopyGroup.pi1MulEquivFundamentalGroup`. -/
theorem pi_one (X : Type*) [TopologicalSpace X] (x : X) :
    Nonempty (π_ 1 X x ≃* FundamentalGroup X x) :=
  ⟨HomotopyGroup.pi1MulEquivFundamentalGroup⟩
-- @endregion

open Topology Topology.Homotopy in
-- @region homotopy_theory.loops_of_loops
-- @provenance library
/-- **Loops of loops are higher loops:** the space of `M`-cubes in the space of `N`-cubes of `X`
is homeomorphic to the space of `(M ⊕ N)`-cubes of `X`. Taking `M` with one element this is the
statement `Ω(Ωⁿ X) ≅ Ωⁿ⁺¹ X` behind `πₖ(ΩX) ≅ πₖ₊₁(X)`. This applies Mathlib's
`GenLoop.genLoopGenLoopEquiv`. -/
theorem loops_of_loops (M N : Type*) (X : Type*) [TopologicalSpace X] (x : X) :
    Nonempty (Ω^ M (Ω^ N X x) GenLoop.const ≃ₜ Ω^ (M ⊕ N) X x) :=
  ⟨GenLoop.genLoopGenLoopEquiv x⟩
-- @endregion

/-! ### The Hopf map -/

open ComplexConjugate

-- @region homotopy_theory.hopf
-- @provenance definition
/-- The **Hopf map** `ℂ² → ℂ × ℝ ≅ ℝ³`, `(z, w) ↦ (2 z w̄, |z|² - |w|²)`. Restricted to the unit
sphere `S³ ⊂ ℂ²` it is the Hopf fibration `S³ → S²`. -/
noncomputable def hopf (p : ℂ × ℂ) : ℂ × ℝ :=
  (2 * p.1 * conj p.2, Complex.normSq p.1 - Complex.normSq p.2)
-- @endregion

-- @region homotopy_theory.hopf_mem_sphere
-- @provenance independent
/-- The Hopf map sends `S³` to `S²`: if `|z|² + |w|² = 1` then
`|2 z w̄|² + (|z|² - |w|²)² = 4|z|²|w|² + (|z|² - |w|²)² = (|z|² + |w|²)² = 1`. -/
theorem hopf_mem_sphere (z w : ℂ) (h : Complex.normSq z + Complex.normSq w = 1) :
    Complex.normSq (hopf (z, w)).1 + (hopf (z, w)).2 ^ 2 = 1 := by
  simp only [hopf, Complex.normSq_mul, Complex.normSq_conj]
  have h2 : Complex.normSq 2 = 4 := by norm_num [Complex.normSq_apply]
  rw [h2]
  linear_combination (Complex.normSq z + Complex.normSq w + 1) * h
-- @endregion

-- @region homotopy_theory.hopf_circle_invariant
-- @provenance independent
/-- The Hopf map is constant on circles: multiplying `(z, w)` by a unit complex number `λ`
does not change `hopf (z, w)`, because `λ λ̄ = |λ|² = 1`. -/
theorem hopf_circle_invariant (l z w : ℂ) (hl : Complex.normSq l = 1) :
    hopf (l * z, l * w) = hopf (z, w) := by
  have hc : l * conj l = 1 := by rw [Complex.mul_conj, hl, Complex.ofReal_one]
  unfold hopf
  ext
  · -- first component: `2 (λz) conj(λw) = 2 z w̄ · λλ̄`
    simp only [map_mul]
    linear_combination (2 * z * conj w) * hc
  · -- second component: `|λz|² - |λw|² = |λ|² (|z|² - |w|²)`
    simp only [Complex.normSq_mul, hl, one_mul]
-- @endregion

-- @region homotopy_theory.hopf_fibre
-- @provenance independent
/-- **The fibres of the Hopf map are exactly circles.** If two points `(z, w)` and `(z', w')` of
`S³` have the same image, then `(z', w') = λ · (z, w)` for a unit complex number `λ`; one can
take the Hermitian inner product `λ = z' z̄ + w' w̄`. Together with `hopf_circle_invariant`, the
fibre over each point of `S²` is a great circle of `S³`. -/
theorem hopf_fibre (z w z' w' : ℂ) (hs : Complex.normSq z + Complex.normSq w = 1)
    (hs' : Complex.normSq z' + Complex.normSq w' = 1) (heq : hopf (z, w) = hopf (z', w')) :
    ∃ l : ℂ, Complex.normSq l = 1 ∧ z' = l * z ∧ w' = l * w := by
  simp only [hopf, Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  -- the moduli agree
  have hz : Complex.normSq z = Complex.normSq z' := by linarith
  have hw : Complex.normSq w = Complex.normSq w' := by linarith
  -- the same facts as identities of complex numbers
  have e1 : z * conj w = z' * conj w' := by linear_combination h1 / 2
  have e1c : conj z * w = conj z' * w' := by
    have := congrArg conj e1
    simpa [map_mul, mul_comm] using this
  have mz : z * conj z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have mw : w * conj w = (Complex.normSq w : ℂ) := Complex.mul_conj w
  have mz' : z' * conj z' = (Complex.normSq z' : ℂ) := Complex.mul_conj z'
  have mw' : w' * conj w' = (Complex.normSq w' : ℂ) := Complex.mul_conj w'
  have cz : (Complex.normSq z : ℂ) = Complex.normSq z' := by rw [hz]
  have cw : (Complex.normSq w : ℂ) = Complex.normSq w' := by rw [hw]
  have cs : (Complex.normSq z : ℂ) + Complex.normSq w = 1 := by
    rw [← Complex.ofReal_add, hs, Complex.ofReal_one]
  -- the circle parameter is the Hermitian inner product of the two points
  set l := z' * conj z + w' * conj w with hl
  have hz' : z' = l * z := by
    rw [hl]
    linear_combination (-z') * mz + (-w') * e1 + (-z') * mw' + z' * cw + (-z') * cs
  have hw' : w' = l * w := by
    rw [hl]
    linear_combination (-z') * e1c + (-w') * mz' + (-w') * mw + w' * cz + (-w') * cs
  refine ⟨l, ?_, hz', hw'⟩
  -- `1 = |z'|² + |w'|² = |λ|² (|z|² + |w|²) = |λ|²`
  have k1 : Complex.normSq z' = Complex.normSq l * Complex.normSq z := by
    rw [← Complex.normSq_mul, ← hz']
  have k2 : Complex.normSq w' = Complex.normSq l * Complex.normSq w := by
    rw [← Complex.normSq_mul, ← hw']
  linear_combination (-Complex.normSq l) * hs - k1 - k2 + hs'
-- @endregion

/-! ### Exact sequences -/

-- @region homotopy_theory.bijective_of_exact
-- @provenance independent
/-- **An exact sequence flanked by trivial groups.** If `A → B → C → D` is exact at `B` and at
`C` (kernel = image) and `A`, `D` are trivial, then `g : B → C` is bijective. In the long exact
sequence of the Hopf fibration, `π₃(S¹) → π₃(S³) → π₃(S²) → π₂(S¹)` with `πₖ(S¹) = 0` for
`k ≥ 2`, this gives `π₃(S²) ≅ π₃(S³) ≅ ℤ`. -/
theorem bijective_of_exact {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    [Subsingleton A] [Subsingleton D] (f : A →* B) (g : B →* C) (k : C →* D)
    (exactB : ∀ b, g b = 1 ↔ ∃ a, f a = b) (exactC : ∀ c, k c = 1 ↔ ∃ b, g b = c) :
    Function.Bijective g := by
  constructor
  · -- injective: the kernel of `g` is the image of the trivial group `A`
    intro b₁ b₂ h
    have hker : g (b₁⁻¹ * b₂) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    obtain ⟨a, ha⟩ := (exactB _).1 hker
    have ha1 : a = 1 := Subsingleton.elim a 1
    rw [ha1, map_one] at ha
    -- `1 = b₁⁻¹ * b₂`, so `b₁ = b₂`
    exact inv_mul_eq_one.mp ha.symm
  · -- surjective: everything is in the kernel of the map to the trivial group `D`
    intro c
    exact (exactC c).1 (Subsingleton.elim _ _)
-- @endregion

end Lumenary.HomotopyTheory
