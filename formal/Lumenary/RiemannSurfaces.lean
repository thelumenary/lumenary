/-
The Lumenary — formal mathematics
Riemann surfaces: the square root has no continuous branch on `ℂ ∖ {0}` (so it lives on a
two-sheeted surface), holomorphic functions on a compact Riemann surface are constant, doubly
periodic entire functions are constant, holomorphic maps between complex tori lift to affine
maps of `ℂ`, and the Weierstrass function maps a torus onto a cubic curve.

What is proved here and what Mathlib provides. Mathlib has complex manifolds (manifolds modelled
on `ℂⁿ` with holomorphic transition maps) and proves that a holomorphic function on a compact
connected complex manifold is constant; it has Liouville's theorem, lattices in `ℂ` (`PeriodPair`)
and — very recently — the Weierstrass `℘` function with the differential equation
`℘'² = 4℘³ - g₂℘ - g₃`. We cite these. The *independent* declarations prove: the non-existence of
a continuous square root (by connectedness of `[0, 2π]`), Liouville for doubly periodic functions,
and the lemma behind the classification of tori — a holomorphic map of `ℂ` that commutes with
lattice translations up to constants is affine.

Not formalised: Riemann surfaces as one-dimensional complex manifolds in general (Mathlib has the
definitions but not the theory of branched coverings), the Riemann–Hurwitz formula, the
uniformisation theorem, the Riemann–Roch theorem, and the isomorphism between compact Riemann
surfaces and smooth projective curves.
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Topology.Algebra.Field

namespace Lumenary.RiemannSurfaces

open Complex
open scoped Manifold

/-! ### The square root is not a function on `ℂ ∖ {0}` -/

-- @region riemann_surfaces.no_continuous_sqrt
-- @provenance independent
/-- **There is no continuous square root on `ℂ ∖ {0}`.** Suppose `g` were one. Along the circle,
`f(t) = g(e^{it})` and `h(t) = e^{it/2}` are continuous on `[0, 2π]` with `f² = h²` and `h ≠ 0`;
since `[0, 2π]` is connected, `f = h` or `f = -h` throughout. But `f(0) = f(2π) = g(1)`, while
`h(0) = 1` and `h(2π) = e^{iπ} = -1`: contradiction in both cases. The square root becomes a
single-valued continuous (indeed holomorphic) function only on its two-sheeted Riemann surface. -/
theorem no_continuous_sqrt :
    ¬ ∃ g : ℂ → ℂ, ContinuousOn g {z | z ≠ 0} ∧ ∀ z, z ≠ 0 → g z ^ 2 = z := by
  rintro ⟨g, hg, hsq⟩
  set S : Set ℝ := Set.Icc 0 (2 * Real.pi)
  let f : ℝ → ℂ := fun t => g (exp (t * I))
  let h : ℝ → ℂ := fun t => exp (t * I / 2)
  have hexp_ne : ∀ t : ℝ, exp (t * I) ≠ 0 := fun t => exp_ne_zero _
  have hf : ContinuousOn f S := by
    refine hg.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro t _
    exact hexp_ne t
  have hh : ContinuousOn h S := Continuous.continuousOn (by fun_prop)
  have hfh : Set.EqOn (f ^ 2) (h ^ 2) S := by
    intro t _
    simp only [Pi.pow_apply, f, h]
    rw [hsq _ (hexp_ne t), ← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hne : ∀ {t}, t ∈ S → h t ≠ 0 := fun {t} _ => exp_ne_zero _
  have h0 : (0 : ℝ) ∈ S := ⟨le_rfl, by positivity⟩
  have h2 : 2 * Real.pi ∈ S := ⟨by positivity, le_rfl⟩
  have hf0 : f 0 = g 1 := by simp [f]
  have hf2 : f (2 * Real.pi) = g 1 := by
    simp only [f]
    congr 1
    push_cast
    exact exp_two_pi_mul_I
  have hh0 : h 0 = 1 := by simp [h]
  have hh2 : h (2 * Real.pi) = -1 := by
    simp only [h]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * I / 2 = Real.pi * I by push_cast; ring]
    exact exp_pi_mul_I
  rcases (isPreconnected_Icc).eq_or_eq_neg_of_sq_eq hf hh hfh hne with heq | heq
  · have a := heq h0
    have b := heq h2
    rw [hf0, hh0] at a
    rw [hf2, hh2, a] at b
    norm_num at b
  · have a := heq h0
    have b := heq h2
    simp only [Pi.neg_apply] at a b
    rw [hf0, hh0] at a
    rw [hf2, hh2, a] at b
    norm_num at b
-- @endregion

/-! ### Compact Riemann surfaces and complex tori -/

-- @region riemann_surfaces.holomorphic_constant_compact
-- @provenance library
/-- **On a compact connected Riemann surface every holomorphic function is constant** (maximum
modulus). So the interesting functions on a compact Riemann surface are *meromorphic*. Mathlib's
`MDifferentiable.apply_eq_of_compactSpace`, stated for any compact connected complex manifold
without boundary. -/
theorem holomorphic_constant_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [CompactSpace M] [PreconnectedSpace M] {f : M → ℂ}
    (hf : MDifferentiable I (modelWithCornersSelf ℂ ℂ) f) (a b : M) : f a = f b :=
  hf.apply_eq_of_compactSpace a b
-- @endregion

-- @region riemann_surfaces.periodic_lattice
-- @provenance independent
/-- A function with periods `ω₁` and `ω₂` is invariant under the whole lattice
`Λ = ℤω₁ + ℤω₂`: every `w = mω₁ + nω₂ ∈ Λ` is a period. So it is a function on the torus `ℂ/Λ`. -/
theorem periodic_lattice (L : PeriodPair) {f : ℂ → ℂ} (h₁ : ∀ z, f (z + L.ω₁) = f z)
    (h₂ : ∀ z, f (z + L.ω₂) = f z) : ∀ z w, w ∈ L.lattice → f (z + w) = f z := by
  intro z w hw
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
  have p₁ : Function.Periodic f L.ω₁ := h₁
  have p₂ : Function.Periodic f L.ω₂ := h₂
  have hm := (p₁.int_mul m) z
  have hn := (p₂.int_mul n) (z + m * L.ω₁)
  rw [← add_assoc, hn, hm]
-- @endregion

-- @region riemann_surfaces.doubly_periodic_constant
-- @provenance independent
/-- **A doubly periodic entire function is constant.** It is continuous and invariant under the
lattice, so its range is the image of a compact fundamental parallelogram, hence bounded; by
Liouville's theorem it is constant. Equivalently: every holomorphic function on the compact
Riemann surface `ℂ/Λ` is constant. -/
theorem doubly_periodic_constant (L : PeriodPair) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h₁ : ∀ z, f (z + L.ω₁) = f z) (h₂ : ∀ z, f (z + L.ω₂) = f z) (z w : ℂ) : f z = f w := by
  have hc : IsCompact (Set.range f) :=
    IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous (periodic_lattice L h₁ h₂)
  exact hf.apply_eq_apply_of_bounded hc.isBounded z w
-- @endregion

-- @region riemann_surfaces.lift_affine
-- @provenance independent
/-- **Holomorphic maps between tori lift to affine maps.** Let `F : ℂ → ℂ` be entire and suppose
`F(z + ω₁) - F(z)` and `F(z + ω₂) - F(z)` do not depend on `z` (this holds for a lift of a
holomorphic map `ℂ/Λ → ℂ/Λ'`, the differences lying in the discrete set `Λ'`). Then `F' ` is
doubly periodic, hence constant `= a`, and `F(z) = a z + F(0)`. This is the key step in the
classification of complex tori: `ℂ/Λ ≅ ℂ/Λ'` iff `Λ' = aΛ` for some `a ∈ ℂ^×`. -/
theorem lift_affine (L : PeriodPair) {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c₁ c₂ : ℂ}
    (h₁ : ∀ z, F (z + L.ω₁) = F z + c₁) (h₂ : ∀ z, F (z + L.ω₂) = F z + c₂) :
    ∃ a : ℂ, ∀ z, F z = a * z + F 0 := by
  have hd : Differentiable ℂ (deriv F) := fun z =>
    ((hF.differentiableOn.deriv isOpen_univ) z (Set.mem_univ z)).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))
  have per : ∀ (c ω : ℂ), (∀ z, F (z + ω) = F z + c) → ∀ z, deriv F (z + ω) = deriv F z := by
    intro c ω h z
    have e1 : deriv (fun z => F (z + ω)) z = deriv F (z + ω) := deriv_comp_add_const _ _ _
    have e2 : (fun z => F (z + ω)) = fun z => F z + c := funext h
    rw [← e1, e2, deriv_add_const]
  obtain ⟨a, ha⟩ : ∃ a, ∀ z, deriv F z = a :=
    ⟨deriv F 0, fun z => doubly_periodic_constant L hd (per c₁ _ h₁) (per c₂ _ h₂) z 0⟩
  refine ⟨a, fun z => ?_⟩
  have hG : Differentiable ℂ (fun z => F z - a * z) := hF.sub (differentiable_id.const_mul a)
  have hG' : ∀ z, deriv (fun z => F z - a * z) z = 0 := by
    intro z
    have hz : HasDerivAt (fun z => F z - a * z) (deriv F z - a * 1) z :=
      (hF z).hasDerivAt.sub ((hasDerivAt_id' z).const_mul a)
    rw [hz.deriv, ha]
    ring
  have := is_const_of_deriv_eq_zero hG hG' z 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this
-- @endregion

/-! ### The Weierstrass function: a torus is a cubic curve -/

-- @region riemann_surfaces.weierstrass_periodic
-- @provenance library
/-- The **Weierstrass function** `℘(z) = 1/z² + Σ_{w ∈ Λ ∖ 0} (1/(z - w)² - 1/w²)` is periodic
for the lattice `Λ`, so it is a meromorphic function on the torus `ℂ/Λ` (with a double pole at
`0`). Mathlib's `PeriodPair.weierstrassP_add_coe`. -/
theorem weierstrass_periodic (L : PeriodPair) (z : ℂ) (w : L.lattice) :
    L.weierstrassP (z + w) = L.weierstrassP z :=
  L.weierstrassP_add_coe z w
-- @endregion

-- @region riemann_surfaces.weierstrass_cubic
-- @provenance library
/-- **The torus is a cubic curve.** Away from the lattice, `℘'(z)² = 4℘(z)³ - g₂℘(z) - g₃`, so
`z ↦ (℘(z), ℘'(z))` maps `ℂ/Λ` minus a point into the affine curve `y² = 4x³ - g₂x - g₃`; sending
`0` to the point at infinity gives a biholomorphism onto the projective cubic. Mathlib's
`PeriodPair.derivWeierstrassP_sq`. -/
theorem weierstrass_cubic (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 - L.g₂ * L.weierstrassP z - L.g₃ :=
  L.derivWeierstrassP_sq z hz
-- @endregion

end Lumenary.RiemannSurfaces
