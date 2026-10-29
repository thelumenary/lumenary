/-
The Lumenary — formal mathematics
Homotopy and the fundamental group: straight-line homotopies, simply connected spaces, the
covering `ℝ → ℝ/ℤ`, path lifting, `π₁(S¹) ≅ ℤ`, the circle is not a retract of a simply
connected space, the one-dimensional Brouwer theorem, and a non-abelian free group.

What is proved here and what Mathlib provides. Mathlib defines paths (`Path x y`), homotopies of
paths rel endpoints (`Path.Homotopy`), the fundamental group (`FundamentalGroup X x`, the
automorphism group of `x` in the fundamental groupoid), covering maps (`IsCoveringMap`), the
homotopy lifting property, and — very recently — the isomorphism `π₁(ℝ/ℤ) ≅ ℤ` given by the
winding number (`AddCircle.windingNumberIso`). The *library* declarations below cite these.
The *independent* declarations prove lesson results from them: the straight-line homotopy (so
every loop in a real vector space is null-homotopic), functoriality of induced maps, the
theorem that the circle is not a retract of any simply connected space (the heart of the
Brouwer fixed-point theorem; the disc is such a space), the fixed-point theorem for `[0, 1]`,
and the non-commutativity of the free group on two generators, detected by a homomorphism to
the symmetric group `S₃`.

Not formalised here: the Seifert–van Kampen theorem (it is not in Mathlib in topological form),
`π₁(S¹ ∨ S¹) ≅ F₂`, the classification of covering spaces, and the two-dimensional Brouwer
theorem itself (the retraction built from a fixed-point-free map is described in the lesson).
-/
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace Lumenary.FundamentalGroup

open unitInterval

/-! ### Homotopies in a vector space -/

-- @region fundamental_group.smul_combo_self
-- @provenance independent
/-- The convex combination of a vector with itself is that vector: `(1 - t) • v + t • v = v`.
This is why a straight-line homotopy keeps the endpoints of paths fixed. -/
theorem smul_combo_self {E : Type*} [AddCommGroup E] [Module ℝ E] (t : ℝ) (v : E) :
    (1 - t) • v + t • v = v := by
  rw [← add_smul, sub_add_cancel, one_smul]
-- @endregion

-- @region fundamental_group.straight_line_homotopy
-- @provenance definition
/-- **The straight-line homotopy.** Two paths `p`, `q` from `x` to `y` in a real normed space are
deformed into each other by `H(t, s) = (1 - t) • p(s) + t • q(s)`: at time `t = 0` it is `p`, at
`t = 1` it is `q`, and at every time the endpoints stay at `x` and `y`. -/
noncomputable def straightLineHomotopy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (p q : Path x y) : p.Homotopy q where
  toFun z := (1 - (z.1 : ℝ)) • p z.2 + (z.1 : ℝ) • q z.2
  continuous_toFun := by fun_prop
  map_zero_left s := by simp
  map_one_left s := by simp
  prop' t s hs := by
    rcases hs with rfl | hs
    · simp only [ContinuousMap.coe_mk, Path.coe_toContinuousMap, Path.source]
      exact smul_combo_self _ _
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      simp only [ContinuousMap.coe_mk, Path.coe_toContinuousMap, Path.target]
      exact smul_combo_self _ _
-- @endregion

-- @region fundamental_group.paths_homotopic_in_vector_space
-- @provenance independent
/-- In a real normed space any two paths with the same endpoints are homotopic rel endpoints,
via `straightLineHomotopy`. -/
theorem paths_homotopic_in_vector_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (p q : Path x y) : p.Homotopic q :=
  ⟨straightLineHomotopy p q⟩
-- @endregion

-- @region fundamental_group.loop_nullhomotopic
-- @provenance independent
/-- Every loop in a real normed space (such as `ℝⁿ`, or the plane containing a disc) is
homotopic to the constant loop: the fundamental group is trivial. -/
theorem loop_nullhomotopic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (γ : Path x x) : γ.Homotopic (Path.refl x) :=
  paths_homotopic_in_vector_space γ (Path.refl x)
-- @endregion

-- @region fundamental_group.vector_space_simply_connected
-- @provenance library
/-- A real normed space is simply connected. Mathlib gets this from contractibility
(`RealTopologicalVectorSpace.contractibleSpace` and `SimplyConnectedSpace.ofContractible`). -/
theorem vector_space_simply_connected (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    SimplyConnectedSpace E :=
  inferInstance
-- @endregion

/-! ### Induced homomorphisms and change of basepoint -/

-- @region fundamental_group.map_comp
-- @provenance independent
/-- **Functoriality.** The homomorphism induced by a composite `g ∘ f` is the composite of the
induced homomorphisms: `(g ∘ f)_* = g_* ∘ f_*`. In Mathlib `FundamentalGroup.map f x` sends the
class of a loop `γ` to the class of `f ∘ γ`; both sides send the class of `γ` to the class of
`g ∘ f ∘ γ`, so we check the equation on a representative loop. -/
theorem map_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x = (FundamentalGroup.map g (f x)).comp
      (FundamentalGroup.map f x) := by
  ext γ
  rcases γ with ⟨γ⟩
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p => rfl
-- @endregion

-- @region fundamental_group.change_of_basepoint
-- @provenance library
/-- **Change of basepoint.** A path `p` from `x₀` to `x₁` gives an isomorphism
`π₁(X, x₀) ≅ π₁(X, x₁)`, sending a loop `γ` to `p⁻¹ · γ · p`. This applies Mathlib's
`FundamentalGroup.fundamentalGroupMulEquivOfPath`. -/
theorem change_of_basepoint {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (p : Path x₀ x₁) :
    Nonempty (FundamentalGroup X x₀ ≃* FundamentalGroup X x₁) :=
  ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath p⟩
-- @endregion

/-! ### The circle -/

-- @region fundamental_group.fact_one_pos
-- @provenance definition
/-- Mathlib's circle `AddCircle p = ℝ/pℤ` needs to know that the period is positive. We use the
period `1`, so `AddCircle 1` is `ℝ/ℤ`. -/
instance fact_one_pos : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
-- @endregion

-- @region fundamental_group.covering_real_circle
-- @provenance library
/-- **`ℝ → ℝ/ℤ` is a covering map**: each point of the circle has a neighbourhood whose preimage
is a disjoint union of copies of it, one for each integer translate. This applies Mathlib's
`AddCircle.isCoveringMap_coe`. -/
theorem covering_real_circle : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1
-- @endregion

-- @region fundamental_group.path_lifting
-- @provenance library
/-- **Path lifting.** Every path `γ` in the circle starting at the image of `e ∈ ℝ` lifts to a
path in `ℝ` starting at `e`. This applies Mathlib's `IsCoveringMap.exists_path_lifts`. -/
theorem path_lifting (γ : C(I, AddCircle (1 : ℝ))) (e : ℝ) (h : γ 0 = e) :
    ∃ Γ : C(I, ℝ), (↑) ∘ Γ = γ ∧ Γ 0 = e :=
  covering_real_circle.exists_path_lifts γ e h
-- @endregion

-- @region fundamental_group.pi1_circle
-- @provenance library
/-- **`π₁(S¹) ≅ ℤ`.** The fundamental group of the circle `ℝ/ℤ`, at any basepoint, is
isomorphic to the integers; the isomorphism is the winding number. This applies Mathlib's
`AddCircle.windingNumberIso`, proved with the covering `ℝ → ℝ/ℤ` and the lifting theorems. -/
theorem pi1_circle (x : AddCircle (1 : ℝ)) :
    Nonempty (FundamentalGroup (AddCircle (1 : ℝ)) x ≃* Multiplicative ℤ) :=
  ⟨AddCircle.windingNumberIso x⟩
-- @endregion

-- @region fundamental_group.winding_number_loop
-- @provenance library
/-- The loop `t ↦ n t` (mod 1), which runs `n` times around the circle, has winding number `n`.
So the winding-number isomorphism is onto, and the loop running once around generates `π₁(S¹)`.
This applies Mathlib's `AddCircle.windingNumber_zsmulLoop`. -/
theorem windingNumber_loop (n : ℤ) :
    AddCircle.windingNumber (x := ((0 : ℝ) : AddCircle (1 : ℝ)))
      (.of (.mk (AddCircle.zsmulLoop (1 : ℝ) 0 n))) = n :=
  AddCircle.windingNumber_zsmulLoop 0 n
-- @endregion

-- @region fundamental_group.circle_not_retract
-- @provenance independent
/-- **The circle is not a retract of a simply connected space.** Suppose `i : S¹ → X` and
`r : X → S¹` are continuous with `r ∘ i = id`, and `X` is simply connected (for example, the
closed disc). Take the loop `γ` running once around the circle. Then `i ∘ γ` is null-homotopic
in `X`, so applying `r`, the loop `r ∘ i ∘ γ = γ` is null-homotopic in `S¹`. But homotopic loops
have the same winding number, and `γ` winds once while a constant loop winds zero times. -/
theorem circle_not_retract {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    (i : C(AddCircle (1 : ℝ), X)) (r : C(X, AddCircle (1 : ℝ))) (h : ∀ z, r (i z) = z) :
    False := by
  set x : AddCircle (1 : ℝ) := r (i ((0 : ℝ) : AddCircle (1 : ℝ))) with hx
  let γ := AddCircle.zsmulLoop (1 : ℝ) 0 1
  let δ : Path x x := (γ.map i.continuous).map r.continuous
  -- `i ∘ γ` is null-homotopic in the simply connected space `X`; apply `r`.
  have hδ : δ.Homotopic ((Path.refl (i ((0 : ℝ) : AddCircle (1 : ℝ)))).map r.continuous) :=
    (SimplyConnectedSpace.paths_homotopic (γ.map i.continuous) (Path.refl _)).map r
  -- So `δ` and the constant loop define the same element of `π₁(S¹, x)`.
  have hclass : (FundamentalGroup.fromPath (.mk δ) : FundamentalGroup _ x) =
      FundamentalGroup.fromPath (.mk ((Path.refl _).map r.continuous)) :=
    congrArg _ (Quotient.sound hδ)
  -- The winding number of `δ` is `1`: it has the lift `t ↦ t`, since `r ∘ i = id`.
  have w1 : (AddCircle.windingNumber (FundamentalGroup.fromPath (.mk δ)) : ℝ) = 1 := by
    have hw := AddCircle.windingNumber_eq_div δ ⟨fun t => (t : ℝ), continuous_subtype_val⟩ (by
      funext t
      change ((t : ℝ) : AddCircle (1 : ℝ)) = r (i (AddCircle.zsmulLoop 1 0 1 t))
      rw [h, AddCircle.zsmulLoop_apply]
      simp)
    simpa using hw
  -- The winding number of a constant loop is `0`: it has a constant lift.
  have w0 : (AddCircle.windingNumber
      (FundamentalGroup.fromPath (.mk ((Path.refl (i ((0 : ℝ) : AddCircle (1 : ℝ)))).map
        r.continuous))) : ℝ) = 0 := by
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective x
    have hw := AddCircle.windingNumber_eq_div ((Path.refl _).map r.continuous)
      (ContinuousMap.const I c) (by
        funext t
        simp only [Function.comp_apply, ContinuousMap.const_apply, Path.map_coe,
          Path.refl_apply]
        exact hc)
    simpa using hw
  rw [hclass, w0] at w1
  exact zero_ne_one w1
-- @endregion

/-! ### Fixed points -/

-- @region fundamental_group.brouwer_interval
-- @provenance independent
/-- **Brouwer's theorem in dimension one.** Every continuous map of `[0, 1]` into itself has a
fixed point. Apply the intermediate value theorem to `g(x) = f(x) - x`, which is `≥ 0` at `0`
and `≤ 0` at `1`. (Dimension one needs only connectedness; dimension two needs `π₁(S¹) ≅ ℤ`.) -/
theorem brouwer_interval (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hmaps : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = x := by
  have hg : ContinuousOn (fun x => f x - x) (Set.Icc 0 1) := hf.sub continuousOn_id
  have h0 := hmaps 0 ⟨le_refl 0, zero_le_one⟩
  have h1 := hmaps 1 ⟨zero_le_one, le_refl 1⟩
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1 - 1) (f 0 - 0) :=
    ⟨by linarith [h1.2], by linarith [h0.1]⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' zero_le_one hg hmem
  exact ⟨x, hx, by linarith [hfx]⟩
-- @endregion

/-! ### Fundamental groups need not be abelian -/

-- @region fundamental_group.free_group_not_comm
-- @provenance independent
/-- **The free group on two generators is not abelian.** By van Kampen's theorem it is the
fundamental group of the figure eight `S¹ ∨ S¹` (not formalised here). To see `ab ≠ ba`, send
`a ↦ (0 1)` and `b ↦ (1 2)` in the symmetric group `S₃` (the universal property `FreeGroup.lift`):
the images of `ab` and `ba` are different permutations, which `decide` checks. -/
theorem free_group_not_comm :
    FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 ≠ FreeGroup.of 1 * FreeGroup.of 0 := by
  intro h
  let φ : FreeGroup (Fin 2) →* Equiv.Perm (Fin 3) :=
    FreeGroup.lift (fun i => if i = 0 then Equiv.swap 0 1 else Equiv.swap 1 2)
  have h' := congrArg φ h
  simp only [map_mul, φ, FreeGroup.lift_apply_of] at h'
  revert h'
  decide
-- @endregion

end Lumenary.FundamentalGroup
