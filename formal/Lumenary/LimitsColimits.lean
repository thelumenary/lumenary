/-
The Lumenary — formal mathematics
Limits and colimits: equalisers, pullbacks, coequalisers, cones as natural transformations,
limits from products and equalisers, completeness, preservation by hom functors, the p-adic
integers as an inverse limit, and a forgetful functor that does not preserve coproducts.

What is proved here. In the category of types we prove the universal properties of the
equaliser `{x // f x = g x}`, of the pullback `{(a, b) // f a = g b}` and of the coequaliser (a
quotient by the relation `f x ~ g x`), and we check that maps into an equaliser are the same as
maps equalising `f` and `g` — the hom functor preserving an equaliser. We prove that the
canonical map `ℤ ⊔ ℤ → ℤ ∗ ℤ` from the disjoint union of the underlying sets to the underlying set
of the free product is not surjective, so the forgetful functor from groups to sets does not
preserve coproducts (it does preserve limits — a Mathlib instance).

What Mathlib provides, cited as library results. `Cone.w` (a cone is a natural transformation
from a constant functor); `has_limits_of_hasEqualizers_and_products` and
`hasPullbacks_of_hasBinaryProducts_of_hasEqualizers`; the instances that `Type`, `TopCat` and
`GrpCat` have all small limits and `Type`, `TopCat` and `AddCommGrpCat` all small colimits;
`coyoneda_preservesLimits`; `GrpCat.forget_preservesLimits`; the universal property of `ℤ_[p]`
(`PadicInt.lift_spec`, `PadicInt.lift_unique`); and `isLUB_of_tendsto_atTop`, relating the
categorical colimit of an increasing sequence in `(ℝ, ≤)` to its analytic limit.
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Support
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

namespace Lumenary.LimitsColimits

open CategoryTheory Limits Opposite Filter Topology Monoid.Coprod

universe v u

/-! ### Equalisers, pullbacks and coequalisers of types -/

section Types

variable {W X Y Z A B C : Type u}

-- @region limits_colimits.equalizer_universal
-- @provenance independent
/-- **The equaliser in the category of types** of `f g : X → Y` is the subtype
`{x // f x = g x}` with its inclusion. Universal property: every `h : W → X` with
`f ∘ h = g ∘ h` factors through the inclusion by exactly one map `u`, namely
`u w = ⟨h w, _⟩`; uniqueness holds because an element of a subtype is determined by its value. -/
theorem equalizer_universal (f g : X → Y) (h : W → X) (hh : f ∘ h = g ∘ h) :
    ∃! u : W → {x : X // f x = g x}, Subtype.val ∘ u = h := by
  refine ⟨fun w => ⟨h w, congr_fun hh w⟩, rfl, ?_⟩
  intro u hu
  funext w
  exact Subtype.ext (congr_fun hu w)
-- @endregion

-- @region limits_colimits.hom_equalizer_equiv
-- @provenance definition
/-- **Maps into an equaliser are maps that equalise.** For every type `W`, maps
`W → {x // f x = g x}` correspond bijectively to maps `h : W → X` with `f ∘ h = g ∘ h`. In other
words the hom functor `Hom(W, −)` sends the equaliser of `f, g` to the equaliser of
`f ∘ −, g ∘ −` — the simplest case of "hom functors preserve limits". -/
def homEqualizerEquiv (f g : X → Y) (W : Type u) :
    (W → {x : X // f x = g x}) ≃ {h : W → X // f ∘ h = g ∘ h} where
  toFun u := ⟨Subtype.val ∘ u, funext fun w => (u w).2⟩
  invFun h := fun w => ⟨h.1 w, congr_fun h.2 w⟩
  left_inv _ := rfl
  right_inv _ := rfl
-- @endregion

-- @region limits_colimits.pullback_universal
-- @provenance independent
/-- **The pullback in the category of types** of `f : A → C` and `g : B → C` is the subtype
`{(a, b) // f a = g b}` of `A × B` — the equaliser of `f ∘ fst` and `g ∘ snd`, exactly the
construction "limits from products and equalisers". Universal property: maps `a : W → A`,
`b : W → B` with `f ∘ a = g ∘ b` factor through it by exactly one map, `w ↦ (a w, b w)`. -/
theorem pullback_universal (f : A → C) (g : B → C) (a : W → A) (b : W → B)
    (hab : f ∘ a = g ∘ b) :
    ∃! u : W → {p : A × B // f p.1 = g p.2},
      (fun w => (u w).1.1) = a ∧ (fun w => (u w).1.2) = b := by
  refine ⟨fun w => ⟨(a w, b w), congr_fun hab w⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro u ⟨h₁, h₂⟩
  funext w
  exact Subtype.ext (Prod.ext (congr_fun h₁ w) (congr_fun h₂ w))
-- @endregion

-- @region limits_colimits.coeq_rel
-- @provenance definition
/-- The relation generating the **coequaliser** of `f g : X → Y`: `f x` is related to `g x`. -/
def CoeqRel (f g : X → Y) : Y → Y → Prop :=
  fun y y' => ∃ x, f x = y ∧ g x = y'
-- @endregion

-- @region limits_colimits.coequalizer_universal
-- @provenance independent
/-- **The coequaliser in the category of types** is the quotient `Quot (CoeqRel f g)` of `Y` by
the equivalence relation generated by `f x ~ g x`, with the quotient map. Universal property:
every `h : Y → Z` with `h ∘ f = h ∘ g` factors through the quotient by exactly one map
(`Quot.lift`); uniqueness holds because every element of the quotient is a class `[y]`. Colimits
of types glue, limits of types carve out. -/
theorem coequalizer_universal (f g : X → Y) (h : Y → Z) (hh : h ∘ f = h ∘ g) :
    ∃! u : Quot (CoeqRel f g) → Z, u ∘ Quot.mk _ = h := by
  refine ⟨Quot.lift h ?_, rfl, ?_⟩
  · rintro _ _ ⟨x, rfl, rfl⟩
    exact congr_fun hh x
  · intro u hu
    funext q
    induction q using Quot.ind with
    | mk y => exact congr_fun hu y
-- @endregion

end Types

/-! ### General limits (Mathlib) -/

section General

-- @region limits_colimits.cone_naturality
-- @provenance library
/-- **A cone is a natural transformation from a constant functor.** A cone over `F : J ⥤ C` has
an apex and legs `c.π.app j : apex ⟶ F j`; naturality of `c.π : const apex ⟶ F` at
`f : j ⟶ j'` says exactly that the legs are compatible: `F f ∘ π_j = π_j'`. This is Mathlib's
`Cone.w`. -/
theorem cone_naturality {J : Type*} [Category J] {C : Type*} [Category C] {F : J ⥤ C}
    (c : Cone F) {j j' : J} (f : j ⟶ j') : c.π.app j ≫ F.map f = c.π.app j' :=
  c.w f
-- @endregion

-- @region limits_colimits.limits_of_products_equalizers
-- @provenance library
/-- **Products and equalisers give all limits.** A category with all small products and all
equalisers has all small limits: the limit of `F` is the equaliser of two maps
`∏ⱼ F j ⇉ ∏_{u : i ⟶ j} F j`. This applies Mathlib's `has_limits_of_hasEqualizers_and_products`;
the lesson proves it. -/
theorem limits_of_products_equalizers {C : Type u} [Category.{v} C] [HasProducts.{v} C]
    [HasEqualizers C] : HasLimits C :=
  has_limits_of_hasEqualizers_and_products
-- @endregion

-- @region limits_colimits.pullbacks_of_products_equalizers
-- @provenance library
/-- **Binary products and equalisers give pullbacks**: the pullback of `f : A ⟶ C` and
`g : B ⟶ C` is the equaliser of `f ∘ π₁` and `g ∘ π₂` on `A × B`. This applies Mathlib's
`hasPullbacks_of_hasBinaryProducts_of_hasEqualizers`. -/
theorem pullbacks_of_products_equalizers (C : Type u) [Category.{v} C] [HasBinaryProducts C]
    [HasEqualizers C] : HasPullbacks C :=
  hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C
-- @endregion

-- @region limits_colimits.complete_cocomplete
-- @provenance library
/-- **Completeness and cocompleteness.** Types and topological spaces have all small limits and
colimits; groups have all small limits and abelian groups all small colimits. These are Mathlib
instances (limits of types are compatible families, colimits are quotients of disjoint unions). -/
theorem complete_cocomplete :
    HasLimits (Type u) ∧ HasColimits (Type u) ∧ HasLimits TopCat.{u} ∧ HasColimits TopCat.{u} ∧
      HasLimits GrpCat.{u} ∧ HasColimits AddCommGrpCat.{u} :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
-- @endregion

-- @region limits_colimits.hom_preserves_limits
-- @provenance library
/-- **Hom functors preserve limits.** For every object `A`, the functor
`Hom(A, −) = coyoneda.obj (op A) : C ⥤ Type v` sends limit cones to limit cones:
`Hom(A, lim F) ≅ lim Hom(A, F −)`. This is Mathlib's instance `coyoneda_preservesLimits`. -/
theorem hom_preserves_limits {C : Type u} [Category.{v} C] (A : C) :
    PreservesLimits (coyoneda.obj (op A)) :=
  inferInstance
-- @endregion

end General

/-! ### The forgetful functor from groups to sets -/

-- @region limits_colimits.forget_preserves_limits
-- @provenance library
/-- **The forgetful functor `Grp → Set` preserves limits**: the underlying set of a limit of
groups is the limit of the underlying sets (Mathlib's `GrpCat.forget_preservesLimits`). -/
theorem forget_preserves_limits : PreservesLimits (forget GrpCat.{u}) :=
  inferInstance
-- @endregion

-- @region limits_colimits.forget_not_preserves_coproduct
-- @provenance independent
/-- **…but not coproducts.** If the forgetful functor preserved the coproduct `ℤ ∗ ℤ`, the
canonical map from the disjoint union `ℤ ⊔ ℤ` of underlying sets to the underlying set of `ℤ ∗ ℤ`
(sending the summands by `inl`, `inr`) would be a bijection. It is not even surjective: `x y`
(with `x = inl 1`, `y = inr 1`) is not in its image. Proof: map `ℤ ∗ ℤ → S₃` by `x ↦ (0 1)`,
`y ↦ (1 2)` (universal property). Every `inl n` goes to a power of `(0 1)`, which fixes `2`;
every `inr n` to a power of `(1 2)`, which fixes `0`; but `x y` goes to `(0 1)(1 2)`, which moves
both `0` and `2`. -/
theorem forget_not_preserves_coproduct :
    ¬ Function.Surjective (Sum.elim (inl : Multiplicative ℤ →* _) (inr : Multiplicative ℤ →* _) :
      Multiplicative ℤ ⊕ Multiplicative ℤ → Multiplicative ℤ ∗ Multiplicative ℤ) := by
  intro hsurj
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let φ := lift (zpowersHom (Equiv.Perm (Fin 3)) σ) (zpowersHom (Equiv.Perm (Fin 3)) τ)
  obtain ⟨z, hz⟩ := hsurj (inl (Multiplicative.ofAdd 1) * inr (Multiplicative.ofAdd 1))
  have key : φ (inl (Multiplicative.ofAdd 1) * inr (Multiplicative.ofAdd 1)) = σ * τ := by
    simp [φ]
  rcases z with n | n
  · -- `φ (inl n) = σ ^ n` fixes `2`, but `σ * τ` does not.
    have h₁ : φ (inl n) 2 = 2 := by
      simp only [φ, lift_apply_inl, zpowersHom_apply]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by decide) _
    have h₂ : (σ * τ) 2 ≠ 2 := by decide
    simp only [Sum.elim_inl] at hz
    rw [hz, key] at h₁
    exact h₂ h₁
  · -- `φ (inr n) = τ ^ n` fixes `0`, but `σ * τ` does not.
    have h₁ : φ (inr n) 0 = 0 := by
      simp only [φ, lift_apply_inr, zpowersHom_apply]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by decide) _
    have h₂ : (σ * τ) 0 ≠ 0 := by decide
    simp only [Sum.elim_inr] at hz
    rw [hz, key] at h₁
    exact h₂ h₁
-- @endregion

/-! ### The p-adic integers as an inverse limit -/

-- @region limits_colimits.padic_inverse_limit
-- @provenance library
/-- **`ℤ_p` is the inverse limit of the rings `ℤ/pⁿ`.** The reduction maps
`toZModPow n : ℤ_[p] → ℤ/pⁿ` form a cone (they are compatible with the reductions
`ℤ/pⁿ → ℤ/pᵐ`, `m ≤ n`), and it is a limit cone in rings: every compatible family of ring maps
`f n : R → ℤ/pⁿ` comes from exactly one ring map `R → ℤ_[p]`. This applies Mathlib's
`PadicInt.zmod_cast_comp_toZModPow`, `PadicInt.lift_spec` and `PadicInt.lift_unique`. -/
theorem padic_inverse_limit (p : ℕ) [Fact p.Prime] {R : Type*} [NonAssocSemiring R]
    (f : ∀ k : ℕ, R →+* ZMod (p ^ k))
    (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow p hk) _).comp (f k₂) = f k₁) :
    (∀ (m n : ℕ) (h : m ≤ n),
      (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (PadicInt.toZModPow n) =
        PadicInt.toZModPow m) ∧
    ∃! g : R →+* ℤ_[p], ∀ n, (PadicInt.toZModPow n).comp g = f n :=
  ⟨PadicInt.zmod_cast_comp_toZModPow, PadicInt.lift f_compat, PadicInt.lift_spec f_compat,
    fun g hg => (PadicInt.lift_unique f_compat g hg).symm⟩
-- @endregion

/-! ### Categorical limits versus limits of sequences -/

-- @region limits_colimits.increasing_limit_is_colimit
-- @provenance library
/-- **When the two meanings of "limit" meet.** In the poset `(ℝ, ≤)` regarded as a category, an
increasing sequence `u 0 ≤ u 1 ≤ ⋯` is a diagram of shape `ℕ`, and its colimit is its least upper
bound. For such a sequence, converging to `L` (analysis) is the same as `L` being the least upper
bound of its values (category theory). This applies Mathlib's `isLUB_of_tendsto_atTop` and
`tendsto_atTop_isLUB`. -/
theorem increasing_limit_is_colimit {u : ℕ → ℝ} (hu : Monotone u) (L : ℝ) :
    Tendsto u atTop (𝓝 L) ↔ IsLUB (Set.range u) L :=
  ⟨isLUB_of_tendsto_atTop hu, tendsto_atTop_isLUB hu⟩
-- @endregion

end Lumenary.LimitsColimits
