/-
The Lumenary — formal mathematics
Adjunctions: currying, free monoids, Galois connections, units and counits, and the
preservation of limits by right adjoints.

What is proved here. Currying is the adjunction `− × B ⊣ (−)^B` on types: we give the bijection
`(A × B → C) ≃ (A → B → C)`, prove that it is natural in `A` and in `C`, and verify the triangle
identities for its unit `a ↦ (b ↦ (a, b))` and counit "evaluate". For the free monoid we prove the
uniqueness half of its universal property by induction, and that the unit `of` is not surjective
(an adjunction need not be an equivalence). For Galois connections — adjunctions between
posets — we prove that left adjoints preserve binary joins and the least element, that right
adjoints are unique, and deduce that a map not preserving `⊥` has no right adjoint. Finally we use
"right adjoints preserve limits" (Mathlib) to prove that the functor `X ↦ Option X` (adjoin one
point) on types has no left adjoint, because it does not preserve the terminal object, and no
right adjoint, because it does not preserve the initial object.

What Mathlib provides. `CategoryTheory.Adjunction` (unit–counit form with the triangle identities
`left_triangle_components`, `right_triangle_components`; hom-set form `Adjunction.homEquiv`),
`Adjunction.leftAdjointUniq`, `Adjunction.rightAdjoint_preservesLimits`,
`Adjunction.leftAdjoint_preservesColimits`, `Adjunction.toMonad`, Freyd's adjoint functor theorem
`isRightAdjoint_of_preservesLimits_of_solutionSetCondition`, `GaloisConnection` with
`Set.image_preimage`, `Int.gc_coe_floor` and `Int.gc_ceil_coe`, `FreeMonoid.lift`, and the
tensor–hom adjunction `TensorProduct.lift.equiv`.
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Order.GaloisConnection.Basic

namespace Lumenary.Adjunctions

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂ u

/-! ### Currying: `− × B ⊣ (−)^B` -/

section Currying

variable {A A' B C C' : Type u}

-- @region adjunctions.curry_equiv
-- @provenance definition
/-- **Currying.** Functions of two arguments `A × B → C` correspond bijectively to functions
`A → (B → C)` returning functions: `h ↦ (a ↦ (b ↦ h (a, b)))`, with inverse "uncurrying". This is
the hom-set bijection `Hom(A × B, C) ≅ Hom(A, C^B)` of the adjunction `− × B ⊣ (−)^B`.
(Mathlib: `Equiv.curry`.) -/
def curryEquiv (A B C : Type u) : (A × B → C) ≃ (A → B → C) where
  toFun h a b := h (a, b)
  invFun k p := k p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
-- @endregion

-- @region adjunctions.curry_natural
-- @provenance independent
/-- **The currying bijection is natural in `A` and in `C`.** Precomposing with `u : A' → A` (on
`A × B`, with `u × id`) and postcomposing with `v : C → C'` before currying gives the same as
currying first and then precomposing with `u` and postcomposing with `v` pointwise. Both sides are
`a' ↦ b ↦ v (h (u a', b))`, so Lean accepts `rfl`. -/
theorem curry_natural (u : A' → A) (v : C → C') (h : A × B → C) :
    curryEquiv A' B C' (v ∘ h ∘ Prod.map u id) = fun a' => v ∘ curryEquiv A B C h (u a') :=
  rfl
-- @endregion

-- @region adjunctions.curry_unit
-- @provenance definition
/-- The **unit** of the currying adjunction, `η_A : A → (B → A × B)`, `a ↦ (b ↦ (a, b))`: the
curried form of the identity of `A × B`. -/
def curryUnit (A B : Type u) : A → B → A × B :=
  fun a b => (a, b)
-- @endregion

-- @region adjunctions.curry_counit
-- @provenance definition
/-- The **counit** of the currying adjunction, `ε_C : (B → C) × B → C`, evaluation
`(φ, b) ↦ φ b`: the uncurried form of the identity of `B → C`. -/
def curryCounit (B C : Type u) : (B → C) × B → C :=
  fun p => p.1 p.2
-- @endregion

-- @region adjunctions.curry_triangles
-- @provenance independent
/-- **The triangle identities for currying.**
1. `ε_{A × B} ∘ (η_A × id_B) = id`: pair `(a, b)` ↦ `(η a, b)` ↦ `η a b = (a, b)`.
2. `(ε_C)^B ∘ η_{C^B} = id`: `φ` ↦ `(b ↦ (φ, b))` ↦ `(b ↦ φ b) = φ`.
Both hold by computation. -/
theorem curry_triangles :
    (curryCounit B (A × B) ∘ Prod.map (curryUnit A B) id = id) ∧
      ((fun (k : B → (B → C) × B) => curryCounit B C ∘ k) ∘ curryUnit (B → C) B = id) :=
  ⟨rfl, rfl⟩
-- @endregion

end Currying

/-! ### The free monoid -/

section FreeMonoid

variable {α M : Type u} [Monoid M]

-- @region adjunctions.free_monoid_lift
-- @provenance library
/-- **Free monoid ⊣ forgetful.** Functions `α → M` into (the underlying set of) a monoid
correspond bijectively to monoid homomorphisms `FreeMonoid α →* M`, by extending a function to
words multiplicatively: `Hom_Mon(F α, M) ≅ Hom_Set(α, U M)`. This is Mathlib's `FreeMonoid.lift`,
and naturality in `M` is `FreeMonoid.comp_lift`. -/
theorem free_monoid_lift {N : Type u} [Monoid N] (g : M →* N) (f : α → M) :
    Function.Bijective (FreeMonoid.lift : (α → M) → (FreeMonoid α →* M)) ∧
      g.comp (FreeMonoid.lift f) = FreeMonoid.lift (g ∘ f) :=
  ⟨FreeMonoid.lift.bijective, FreeMonoid.comp_lift g f⟩
-- @endregion

-- @region adjunctions.free_hom_ext
-- @provenance independent
/-- **Uniqueness in the universal property of the free monoid.** Two homomorphisms out of
`FreeMonoid α` that agree on the generators `of x` agree everywhere: by induction on words, using
`f 1 = 1 = g 1` and `f (of x * w) = f (of x) * f w`. -/
theorem free_hom_ext {f g : FreeMonoid α →* M} (h : ∀ x, f (FreeMonoid.of x) = g (FreeMonoid.of x)) :
    f = g := by
  refine DFunLike.ext _ _ fun w => ?_
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one]
  | of_mul x w ih => rw [map_mul, map_mul, h x, ih]
-- @endregion

-- @region adjunctions.unit_not_surjective
-- @provenance independent
/-- **The unit of an adjunction need not be an isomorphism.** The unit of free ⊣ forgetful at a
set `α` is `of : α → FreeMonoid α`. It is never surjective: the empty word `1` is not a generator.
So this adjunction is not an equivalence. -/
theorem unit_not_surjective : ¬ Function.Surjective (FreeMonoid.of : α → FreeMonoid α) := by
  intro hs
  obtain ⟨x, hx⟩ := hs 1
  exact FreeMonoid.of_ne_one x hx
-- @endregion

end FreeMonoid

/-! ### Galois connections: adjunctions between posets -/

section Galois

-- @region adjunctions.image_preimage
-- @provenance library
/-- **Image ⊣ preimage.** For `f : α → β`, `f '' S ⊆ T ↔ S ⊆ f ⁻¹' T`: direct image is left adjoint
to inverse image between the power-set lattices. This is Mathlib's `Set.image_preimage`. -/
theorem image_preimage {α β : Type u} (f : α → β) :
    GaloisConnection (Set.image f) (Set.preimage f) :=
  Set.image_preimage
-- @endregion

-- @region adjunctions.floor_ceil
-- @provenance library
/-- **Ceiling ⊣ inclusion ⊣ floor.** For the inclusion `ℤ → ℝ`: `⌈x⌉ ≤ n ↔ x ≤ n` and
`n ≤ ⌊x⌋ ↔ (n : ℝ) ≤ x`. The inclusion has a left adjoint (ceiling) and a right adjoint (floor).
These are Mathlib's `Int.gc_ceil_coe` and `Int.gc_coe_floor`. -/
theorem floor_ceil :
    GaloisConnection (Int.ceil : ℝ → ℤ) (fun n : ℤ => (n : ℝ)) ∧
      GaloisConnection (fun n : ℤ => (n : ℝ)) (Int.floor : ℝ → ℤ) :=
  ⟨Int.gc_ceil_coe, Int.gc_coe_floor⟩
-- @endregion

variable {α β : Type u}

-- @region adjunctions.left_adjoint_sup
-- @provenance independent
/-- **Left adjoints preserve joins** (binary coproducts in a poset). If `l ⊣ u`, then
`l (a ⊔ b) = l a ⊔ l b`. (≤): `a ≤ u (l a ⊔ l b)` because `l a ≤ l a ⊔ l b`, likewise for `b`,
so `a ⊔ b ≤ u (l a ⊔ l b)`, i.e. `l (a ⊔ b) ≤ l a ⊔ l b`. (≥): `l` is monotone.
(Mathlib: `GaloisConnection.l_sup`.) -/
theorem left_adjoint_sup [SemilatticeSup α] [SemilatticeSup β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (a b : α) : l (a ⊔ b) = l a ⊔ l b := by
  apply le_antisymm
  · rw [gc]
    exact sup_le ((gc _ _).1 le_sup_left) ((gc _ _).1 le_sup_right)
  · exact sup_le (gc.monotone_l le_sup_left) (gc.monotone_l le_sup_right)
-- @endregion

-- @region adjunctions.left_adjoint_bot
-- @provenance independent
/-- **Left adjoints preserve the least element** (the empty coproduct, an initial object):
`l ⊥ ≤ b ↔ ⊥ ≤ u b`, which is true for every `b`, so `l ⊥ ≤ ⊥`. -/
theorem left_adjoint_bot [PartialOrder α] [OrderBot α] [PartialOrder β] [OrderBot β] {l : α → β}
    {u : β → α} (gc : GaloisConnection l u) : l ⊥ = ⊥ :=
  le_antisymm ((gc _ _).2 bot_le) bot_le
-- @endregion

-- @region adjunctions.right_adjoint_unique
-- @provenance independent
/-- **Right adjoints are unique.** If `l ⊣ u` and `l ⊣ u'` between partial orders, then `u = u'`:
for every `b` and every `a`, `a ≤ u b ↔ l a ≤ b ↔ a ≤ u' b`, and an element is determined by its
lower set. (This is the poset case of uniqueness of adjoints up to unique isomorphism.) -/
theorem right_adjoint_unique [PartialOrder α] [Preorder β] {l : α → β} {u u' : β → α}
    (gc : GaloisConnection l u) (gc' : GaloisConnection l u') : u = u' := by
  funext b
  apply le_antisymm
  · exact (gc' _ _).1 ((gc _ _).2 le_rfl)
  · exact (gc _ _).1 ((gc' _ _).2 le_rfl)
-- @endregion

-- @region adjunctions.const_true_no_right_adjoint
-- @provenance independent
/-- **Using preservation to rule out an adjoint.** The constant map `Bool → Bool` with value
`true` is monotone, but it sends `⊥ = false` to `true ≠ ⊥`. Left adjoints preserve `⊥`
(`left_adjoint_bot`), so it has no right adjoint. -/
theorem const_true_no_right_adjoint : ¬ ∃ u : Bool → Bool, GaloisConnection (fun _ => true) u := by
  rintro ⟨u, gc⟩
  have h : true = false := left_adjoint_bot gc
  exact Bool.noConfusion h
-- @endregion


-- @region adjunctions.adjoint_functor_theorem_lattices
-- @provenance independent
/-- **The adjoint functor theorem for complete lattices.** If `u : β → α` between complete
lattices preserves all infima (all limits of the poset), then `u` has a left adjoint, given by
the formula `l a = ⨅ { b | a ≤ u b }` (the "best approximation from above").
Proof: `u` is monotone (if `b ≤ b'` then `u b = u (⨅ {b, b'}) = u b ⊓ u b' ≤ u b'`). If
`a ≤ u b` then `b` belongs to the set, so `l a ≤ b`. Conversely `u (l a)` is the infimum of
the `u b` with `a ≤ u b`, all of which are `≥ a`; so `a ≤ u (l a) ≤ u b` whenever `l a ≤ b`. -/
theorem adjoint_functor_theorem_lattices [CompleteLattice α] [CompleteLattice β] (u : β → α)
    (hu : ∀ S : Set β, u (sInf S) = sInf (u '' S)) :
    GaloisConnection (fun a => sInf {b | a ≤ u b}) u := by
  have mono : Monotone u := by
    intro b b' h
    have hpair : u (sInf {b, b'}) = sInf (u '' {b, b'}) := hu {b, b'}
    rw [sInf_pair, inf_eq_left.mpr h, Set.image_pair, sInf_pair] at hpair
    rw [hpair]
    exact inf_le_right
  intro a b
  constructor
  · intro h
    refine le_trans ?_ (mono h)
    rw [hu]
    exact le_sInf (by rintro _ ⟨c, hc, rfl⟩; exact hc)
  · intro h
    exact sInf_le h
-- @endregion

end Galois

/-! ### General adjunctions (Mathlib) -/

section General

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- @region adjunctions.triangle_identities
-- @provenance library
/-- **The triangle identities.** For an adjunction `F ⊣ G` with unit `η` and counit `ε`:
`ε_{F X} ∘ F(η_X) = id_{F X}` and `G(ε_Y) ∘ η_{G Y} = id_{G Y}` (written in diagrammatic order).
These are the fields `left_triangle_components` and `right_triangle_components` of Mathlib's
`Adjunction`. -/
theorem triangle_identities {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) :
    F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) ∧
      adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
  ⟨adj.left_triangle_components X, adj.right_triangle_components Y⟩
-- @endregion

-- @region adjunctions.left_adjoint_unique
-- @provenance library
/-- **Left adjoints are unique up to natural isomorphism**: if `F ⊣ G` and `F' ⊣ G` then
`F ≅ F'`. This applies Mathlib's `Adjunction.leftAdjointUniq` (the isomorphism is moreover
unique compatible with the units). -/
theorem left_adjoint_unique {F F' : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (adj' : F' ⊣ G) :
    Nonempty (F ≅ F') :=
  ⟨Adjunction.leftAdjointUniq adj adj'⟩
-- @endregion

-- @region adjunctions.right_adjoint_preserves_limits
-- @provenance library
/-- **Right adjoints preserve limits, left adjoints preserve colimits** (RAPL). This applies
Mathlib's `Adjunction.rightAdjoint_preservesLimits` and `Adjunction.leftAdjoint_preservesColimits`;
the lesson proves it from the hom-set bijection. -/
theorem right_adjoint_preserves_limits {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesLimitsOfSize.{v₂, u₂} G ∧ PreservesColimitsOfSize.{v₁, u₁} F :=
  ⟨adj.rightAdjoint_preservesLimits, adj.leftAdjoint_preservesColimits⟩
-- @endregion

-- @region adjunctions.adjunction_monad
-- @provenance definition
/-- **Every adjunction induces a monad** `G ∘ F` on `C`, with unit `η` and multiplication
`G ε F : GFGF ⇒ GF`. This is Mathlib's `Adjunction.toMonad`; see the lesson on monads. -/
def adjunctionMonad {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : Monad C :=
  adj.toMonad
-- @endregion


-- @region adjunctions.freyd_adjoint_functor_theorem
-- @provenance library
/-- **Freyd's general adjoint functor theorem.** If `D` is complete (and locally small) and
`G : D ⥤ C` preserves limits and satisfies the *solution set condition* — for each object `A` of
`C`, a set of arrows `A ⟶ G Bᵢ` through which every arrow `A ⟶ G X` factors — then `G` has a
left adjoint. This applies Mathlib's `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`;
`adjoint_functor_theorem_lattices` is the special case of complete lattices, where the solution
set can be taken to be everything. -/
theorem freyd_adjoint_functor_theorem {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₁} D] [HasLimits D] (G : D ⥤ C) [PreservesLimits G]
    (hG : SolutionSetCondition.{v₁} G) : G.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG
-- @endregion

end General

/-! ### The tensor–hom adjunction -/

-- @region adjunctions.tensor_hom
-- @provenance definition
/-- **Tensor–hom adjunction** `− ⊗ N ⊣ Hom(N, −)` for modules over a commutative ring:
bilinear maps `M → N → P` (that is, linear maps `M → Hom(N, P)`) correspond to linear maps
`M ⊗ N → P`. This is Mathlib's `TensorProduct.lift.equiv`, the linear analogue of currying. -/
noncomputable def tensorHom (R M N P : Type u) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] :
    (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] (TensorProduct R M N →ₗ[R] P) :=
  TensorProduct.lift.equiv (RingHom.id R) M N P
-- @endregion

/-! ### A functor with no left adjoint -/

-- @region adjunctions.option_no_left_adjoint
-- @provenance independent
/-- **"Adjoin a point" has no left adjoint on types.** Let `G X = Option X` (that is, `X ⊔ {∗}`).
If `F ⊣ G`, then `G` preserves limits (Mathlib's `rightAdjoint_preservesLimits`), in particular the
terminal object, so `Option PUnit` would be terminal. But there are two different maps
`PUnit → Option PUnit` (constant `none`, constant `some ()`), and a terminal object admits only
one map from each object. -/
theorem option_no_left_adjoint :
    ¬ ∃ F : Type u ⥤ Type u, Nonempty (F ⊣ ofTypeFunctor Option) := by
  rintro ⟨F, ⟨adj⟩⟩
  have := adj.rightAdjoint_preservesLimits
  have hT : IsTerminal ((ofTypeFunctor Option).obj PUnit) :=
    IsTerminal.isTerminalObj _ _ Types.isTerminalPUnit
  have h := hT.hom_ext (↾fun _ : PUnit => (none : Option PUnit))
    (↾fun _ : PUnit => (some PUnit.unit : Option PUnit))
  have h' := ConcreteCategory.congr_hom h PUnit.unit
  simp at h'
-- @endregion

-- @region adjunctions.option_no_right_adjoint
-- @provenance independent
/-- **…and no right adjoint either.** A left adjoint preserves colimits, in particular the initial
object `PEmpty`. But `Option PEmpty` has an element (`none`), so there are two different maps from
it to a two-element type, and it is not initial. (Changing the target category repairs this:
`X ↦ X ⊔ {∗}` is left adjoint to the forgetful functor from *pointed* sets to sets.) -/
theorem option_no_right_adjoint :
    ¬ ∃ G : Type u ⥤ Type u, Nonempty (ofTypeFunctor Option ⊣ G) := by
  rintro ⟨G, ⟨adj⟩⟩
  have := adj.leftAdjoint_preservesColimits
  have hI : IsInitial ((ofTypeFunctor Option).obj PEmpty) :=
    IsInitial.isInitialObj _ _ Types.isInitialPEmpty
  have h := hI.hom_ext (↾fun _ : Option PEmpty => (ULift.up true : ULift.{u} Bool))
    (↾fun _ : Option PEmpty => (ULift.up false : ULift.{u} Bool))
  have h' := ConcreteCategory.congr_hom h (none : Option PEmpty.{u + 1})
  exact Bool.noConfusion (congrArg ULift.down h' : true = false)
-- @endregion

end Lumenary.Adjunctions
