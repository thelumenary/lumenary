/-
The Lumenary — formal mathematics
Higher categories: the interchange law for natural transformations, the Eckmann–Hilton
argument, and why 2-endomorphisms of an identity 1-morphism commute in any bicategory.

What is proved here. `interchange` proves the interchange law in the 2-category `Cat` from
naturality, and `eckmann_hilton` and `endo_id_comm` are proved from the axioms, mirroring the
lesson's proofs. Mathlib already provides bicategories (`CategoryTheory.Bicategory`, with
associators and unitors and the pentagon and triangle axioms), the strict 2-category `Cat`,
pseudofunctors, the monoidal category of endomorphisms of an object, and the one-object
bicategory of a monoidal category, and the coherence theorem in the form "the free bicategory on
a quiver is locally thin"; the library declarations below point to them. Not formalised here
(or, as far as we know, in Mathlib): the strictification theorem "every bicategory is
biequivalent to a strict 2-category", tricategories and Gray-categories, and any definition of
weak n-category for n ≥ 3.
-/
import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Bicategory.SingleObj
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.GroupTheory.EckmannHilton

namespace Lumenary.HigherCategories

open CategoryTheory

/-! ### The 2-category `Cat`: vertical and horizontal composition -/

-- @region higher_categories.interchange
-- @provenance independent
/-- **The interchange law** in the 2-category of categories. For natural transformations
`α : F ⟶ G`, `β : G ⟶ H` (between functors `C ⥤ D`) and `γ : I ⟶ J`, `δ : J ⟶ K` (between
functors `D ⥤ E`), composing vertically first and then horizontally (`◫`) gives the same
result as composing horizontally first and then vertically:
`(α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ (β ◫ δ)`.
Mathlib's horizontal composite has components `(α ◫ γ)_X = γ_{F X} ≫ J(α_X)`. At an object `X`
the two sides differ only by the order of `δ_{F X}` and `J(α_X)`, and the naturality square
of `δ` at the morphism `α_X` swaps them. -/
theorem interchange {C D E : Type*} [Category C] [Category D] [Category E]
    {F G H : C ⥤ D} {I J K : D ⥤ E}
    (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ (β ◫ δ) := by
  ext X
  simp only [NatTrans.hcomp_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  -- Goal: γ ≫ δ_{FX} ≫ K(α_X) ≫ K(β_X) = γ ≫ J(α_X) ≫ δ_{GX} ≫ K(β_X) (γ at F X).
  -- Naturality of `δ` at `α_X : F X ⟶ G X`: `J(α_X) ≫ δ_{GX} = δ_{FX} ≫ K(α_X)`.
  rw [δ.naturality_assoc]
-- @endregion

-- @region higher_categories.interchange_library
-- @provenance library
/-- The interchange law again, now by Mathlib's `CategoryTheory.NatTrans.exchange`
(proved there by the automation `cat_disch`, which finds the same naturality argument). -/
theorem interchange_library {C D E : Type*} [Category C] [Category D] [Category E]
    {F G H : C ⥤ D} {I J K : D ⥤ E}
    (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ (β ◫ δ) :=
  NatTrans.exchange α β γ δ
-- @endregion

-- @region higher_categories.cat_strict
-- @provenance library
/-- Categories, functors and natural transformations form a **strict** 2-category: composition
of functors is associative and unital on the nose, so Mathlib's bicategory structure on `Cat`
has associators and unitors that are identities (`eqToIso` of equalities). This is Mathlib's
instance `CategoryTheory.Cat.bicategory.strict`. -/
theorem cat_strict : Bicategory.Strict Cat.{0, 0} :=
  inferInstance
-- @endregion

/-! ### The Eckmann–Hilton argument -/

-- @region higher_categories.units_coincide
-- @provenance independent
/-- If two binary operations each have a two-sided unit (`e₁` for `m₁`, `e₂` for `m₂`) and
satisfy the interchange law `m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)`, then the units are
equal. Proof: put `a = d = e₂` and `b = c = e₁` in the interchange law; the left side
collapses to `m₁ e₁ e₁ = e₁` and the right side to `m₂ e₂ e₂ = e₂`. -/
theorem units_coincide {X : Type*} (m₁ m₂ : X → X → X) (e₁ e₂ : X)
    (h₁l : ∀ a, m₁ e₁ a = a) (h₁r : ∀ a, m₁ a e₁ = a)
    (h₂l : ∀ a, m₂ e₂ a = a) (h₂r : ∀ a, m₂ a e₂ = a)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    e₁ = e₂ :=
  calc e₁ = m₁ e₁ e₁ := (h₁l e₁).symm
    _ = m₁ (m₂ e₂ e₁) (m₂ e₁ e₂) := by rw [h₂l, h₂r]
    _ = m₂ (m₁ e₂ e₁) (m₁ e₁ e₂) := interchange e₂ e₁ e₁ e₂
    _ = m₂ e₂ e₂ := by rw [h₁l, h₁r]
    _ = e₂ := h₂l e₂
-- @endregion

-- @region higher_categories.eckmann_hilton
-- @provenance independent
/-- **The Eckmann–Hilton argument.** Two unital binary operations on the same set that satisfy
the interchange law are equal, and the common operation is commutative. This is the algebra
behind "π₂ is abelian" and behind `endo_id_comm` below. The proof slides `a` and `b` past each
other using the units, exactly as in the lesson's picture of 2-cells moving around each other
in the plane. -/
theorem eckmann_hilton {X : Type*} (m₁ m₂ : X → X → X) (e₁ e₂ : X)
    (h₁l : ∀ a, m₁ e₁ a = a) (h₁r : ∀ a, m₁ a e₁ = a)
    (h₂l : ∀ a, m₂ e₂ a = a) (h₂r : ∀ a, m₂ a e₂ = a)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    (∀ a b, m₁ a b = m₂ a b) ∧ (∀ a b, m₂ a b = m₂ b a) := by
  have he : e₁ = e₂ := units_coincide m₁ m₂ e₁ e₂ h₁l h₁r h₂l h₂r interchange
  subst he
  have same : ∀ a b, m₁ a b = m₂ a b := fun a b =>
    calc m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by rw [h₂r, h₂l]
      _ = m₂ (m₁ a e₁) (m₁ e₁ b) := interchange a e₁ e₁ b
      _ = m₂ a b := by rw [h₁r, h₁l]
  refine ⟨same, fun a b => ?_⟩
  calc m₂ a b = m₁ a b := (same a b).symm
    _ = m₁ (m₂ e₁ a) (m₂ b e₁) := by rw [h₂l, h₂r]
    _ = m₂ (m₁ e₁ b) (m₁ a e₁) := interchange e₁ a b e₁
    _ = m₂ b a := by rw [h₁l, h₁r]
-- @endregion

-- @region higher_categories.eckmann_hilton_library
-- @provenance library
/-- Mathlib's version: `EckmannHilton.mul_comm` (in `Mathlib.GroupTheory.EckmannHilton`), stated
with Mathlib's `EckmannHilton.IsUnital`. Mathlib uses it to prove that the higher homotopy groups
`πₙ` with `n ≥ 2` are commutative. -/
theorem eckmann_hilton_library {X : Type*} {m₁ m₂ : X → X → X} {e₁ e₂ : X}
    (h₁ : EckmannHilton.IsUnital m₁ e₁) (h₂ : EckmannHilton.IsUnital m₂ e₂)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    ∀ a b, m₂ a b = m₂ b a :=
  (EckmannHilton.mul_comm h₁ h₂ interchange).comm
-- @endregion

/-! ### Bicategories -/

open Bicategory in
-- @region higher_categories.endo_id_comm
-- @provenance independent
/-- **2-endomorphisms of an identity 1-morphism commute**, in any bicategory: for 2-morphisms
`η θ : 𝟙 a ⟶ 𝟙 a`, `η ≫ θ = θ ≫ η`. This is Eckmann–Hilton inside a bicategory. The two
"operations" are vertical composition and horizontal composition (whiskering), and the
interchange law is Mathlib's axiom `whisker_exchange`. The unitors enter because `𝟙 a ≫ 𝟙 a` is
only isomorphic to `𝟙 a`; the key coherence fact is `λ_(𝟙 a) = ρ_(𝟙 a)` (`unitors_equal`). -/
theorem endo_id_comm {B : Type*} [Bicategory B] {a : B} (η θ : 𝟙 a ⟶ 𝟙 a) :
    η ≫ θ = θ ≫ η := by
  -- Interchange for the two whiskerings of η and θ.
  have ex : 𝟙 a ◁ θ ≫ η ▷ 𝟙 a = η ▷ 𝟙 a ≫ 𝟙 a ◁ θ := whisker_exchange η θ
  -- Whiskering by an identity is conjugation by a unitor; for `𝟙 a` both unitors agree.
  rw [id_whiskerLeft, whiskerRight_id, unitors_equal, unitors_inv_equal] at ex
  -- Now ex : (ρ ≫ θ ≫ ρ⁻¹) ≫ (ρ ≫ η ≫ ρ⁻¹) = (ρ ≫ η ≫ ρ⁻¹) ≫ (ρ ≫ θ ≫ ρ⁻¹).
  simp only [Category.assoc, Iso.inv_hom_id_assoc, cancel_epi] at ex
  -- ex : θ ≫ η ≫ ρ⁻¹ = η ≫ θ ≫ ρ⁻¹; cancel the isomorphism ρ⁻¹ on the right.
  rw [← Category.assoc, ← Category.assoc, cancel_mono] at ex
  exact ex.symm
-- @endregion

-- @region higher_categories.nat_trans_id_comm
-- @provenance library
/-- The special case of `endo_id_comm` in `Cat`: natural transformations from the identity
functor of a category to itself commute. (Their monoid is sometimes called the *centre* of the
category.) This applies Mathlib's `CategoryTheory.NatTrans.id_comm`. -/
theorem nat_trans_id_comm {C : Type*} [Category C] (α β : 𝟭 C ⟶ 𝟭 C) :
    α ≫ β = β ≫ α :=
  NatTrans.id_comm α β
-- @endregion

-- @region higher_categories.free_bicategory_coherence
-- @provenance library
/-- **Coherence for bicategories**, in the form Mathlib proves it: in the free bicategory on a
quiver `B` (1-morphisms are formal composites of arrows of `B` and identities; 2-morphisms are
built from associators, unitors and their inverses only), any two parallel 2-morphisms are
equal. So every "formal" diagram of associators and unitors commutes, in every bicategory. This
applies Mathlib's instance `CategoryTheory.FreeBicategory.locally_thin` (proved by normalisation,
following Beylin and Dybjer). -/
theorem free_bicategory_coherence {B : Type*} [Quiver B] {a b : FreeBicategory B}
    {f g : a ⟶ b} (η θ : f ⟶ g) : η = θ :=
  Subsingleton.elim η θ
-- @endregion

-- @region higher_categories.end_monoidal
-- @provenance definition
/-- **A bicategory with one object is a monoidal category**, one direction: the 1-morphisms
`a ⟶ a` of any object `a` form a monoidal category whose tensor product is composition, whose
unit is `𝟙 a`, and whose associator and unitors are those of the bicategory. This is Mathlib's
instance on `CategoryTheory.EndMonoidal`. -/
abbrev endMonoidal {B : Type*} [Bicategory B] (a : B) : MonoidalCategory (a ⟶ a) :=
  inferInstance
-- @endregion

-- @region higher_categories.single_obj_equiv
-- @provenance definition
/-- The other direction: a monoidal category `C` becomes a bicategory `MonoidalSingleObj C` with a
single object `⋆`, objects of `C` as 1-morphisms and morphisms of `C` as 2-morphisms; and the
monoidal category of endomorphisms of `⋆` is equivalent to `C` again. This is Mathlib's
`CategoryTheory.MonoidalSingleObj.endMonoidalStarFunctorEquivalence`. -/
noncomputable def singleObjEquiv (C : Type*) [Category C] [MonoidalCategory C] :
    EndMonoidal (MonoidalSingleObj.star C) ≌ C :=
  MonoidalSingleObj.endMonoidalStarFunctorEquivalence C
-- @endregion

end Lumenary.HigherCategories
