/-
The Lumenary — formal mathematics
The Yoneda lemma: natural transformations out of a representable functor are elements, the
Yoneda embedding is full and faithful, an object is determined by the arrows out of it (or
into it), and Cayley's theorem as the one-object case.

What is proved here. Independently, for any category `C` and functor `F : C ⥤ Type`: the maps
`α ↦ α_A(id_A)` and `x ↦ (f ↦ F(f)(x))` are mutually inverse bijections between
`Nat(Hom(A, −), F)` and `F(A)`, natural in `F` and in `A` (the human proof, line by line);
every natural transformation `Hom(A, −) ⇒ Hom(B, −)` is precomposition with exactly one arrow
`B ⟶ A`, and `Hom(A, −) ≅ Hom(B, −)` implies `A ≅ B`; for groups, a permutation of `G` that
commutes with right multiplications is a left multiplication, and `g ↦ (x ↦ g x)` embeds `G`
into its symmetric group (Cayley); for partial orders, `x` is determined by `{z | z ≤ x}`.
From Mathlib (`Mathlib.CategoryTheory.Yoneda`, `Mathlib.CategoryTheory.Limits.Presheaf`): the
contravariant Yoneda bijection `yonedaEquiv`, full faithfulness of `yoneda`, and the density
theorem (every presheaf is a colimit of representables).

Naming: Mathlib's `yoneda : C ⥤ (Cᵒᵖ ⥤ Type)` sends `A` to `Hom(−, A)`, and
`coyoneda : Cᵒᵖ ⥤ (C ⥤ Type)` sends `A` to `Hom(A, −)`. Composition `f ≫ g` means "first `f`,
then `g`".
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.GroupTheory.Perm.Subgroup

namespace Lumenary.Yoneda

open CategoryTheory Opposite

universe u v

section Lemma

variable {C : Type u} [Category.{v} C]

-- @region yoneda.to_element
-- @provenance definition
/-- The Yoneda map: a natural transformation `α : Hom(A, −) ⇒ F` goes to the element
`α_A(id_A) ∈ F(A)` — "where `α` sends the identity". -/
def toElement {A : C} {F : C ⥤ Type v} (α : coyoneda.obj (op A) ⟶ F) : F.obj A :=
  α.app A (𝟙 A)
-- @endregion

-- @region yoneda.of_element
-- @provenance definition
/-- The inverse map: an element `x ∈ F(A)` gives the natural transformation
`Hom(A, −) ⇒ F` whose component at `B` sends `f : A ⟶ B` to `F(f)(x)`. Naturality is
functoriality of `F`: `F(f ≫ g)(x) = F(g)(F(f)(x))`. -/
def ofElement {A : C} {F : C ⥤ Type v} (x : F.obj A) : coyoneda.obj (op A) ⟶ F where
  app B := ↾fun f => F.map f x
  naturality B B' g := by
    ext f
    exact Functor.map_comp_apply F f g x
-- @endregion

-- @region yoneda.of_element_to_element
-- @provenance independent
/-- **The heart of the Yoneda lemma**: a natural transformation `α : Hom(A, −) ⇒ F` is
determined by `α_A(id_A)`. For `f : A ⟶ B`, naturality of `α` along `f` applied to `id_A` gives
`α_B(f) = α_B(id_A ≫ f) = F(f)(α_A(id_A))`. -/
theorem ofElement_toElement {A : C} {F : C ⥤ Type v} (α : coyoneda.obj (op A) ⟶ F) :
    ofElement (toElement α) = α := by
  ext B f
  calc F.map f (α.app A (𝟙 A))
      = α.app B ((coyoneda.obj (op A)).map f (𝟙 A)) := (NatTrans.naturality_apply α f _).symm
    _ = α.app B (𝟙 A ≫ f) := rfl
    _ = α.app B f := by rw [Category.id_comp]
-- @endregion

-- @region yoneda.to_element_of_element
-- @provenance independent
/-- The other composite: the transformation built from `x` sends `id_A` to `F(id_A)(x) = x`. -/
theorem toElement_ofElement {A : C} {F : C ⥤ Type v} (x : F.obj A) :
    toElement (ofElement x) = x :=
  Functor.map_id_apply F A x
-- @endregion

-- @region yoneda.yoneda_bijection
-- @provenance definition
/-- **The Yoneda lemma** (covariant form): `Nat(Hom(A, −), F) ≃ F(A)`, via `α ↦ α_A(id_A)`,
with inverse `x ↦ (f ↦ F(f)(x))`. Packaged from the two theorems above. -/
def yonedaBijection {A : C} {F : C ⥤ Type v} : (coyoneda.obj (op A) ⟶ F) ≃ F.obj A where
  toFun := toElement
  invFun := ofElement
  left_inv := ofElement_toElement
  right_inv := toElement_ofElement
-- @endregion

-- @region yoneda.to_element_natural_functor
-- @provenance independent
/-- The Yoneda bijection is **natural in `F`**: following `α` by a transformation
`β : F ⇒ G` corresponds to applying `β_A` to the element. -/
theorem toElement_natural_functor {A : C} {F G : C ⥤ Type v} (α : coyoneda.obj (op A) ⟶ F)
    (β : F ⟶ G) : toElement (α ≫ β) = β.app A (toElement α) :=
  rfl
-- @endregion

-- @region yoneda.to_element_natural_object
-- @provenance independent
/-- The Yoneda bijection is **natural in `A`**: for `f : A ⟶ A'`, precomposing `α` with
`Hom(f, −) : Hom(A', −) ⇒ Hom(A, −)` corresponds to applying `F(f)` to the element. -/
theorem toElement_natural_object {A A' : C} {F : C ⥤ Type v} (f : A ⟶ A')
    (α : coyoneda.obj (op A) ⟶ F) :
    toElement (coyoneda.map f.op ≫ α) = F.map f (toElement α) := by
  calc toElement (coyoneda.map f.op ≫ α)
      = α.app A' (f ≫ 𝟙 A') := rfl
    _ = α.app A' f := by rw [Category.comp_id]
    _ = (ofElement (toElement α)).app A' f := by rw [ofElement_toElement]
    _ = F.map f (toElement α) := rfl
-- @endregion

-- @region yoneda.nat_trans_representables
-- @provenance independent
/-- **Full and faithful**: every natural transformation `α : Hom(A, −) ⇒ Hom(B, −)` is
precomposition with exactly one arrow `g : B ⟶ A`, namely `g = α_A(id_A)`. This is the Yoneda
lemma for `F = Hom(B, −)`; it says that `coyoneda` is full and faithful. -/
theorem nat_trans_representables {A B : C}
    (α : coyoneda.obj (op A) ⟶ coyoneda.obj (op B)) :
    ∃! g : B ⟶ A, coyoneda.map g.op = α := by
  refine ⟨toElement α, ?_, ?_⟩
  · calc coyoneda.map (toElement α).op = ofElement (toElement α) := by
          ext X f
          rfl
      _ = α := ofElement_toElement α
  · intro g hg
    rw [← hg]
    exact (Category.comp_id g).symm
-- @endregion

-- @region yoneda.iso_of_corepresentable_iso
-- @provenance independent
/-- **An object is determined by the arrows out of it.** If `Hom(A, −) ≅ Hom(B, −)` naturally,
then `A ≅ B`. With `g = e(id_A) : B ⟶ A` and `h = e⁻¹(id_B) : A ⟶ B`, the components of `e` and
`e⁻¹` are precomposition with `g` and `h`, and `e⁻¹ ∘ e = id` evaluated at `id_A` reads
`h ≫ g = id_A`; similarly `g ≫ h = id_B`. -/
theorem iso_of_corepresentable_iso {A B : C}
    (e : coyoneda.obj (op A) ≅ coyoneda.obj (op B)) : Nonempty (A ≅ B) := by
  have hom_app : ∀ (X : C) (f : A ⟶ X), e.hom.app X f = toElement e.hom ≫ f := fun X f =>
    calc e.hom.app X f = (ofElement (toElement e.hom)).app X f := by rw [ofElement_toElement]
      _ = toElement e.hom ≫ f := rfl
  have inv_app : ∀ (X : C) (f : B ⟶ X), e.inv.app X f = toElement e.inv ≫ f := fun X f =>
    calc e.inv.app X f = (ofElement (toElement e.inv)).app X f := by rw [ofElement_toElement]
      _ = toElement e.inv ≫ f := rfl
  refine ⟨⟨toElement e.inv, toElement e.hom, ?_, ?_⟩⟩
  · calc toElement e.inv ≫ toElement e.hom = e.inv.app A (toElement e.hom) := (inv_app A _).symm
      _ = e.inv.app A (e.hom.app A (𝟙 A)) := rfl
      _ = 𝟙 A := by simp
  · calc toElement e.hom ≫ toElement e.inv = e.hom.app B (toElement e.inv) := (hom_app B _).symm
      _ = e.hom.app B (e.inv.app B (𝟙 B)) := rfl
      _ = 𝟙 B := by simp
-- @endregion

-- @region yoneda.yoneda_lemma_library
-- @provenance library
/-- **The Yoneda lemma, contravariant form, from Mathlib**: for a presheaf `P : Cᵒᵖ ⥤ Type`,
`α ↦ α_A(id_A)` is a bijection `Nat(Hom(−, A), P) ≃ P(A)`. This applies Mathlib's
`yonedaEquiv`. -/
theorem yoneda_lemma_library (P : Cᵒᵖ ⥤ Type v) (A : C) :
    Function.Bijective (fun α : yoneda.obj A ⟶ P => α.app (op A) (𝟙 A)) :=
  yonedaEquiv.bijective
-- @endregion

-- @region yoneda.yoneda_fully_faithful
-- @provenance library
/-- **The Yoneda embedding `C ⥤ [Cᵒᵖ, Set]` is full and faithful**: `f ↦ yoneda.map f` is a
bijection `Hom(A, B) ≃ Nat(Hom(−, A), Hom(−, B))`. This applies Mathlib's
`Yoneda.fullyFaithful` and `FullyFaithful.map_bijective`. -/
theorem yoneda_fully_faithful (A B : C) :
    Function.Bijective (yoneda.map : (A ⟶ B) → (yoneda.obj A ⟶ yoneda.obj B)) :=
  Yoneda.fullyFaithful.map_bijective A B
-- @endregion

-- @region yoneda.iso_of_representable_iso
-- @provenance library
/-- **An object is determined by the arrows into it**: `Hom(−, A) ≅ Hom(−, B)` implies
`A ≅ B`. This applies Mathlib's `FullyFaithful.preimageIso` to the Yoneda embedding. -/
theorem iso_of_representable_iso {A B : C} (e : yoneda.obj A ≅ yoneda.obj B) :
    Nonempty (A ≅ B) :=
  ⟨Yoneda.fullyFaithful.preimageIso e⟩
-- @endregion

-- @region yoneda.density
-- @provenance library
/-- **Density: every presheaf is a colimit of representables.** For `P : Cᵒᵖ ⥤ Type`, the
cocone over all representables `Hom(−, A) ⟶ P` with apex `P` is a colimit cocone. This applies
Mathlib's `Presheaf.isColimitTautologicalCocone` (Kashiwara–Schapira, Prop. 2.6.3). -/
theorem density (P : Cᵒᵖ ⥤ Type v) :
    Nonempty (Limits.IsColimit (Presheaf.tautologicalCocone P)) :=
  ⟨Presheaf.isColimitTautologicalCocone P⟩
-- @endregion

end Lemma

/-! ### The one-object case: Cayley's theorem -/

section Cayley

variable {G : Type*} [Group G]

-- @region yoneda.cayley
-- @provenance definition
/-- The Cayley map `G → Sym(G)`, `g ↦ (x ↦ g x)` (Mathlib's `Equiv.mulLeft g`). It is the
Yoneda embedding of the one-object category of `G`: arrow `g` goes to "compose with `g`". -/
def cayley : G →* Equiv.Perm G where
  toFun g := Equiv.mulLeft g
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp
-- @endregion

-- @region yoneda.cayley_injective
-- @provenance independent
/-- **Cayley's theorem**: the Cayley map is injective, so every group is isomorphic to a group
of permutations (its image). Evaluate at `1`: if `g · 1 = h · 1` then `g = h` — the faithful
half of Yoneda, "a transformation is determined by where it sends the identity". -/
theorem cayley_injective : Function.Injective (cayley : G →* Equiv.Perm G) := by
  intro g h hgh
  have h1 : cayley g 1 = cayley h 1 := by rw [hgh]
  simpa [cayley] using h1
-- @endregion

-- @region yoneda.equivariant_eq_cayley
-- @provenance independent
/-- **The full half: the image of Cayley's map is exactly the equivariant permutations.**
A permutation `σ` of `G` that commutes with every right multiplication
(`σ (x h) = σ(x) h` — a natural transformation of the representable functor of the one-object
category) is left multiplication by `σ(1)`: `σ(x) = σ(1 · x) = σ(1) x`. -/
theorem equivariant_eq_cayley (σ : Equiv.Perm G) (hσ : ∀ x h : G, σ (x * h) = σ x * h) :
    σ = cayley (σ 1) := by
  ext x
  calc σ x = σ (1 * x) := by rw [one_mul]
    _ = σ 1 * x := hσ 1 x
    _ = cayley (σ 1) x := rfl
-- @endregion

-- @region yoneda.cayley_library
-- @provenance library
/-- Cayley's theorem from Mathlib: `G` is isomorphic to a subgroup of the permutations of `G`.
This applies Mathlib's `Equiv.Perm.subgroupOfMulAction` for the faithful action of `G` on
itself by left multiplication. -/
theorem cayley_library : Nonempty (G ≃* (MulAction.toPermHom G G).range) :=
  ⟨Equiv.Perm.subgroupOfMulAction G G⟩
-- @endregion

end Cayley

/-! ### Thin categories: an element is determined by what lies below it -/

section Preorder

variable {P : Type*}

-- @region yoneda.le_iff_forall_le
-- @provenance independent
/-- **Yoneda for preorders.** In a preorder (a category with at most one arrow between two
objects), `x ≤ y` exactly when everything below `x` is below `y`: "`Hom(−, x) ⇒ Hom(−, y)`
exists iff `Hom(x, y)` is inhabited". Forwards by transitivity; backwards apply the hypothesis
to `z = x` (the identity `x ≤ x`). -/
theorem le_iff_forall_le [Preorder P] (x y : P) : x ≤ y ↔ ∀ z, z ≤ x → z ≤ y :=
  ⟨fun hxy _ hzx => le_trans hzx hxy, fun h => h x (le_refl x)⟩
-- @endregion

-- @region yoneda.eq_of_forall_le_iff
-- @provenance independent
/-- **The Yoneda principle for partial orders**: if exactly the same elements lie below `x` and
below `y`, then `x = y`. (Mathlib has this as `eq_of_forall_le_iff`.) -/
theorem eq_of_same_lower [PartialOrder P] {x y : P} (h : ∀ z, z ≤ x ↔ z ≤ y) : x = y :=
  le_antisymm ((h x).1 (le_refl x)) ((h y).2 (le_refl y))
-- @endregion

end Preorder

end Lumenary.Yoneda
