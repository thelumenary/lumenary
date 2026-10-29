/-
The Lumenary — formal mathematics
Functors: functors preserve isomorphisms; the power-set functors (covariant and contravariant),
the list (free monoid) functor and hom functors; functoriality as a tool for impossibility
proofs; and a functor that does not reflect isomorphisms.

We use Mathlib's `CategoryTheory.Functor` (`C ⥤ D`), whose fields are `obj`, `map`, `map_id`
and `map_comp`. Mathlib composes in diagrammatic order (`f ≫ g` is "first `f`, then `g`"), so
the functor law `F(g ∘ f) = F(g) ∘ F(f)` reads `F.map (f ≫ g) = F.map f ≫ F.map g`. In this
version of Mathlib a morphism `X ⟶ Y` in the category `Type u` wraps a function; `↾f` turns a
function `f` into such a morphism.

Proved here (`independent`): functors carry inverse pairs to inverse pairs, hence isomorphic
objects to isomorphic objects; `ZMod 4` and `ZMod 2 × ZMod 2` are not isomorphic groups (the
functorial argument unwound to elements); a functor to sets turns a retraction into an injective
map, so no retraction `D → S` exists when `F(D)` has one element and `F(S)` has two — the shape
of the "no retraction of the disc onto its boundary circle" proof; and a functor whose image of a
non-invertible morphism is invertible. Defined here (`definition`, with the functor laws proved):
the covariant and contravariant power-set functors, the list functor and the hom functors.
Mathlib provides (`library`): `Functor.map_isIso`, `Functor.assoc`, and the free-monoid functor
`MonCat.free`. The fundamental group functor and `π₁(S¹) ≅ ℤ` are in Mathlib too
(`FundamentalGroup`, `AddCircle.windingNumberIso`); they are used in the Lumenary lesson on the
fundamental group, not here.
-/
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Algebra.Category.MonCat.Adjunctions
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Prod

namespace Lumenary.Functors

open CategoryTheory

universe u v w u₂ v₂

/-! ### Functors preserve isomorphisms -/

-- @region functors.map_inverse
-- @provenance independent
/-- **Functors carry inverse pairs to inverse pairs.** If `g` is a two-sided inverse of `f`,
then `F(g)` is a two-sided inverse of `F(f)`:
`F(g) ∘ F(f) = F(g ∘ f) = F(id) = id`, and the same the other way round. Only the two functor
laws are used. -/
theorem map_inverse {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} (h₁ : f ≫ g = 𝟙 X) (h₂ : g ≫ f = 𝟙 Y) :
    F.map f ≫ F.map g = 𝟙 (F.obj X) ∧ F.map g ≫ F.map f = 𝟙 (F.obj Y) := by
  constructor
  · rw [← F.map_comp, h₁, F.map_id]
  · rw [← F.map_comp, h₂, F.map_id]
-- @endregion

-- @region functors.iso_of_iso
-- @provenance independent
/-- **Functors preserve isomorphic objects.** An isomorphism `e : X ≅ Y` in `C` gives an
isomorphism `F(X) ≅ F(Y)` in `D`, built from `map_inverse`. Read backwards this is the
impossibility tool of the lesson: if `F(X)` and `F(Y)` are *not* isomorphic, neither are `X`
and `Y`. (Mathlib's name for this construction is `Functor.mapIso`.) -/
theorem iso_of_iso {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) : Nonempty (F.obj X ≅ F.obj Y) :=
  ⟨⟨F.map e.hom, F.map e.inv, (map_inverse F e.hom_inv_id e.inv_hom_id).1,
    (map_inverse F e.hom_inv_id e.inv_hom_id).2⟩⟩
-- @endregion

-- @region functors.map_is_iso_library
-- @provenance library
/-- Mathlib's version: if `f` is an isomorphism then so is `F.map f`. This applies the instance
`CategoryTheory.Functor.map_isIso`. -/
theorem map_isIso_library {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  Functor.map_isIso F f
-- @endregion

-- @region functors.zmod4_not_iso_klein
-- @provenance independent
/-- **`ℤ/4` and `ℤ/2 × ℤ/2` are not isomorphic groups.** The lesson's argument applies the
functor `G ↦ 2G = {x + x}` (or, dually, `Hom(ℤ/2, −)`): it sends `ℤ/4` to a group with two
elements and `ℤ/2 × ℤ/2` to the trivial group. Unwound to elements: in `ℤ/2 × ℤ/2` every
`y` has `y + y = 0`, so an additive isomorphism `e` would give `e(2) = e(1) + e(1) = 0 = e(0)`,
and injectivity would force `2 = 0` in `ℤ/4`, which is false. -/
theorem zmod4_not_iso_klein : IsEmpty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  constructor
  intro e
  have hdouble : ∀ y : ZMod 2 × ZMod 2, y + y = 0 := by decide
  have h2 : e 2 = e 0 := by
    calc e 2 = e (1 + 1) := rfl
      _ = e 1 + e 1 := map_add e 1 1
      _ = 0 := hdouble (e 1)
      _ = e 0 := (map_zero e).symm
  have : (2 : ZMod 4) = 0 := e.injective h2
  exact absurd this (by decide)
-- @endregion

/-! ### Examples of functors -/

-- @region functors.powerset
-- @provenance definition
/-- **The covariant power-set functor** `P : Set → Set`. It sends a set `X` to the set of its
subsets, and a function `f : X → Y` to the direct-image map `S ↦ f(S)`.
The functor laws are `id(S) = S` (`Set.image_id`) and `(g ∘ f)(S) = g(f(S))` (`Set.image_comp`). -/
def powerset : Type u ⥤ Type u where
  obj X := Set X
  map f := ↾(fun S => (fun x => f x) '' S)
  map_id X := by
    ext S
    simp
  map_comp f g := by
    ext S
    simp [Set.image_image]
-- @endregion

-- @region functors.powerset_contra
-- @provenance definition
/-- **The contravariant power-set functor** `P* : Setᵒᵖ → Set`. It sends a function
`f : X → Y` to the preimage map `T ↦ f⁻¹(T)`, which goes the *other way*, from subsets of `Y`
to subsets of `X`. So it is a functor out of the opposite category: the laws are
`id⁻¹(T) = T` and `(g ∘ f)⁻¹(T) = f⁻¹(g⁻¹(T))` — note the reversed order. -/
def powersetContra : (Type u)ᵒᵖ ⥤ Type u where
  obj X := Set X.unop
  map f := ↾(fun T => (fun x => f.unop x) ⁻¹' T)
  map_id X := by
    ext T
    simp
  map_comp f g := by
    ext T
    simp [Set.preimage_preimage]
-- @endregion

-- @region functors.list_functor
-- @provenance definition
/-- **The list functor.** It sends a set `X` to the set `List X` of finite words in `X`, and a
function `f` to "apply `f` letter by letter" (`List.map f`). The laws are `List.map_id` and
`List.map_map`. `List X` with concatenation is the free monoid on `X` (see `list_map_append`
and the lesson on universal properties). -/
def listFunctor : Type u ⥤ Type u where
  obj X := List X
  map f := ↾(List.map (fun x => f x))
  map_id X := by
    ext l
    simp
  map_comp f g := by
    ext l
    simp [List.map_map, Function.comp_def]
-- @endregion

-- @region functors.list_map_append
-- @provenance library
/-- `List.map f` is a **monoid homomorphism** for concatenation: it preserves the empty word
and `map f (l ++ m) = map f l ++ map f m`. So the list functor really lands in monoids. This
applies `List.map_nil` and `List.map_append`. -/
theorem list_map_append {X Y : Type u} (f : X → Y) (l m : List X) :
    List.map f [] = [] ∧ List.map f (l ++ m) = List.map f l ++ List.map f m :=
  ⟨List.map_nil, List.map_append⟩
-- @endregion

-- @region functors.free_monoid_library
-- @provenance library
/-- Mathlib's **free monoid functor** `MonCat.free : Type u ⥤ MonCat` sends a set `X` to the free
monoid `FreeMonoid X` (lists with concatenation) and a function to the homomorphism that renames
letters: a one-letter word `[a]` goes to `[f a]`. This applies `MonCat.free` and
`FreeMonoid.map_of`. -/
theorem free_monoid_library {X Y : Type u} (f : X ⟶ Y) (a : X) :
    (MonCat.free.map f).hom (FreeMonoid.of a) = FreeMonoid.of (f a) :=
  FreeMonoid.map_of _ a
-- @endregion

-- @region functors.hom_functor
-- @provenance definition
/-- **The hom functor** `Hom(A, −) : C → Set`. It sends an object `B` to the set of morphisms
`A ⟶ B`, and a morphism `f : B ⟶ B'` to "compose with `f`": `g ↦ f ∘ g` (`g ≫ f` in Mathlib).
The functor laws are exactly the axioms of a category: `id ∘ g = g` (`Category.comp_id`) and
`(f' ∘ f) ∘ g = f' ∘ (f ∘ g)` (`Category.assoc`). Mathlib calls it `coyoneda.obj (op A)`. -/
def homFunctor {C : Type u} [Category.{v} C] (A : C) : C ⥤ Type v where
  obj B := A ⟶ B
  map f := ↾(fun g => g ≫ f)
  map_id B := by
    ext g
    simp
  map_comp f f' := by
    ext g
    simp
-- @endregion

-- @region functors.hom_functor_contra
-- @provenance definition
/-- **The contravariant hom functor** `Hom(−, A) : Cᵒᵖ → Set`, sending `f : B' ⟶ B` to
"precompose with `f`": `g ↦ g ∘ f`. Precomposition reverses the direction of arrows, so this is
a functor out of `Cᵒᵖ`. Mathlib calls it `yoneda.obj A`. -/
def homFunctorContra {C : Type u} [Category.{v} C] (A : C) : Cᵒᵖ ⥤ Type v where
  obj B := B.unop ⟶ A
  map f := ↾(fun g => f.unop ≫ g)
  map_id B := by
    ext g
    simp
  map_comp f f' := by
    ext g
    simp
-- @endregion

-- @region functors.comp_assoc_library
-- @provenance library
/-- **Functors compose, associatively.** `F ⋙ G` is "first `F`, then `G`", and composition of
functors is associative (on the nose). Together with identity functors this makes small
categories and functors into a category, Mathlib's `Cat`. This applies `Functor.assoc`. -/
theorem comp_assoc_library {A : Type u} [Category.{v} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type w} [Category.{w} C] {D : Type u} [Category.{v} D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) :=
  Functor.assoc F G H
-- @endregion

/-! ### Functoriality proves impossibility -/

-- @region functors.map_injective_of_retraction
-- @provenance independent
/-- **Functors preserve retractions.** If `r ∘ i = id_S` (here `i ≫ r = 𝟙 S`), then
`F(r) ∘ F(i) = id_{F(S)}` for every functor `F`; for a functor to sets this makes `F(i)`
injective, since `F(i)(a) = F(i)(b)` gives `a = F(r)(F(i)(a)) = F(r)(F(i)(b)) = b`. -/
theorem map_injective_of_retraction {C : Type u} [Category.{v} C] (F : C ⥤ Type w) {S D : C}
    (i : S ⟶ D) (r : D ⟶ S) (h : i ≫ r = 𝟙 S) : Function.Injective (F.map i) := by
  have hFr : F.map i ≫ F.map r = 𝟙 (F.obj S) := by
    rw [← F.map_comp, h, F.map_id]
  intro a b hab
  calc a = (F.map i ≫ F.map r) a := by rw [hFr]; rfl
    _ = F.map r (F.map i a) := rfl
    _ = F.map r (F.map i b) := by rw [hab]
    _ = (F.map i ≫ F.map r) b := rfl
    _ = b := by rw [hFr]; rfl
-- @endregion

-- @region functors.no_retraction
-- @provenance independent
/-- **The shape of the no-retraction theorem.** Suppose a functor `F` to sets sends `D` to a set
with at most one element and `S` to a set with two different elements. Then there is **no**
retraction `r : D → S` of any `i : S → D` (no `r` with `r ∘ i = id_S`): `F(i)` would be an
injective map from a set with two elements into a set with one.
For the circle `S¹` inside the disc `D²` and `F = π₁` (fundamental group, a functor from pointed
spaces to groups, then to sets): `π₁(D²)` is trivial and `π₁(S¹) ≅ ℤ` is not, so the disc does not
retract onto its boundary circle. -/
theorem no_retraction {C : Type u} [Category.{v} C] (F : C ⥤ Type w) {S D : C} (i : S ⟶ D)
    [Subsingleton (F.obj D)] {a b : F.obj S} (hab : a ≠ b) : ¬ ∃ r : D ⟶ S, i ≫ r = 𝟙 S := by
  rintro ⟨r, h⟩
  exact hab (map_injective_of_retraction F i r h (Subsingleton.elim _ _))
-- @endregion

/-! ### Functors need not reflect isomorphisms -/

-- @region functors.not_reflects_iso
-- @provenance independent
/-- **A functor can send a non-isomorphism to an isomorphism.** In the poset `0 < 1` (Lean's
`Fin 2`) regarded as a category, the morphism `0 ⟶ 1` is not an isomorphism (an inverse would be
a morphism `1 ⟶ 0`, that is `1 ≤ 0`). But the constant functor to a one-element set sends it to
the identity map, which is an isomorphism. So `F(f)` invertible does not force `f` invertible. -/
theorem not_reflects_iso :
    ∃ (F : Fin 2 ⥤ Type) (f : (0 : Fin 2) ⟶ 1), IsIso (F.map f) ∧ ¬ IsIso f := by
  have h01 : (0 : Fin 2) ≤ 1 := by decide
  refine ⟨(Functor.const (Fin 2)).obj PUnit, homOfLE h01, ?_, ?_⟩
  · -- the constant functor sends every morphism to an identity
    show IsIso (𝟙 PUnit)
    infer_instance
  · intro hf
    have h10 : (1 : Fin 2) ≤ 0 := leOfHom (inv (homOfLE h01))
    exact absurd h10 (by decide)
-- @endregion

end Lumenary.Functors
