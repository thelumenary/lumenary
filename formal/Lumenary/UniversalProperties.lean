/-
The Lumenary — formal mathematics
Universal properties: universal arrows and their uniqueness up to unique isomorphism; products
of sets, groups and spaces; quotient sets and quotient groups; the free monoid as finite words;
the field of fractions `ℚ` of `ℤ`; and the non-existence of a product of `𝔽₂` and `𝔽₃` among
fields.

We use Mathlib's categories and functors (`C ⥤ D`; `f ≫ g` is "first `f`, then `g`").

Proved here (`independent`): the general theorem that two universal arrows are related by a
unique compatible isomorphism (for our own structure `UniversalArrow`, which packages the
definition of the lesson); the universal properties of the product of sets, of the product of
groups, of the quotient of a set by an equivalence relation, and of lists as the free monoid;
and that no field has ring homomorphisms to both `ZMod 2` and `ZMod 3` (so these two fields have
no product in the category of fields). Mathlib provides (`library`): uniqueness of initial
objects (`IsInitial.uniqueUpToIso`, `IsInitial.hom_ext`) — a universal arrow is an initial
object of a comma category, Mathlib's `StructuredArrow` —; continuity into a product
(`continuous_prodMk`); quotient groups (`QuotientGroup.lift`); free monoids (`FreeMonoid.lift`);
and the universal property of `ℚ` (`Rat.castHom`, `RingHom.ext_rat`).
-/
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.NormNum.Basic

namespace Lumenary.UniversalProperties

open CategoryTheory

universe u v u₂ v₂

/-! ### Universal arrows and their uniqueness -/

-- @region universal_properties.universal_arrow
-- @provenance definition
/-- A **universal arrow** from an object `X` of `C` to a functor `U : D ⥤ C`: an object `obj`
of `D` with a morphism `unit : X ⟶ U(obj)` such that every morphism `f : X ⟶ U(E)` factors as
`U(g) ∘ unit` for exactly one `g : obj ⟶ E`. Here `lift f` is that `g`, `fac` says it works and
`uniq` says it is the only one. (Free monoids: `X` a set, `U` the forgetful functor from monoids
to sets, `obj` the free monoid, `unit` the inclusion of one-letter words.) -/
structure UniversalArrow {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    (X : C) (U : D ⥤ C) where
  /-- The universal object. -/
  obj : D
  /-- The universal morphism `X ⟶ U(obj)`. -/
  unit : X ⟶ U.obj obj
  /-- The factorisation of a morphism `X ⟶ U(E)` through `unit`. -/
  lift : {E : D} → (X ⟶ U.obj E) → (obj ⟶ E)
  /-- Existence: `U(lift f) ∘ unit = f`. -/
  fac : ∀ {E : D} (f : X ⟶ U.obj E), unit ≫ U.map (lift f) = f
  /-- Uniqueness: any `g` with `U(g) ∘ unit = f` is `lift f`. -/
  uniq : ∀ {E : D} (f : X ⟶ U.obj E) (g : obj ⟶ E), unit ≫ U.map g = f → g = lift f
-- @endregion

namespace UniversalArrow

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] {X : C} {U : D ⥤ C}

-- @region universal_properties.hom_ext
-- @provenance independent
/-- **Maps out of a universal object are determined by what they do to the unit.** If
`U(g) ∘ unit = U(g') ∘ unit` then `g = g'`: both are the unique factorisation of the same
morphism. This is the "uniqueness clause" doing its work. -/
theorem hom_ext (A : UniversalArrow X U) {E : D} {g g' : A.obj ⟶ E}
    (h : A.unit ≫ U.map g = A.unit ≫ U.map g') : g = g' :=
  (A.uniq _ g h).trans (A.uniq _ g' rfl).symm
-- @endregion

-- @region universal_properties.lift_unit
-- @provenance independent
/-- The factorisation of `unit` itself is the identity: `lift unit = id`, because `id` also
factors `unit` (`U(id) ∘ unit = unit`) and factorisations are unique. -/
theorem lift_unit (A : UniversalArrow X U) : A.lift A.unit = 𝟙 A.obj :=
  (A.uniq A.unit (𝟙 A.obj) (by rw [U.map_id, Category.comp_id])).symm
-- @endregion

-- @region universal_properties.iso
-- @provenance definition
/-- **Two universal arrows have isomorphic objects.** The comparison maps are `A.lift B.unit`
and `B.lift A.unit`; each composite factors the unit through itself, so by `hom_ext` (the
uniqueness clause) it is the identity. This is the proof of the lesson, verbatim. -/
def iso (A B : UniversalArrow X U) : A.obj ≅ B.obj where
  hom := A.lift B.unit
  inv := B.lift A.unit
  hom_inv_id := by
    apply A.hom_ext
    rw [U.map_comp, ← Category.assoc, A.fac, B.fac, U.map_id, Category.comp_id]
  inv_hom_id := by
    apply B.hom_ext
    rw [U.map_comp, ← Category.assoc, B.fac, A.fac, U.map_id, Category.comp_id]
-- @endregion

-- @region universal_properties.iso_compatible
-- @provenance independent
/-- The isomorphism `iso A B` is **compatible with the structure maps**: it carries `A.unit` to
`B.unit`, i.e. `U(φ) ∘ A.unit = B.unit`. -/
theorem iso_compatible (A B : UniversalArrow X U) : A.unit ≫ U.map (A.iso B).hom = B.unit :=
  A.fac B.unit
-- @endregion

-- @region universal_properties.iso_unique
-- @provenance independent
/-- **…and it is the only compatible isomorphism** (indeed the only compatible morphism): any
`φ : A.obj ⟶ B.obj` with `U(φ) ∘ A.unit = B.unit` equals `(iso A B).hom`. So an object with a
universal property is unique *up to a unique isomorphism compatible with the structure maps*. -/
theorem iso_unique (A B : UniversalArrow X U) (φ : A.obj ⟶ B.obj)
    (hφ : A.unit ≫ U.map φ = B.unit) : φ = (A.iso B).hom :=
  A.uniq B.unit φ hφ
-- @endregion

-- @region universal_properties.is_initial
-- @provenance definition
/-- **A universal arrow is an initial object.** Objects of Mathlib's comma category
`StructuredArrow X U` are pairs `(E, f : X ⟶ U(E))`, and morphisms `(E, f) ⟶ (E', f')` are maps
`g : E ⟶ E'` with `U(g) ∘ f = f'`. The universal arrow `(obj, unit)` has exactly one morphism to
every other object — `lift` gives one (`fac`), and `uniq` says there are no others — so it is
initial. This connects our structure to Mathlib's library of initial objects and limits. -/
def isInitial (A : UniversalArrow X U) : Limits.IsInitial (StructuredArrow.mk A.unit) :=
  Limits.IsInitial.ofUniqueHom
    (fun E => StructuredArrow.homMk (A.lift E.hom) (A.fac E.hom))
    (fun E m => by
      ext
      exact A.uniq E.hom m.right (StructuredArrow.w m))
-- @endregion

end UniversalArrow

-- @region universal_properties.initial_unique_library
-- @provenance library
/-- Mathlib's form of the same principle: **initial objects are unique up to unique
isomorphism.** A universal arrow from `X` to `U` is exactly an initial object of the comma
category `StructuredArrow X U`, so this covers every universal property of the lesson. This
applies `IsInitial.uniqueUpToIso` and `IsInitial.hom_ext`. -/
theorem initial_unique_library {C : Type u} [Category.{v} C] {I J : C}
    (hI : Limits.IsInitial I) (hJ : Limits.IsInitial J) :
    Nonempty (I ≅ J) ∧ ∀ φ ψ : I ⟶ J, φ = ψ :=
  ⟨⟨hI.uniqueUpToIso hJ⟩, fun φ ψ => hI.hom_ext φ ψ⟩
-- @endregion

/-! ### Products -/

-- @region universal_properties.prod_universal
-- @provenance independent
/-- **The product of sets.** For maps `f : X → A` and `g : X → B` there is exactly one
`h : X → A × B` with `π₁ ∘ h = f` and `π₂ ∘ h = g`, namely `h(x) = (f(x), g(x))`. Uniqueness: a
point of `A × B` is determined by its two coordinates. -/
theorem prod_universal {X A B : Type u} (f : X → A) (g : X → B) :
    ∃! h : X → A × B, Prod.fst ∘ h = f ∧ Prod.snd ∘ h = g := by
  refine ⟨fun x => (f x, g x), ⟨rfl, rfl⟩, ?_⟩
  rintro h ⟨h₁, h₂⟩
  funext x
  exact Prod.ext (congrFun h₁ x) (congrFun h₂ x)
-- @endregion

-- @region universal_properties.group_prod_universal
-- @provenance independent
/-- **The product of groups.** For homomorphisms `f : G → H` and `g : G → K` there is exactly
one homomorphism `h : G → H × K` with `π₁ ∘ h = f` and `π₂ ∘ h = g`. The map is the same as for
sets (`x ↦ (f x, g x)`, Mathlib's `MonoidHom.prod`); the new point is that it is a homomorphism
because the operation on `H × K` is defined coordinatewise. -/
theorem group_prod_universal {G H K : Type u} [Group G] [Group H] [Group K] (f : G →* H)
    (g : G →* K) :
    ∃! h : G →* H × K, (MonoidHom.fst H K).comp h = f ∧ (MonoidHom.snd H K).comp h = g := by
  refine ⟨f.prod g, ⟨MonoidHom.fst_comp_prod f g, MonoidHom.snd_comp_prod f g⟩, ?_⟩
  rintro h ⟨h₁, h₂⟩
  ext x
  · exact DFunLike.congr_fun h₁ x
  · exact DFunLike.congr_fun h₂ x
-- @endregion

-- @region universal_properties.continuous_prod_library
-- @provenance library
/-- **The product of spaces.** With the product topology, a map into `Y × Z` is continuous
exactly when both coordinates are: the product topology is the coarsest topology making the
projections continuous, which is precisely what makes `X × Y` the product in **Top**. This
applies `continuous_prodMk`. -/
theorem continuous_prod_library {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : X → Z) :
    Continuous (fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  continuous_prodMk
-- @endregion

/-! ### Quotients -/

-- @region universal_properties.quotient_universal
-- @provenance independent
/-- **The quotient set.** If `f : X → Y` is constant on equivalence classes (`a ~ b` implies
`f a = f b`), there is exactly one `g : X/~ → Y` with `g ∘ q = f`, where `q : X → X/~` sends an
element to its class. Existence is `Quotient.lift`: define `g [a] = f a`, well defined by the
hypothesis. Uniqueness: every class is `[a]` for some `a` (`Quotient.ind`). -/
theorem quotient_universal {X Y : Type u} (s : Setoid X) (f : X → Y)
    (hf : ∀ a b, s a b → f a = f b) :
    ∃! g : Quotient s → Y, g ∘ Quotient.mk s = f := by
  refine ⟨Quotient.lift f hf, rfl, ?_⟩
  intro g hg
  funext c
  induction c using Quotient.ind with
  | _ a => exact congrFun hg a
-- @endregion

-- @region universal_properties.quotient_group_library
-- @provenance library
/-- **The quotient group.** If `N` is a normal subgroup of `G` and `f : G → H` is a homomorphism
killing `N` (`N ⊆ ker f`), there is exactly one homomorphism `g : G/N → H` with `g ∘ q = f`.
This applies `QuotientGroup.lift`, `QuotientGroup.lift_mk` and `QuotientGroup.monoidHom_ext`. -/
theorem quotient_group_library {G H : Type u} [Group G] [Group H] (N : Subgroup G) [N.Normal]
    (f : G →* H) (hN : N ≤ f.ker) :
    ∃! g : G ⧸ N →* H, g.comp (QuotientGroup.mk' N) = f :=
  ⟨QuotientGroup.lift N f hN, MonoidHom.ext fun x => QuotientGroup.lift_mk N hN x,
    fun _ hg => QuotientGroup.monoidHom_ext N (hg.trans
      (MonoidHom.ext fun x => (QuotientGroup.lift_mk N hN x).symm))⟩
-- @endregion

/-! ### The free monoid is the monoid of words -/

-- @region universal_properties.eval_word
-- @provenance definition
/-- Evaluate a word `[s₁, s₂, …, sₖ]` in a monoid `M`, given a value `f(s)` for each letter:
the product `f(s₁) · f(s₂) ⋯ f(sₖ)` (the empty word gives `1`). -/
def evalWord {S M : Type u} [Monoid M] (f : S → M) (w : List S) : M :=
  (w.map f).prod
-- @endregion

-- @region universal_properties.eval_word_append
-- @provenance independent
/-- `evalWord f` is a **monoid homomorphism** from words under concatenation: it sends the empty
word to `1` and `v ++ w` to the product of the values. -/
theorem evalWord_append {S M : Type u} [Monoid M] (f : S → M) (v w : List S) :
    evalWord f [] = 1 ∧ evalWord f (v ++ w) = evalWord f v * evalWord f w := by
  constructor
  · rfl
  · simp [evalWord, List.map_append, List.prod_append]
-- @endregion

-- @region universal_properties.free_monoid_unique
-- @provenance independent
/-- **Uniqueness in the universal property of the free monoid.** Any map `h` from words to a
monoid that preserves `1` and concatenation and agrees with `f` on one-letter words is
`evalWord f`. Proof by induction on the word: `s :: w` is the concatenation `[s] ++ w`, so
`h(s :: w) = h[s] · h(w) = f(s) · evalWord f w = evalWord f (s :: w)`. -/
theorem free_monoid_unique {S M : Type u} [Monoid M] (f : S → M) (h : List S → M)
    (h_nil : h [] = 1) (h_append : ∀ v w, h (v ++ w) = h v * h w) (h_single : ∀ s, h [s] = f s) :
    h = evalWord f := by
  funext w
  induction w with
  | nil => exact h_nil
  | cons s w ih =>
    calc h (s :: w) = h ([s] ++ w) := rfl
      _ = h [s] * h w := h_append [s] w
      _ = f s * evalWord f w := by rw [h_single, ih]
      _ = evalWord f (s :: w) := by simp [evalWord]
-- @endregion

-- @region universal_properties.free_monoid_library
-- @provenance library
/-- Mathlib's `FreeMonoid S` (words in `S`, with concatenation) and its universal property:
for every map `f : S → M` into a monoid there is exactly one monoid homomorphism
`FreeMonoid S → M` sending each letter `of s` to `f s`. This applies `FreeMonoid.lift`,
`FreeMonoid.lift_eval_of` and `FreeMonoid.hom_eq`. -/
theorem free_monoid_library {S M : Type u} [Monoid M] (f : S → M) :
    ∃! g : FreeMonoid S →* M, ∀ s, g (FreeMonoid.of s) = f s :=
  ⟨FreeMonoid.lift f, FreeMonoid.lift_eval_of f, fun _ hg =>
    FreeMonoid.hom_eq fun s => (hg s).trans (FreeMonoid.lift_eval_of f s).symm⟩
-- @endregion

/-! ### Fields of fractions, and a product that does not exist -/

-- @region universal_properties.rat_universal_library
-- @provenance library
/-- **`ℚ` is the field of fractions of `ℤ`.** For every field `K` of characteristic zero (so that
`ℤ → K` is injective) there is exactly one ring homomorphism `ℚ → K` extending `ℤ → K`. This
applies `Rat.castHom` (existence) and `RingHom.ext_rat` (uniqueness); the general construction
for any integral domain is Mathlib's `IsFractionRing.lift`. -/
theorem rat_universal_library (K : Type u) [Field K] [CharZero K] :
    ∃! φ : ℚ →+* K, φ.comp (Int.castRingHom ℚ) = Int.castRingHom K :=
  ⟨Rat.castHom K, RingHom.ext_int _ _, fun φ _ => RingHom.ext_rat φ (Rat.castHom K)⟩
-- @endregion

-- @region universal_properties.no_field_maps_to_f2_f3
-- @provenance independent
/-- **`𝔽₂` and `𝔽₃` have no product in the category of fields.** A product would be a field `K`
with homomorphisms `K → 𝔽₂` and `K → 𝔽₃`. But a ring homomorphism out of a field is injective;
`2 ↦ 0` in `𝔽₂` forces `2 = 0` in `K`, and `3 ↦ 0` in `𝔽₃` forces `3 = 0` in `K`; then
`1 = 3 - 2 = 0` in `K`, which no field allows. So no such `K` exists at all — the universal
property *characterises* products but does not *construct* them. -/
theorem no_field_maps_to_f2_f3 (K : Type u) [Field K] (f : K →+* ZMod 2) (g : K →+* ZMod 3) :
    False := by
  have h2 : (2 : K) = 0 := by
    apply f.injective
    rw [map_ofNat, map_zero]
    decide
  have h3 : (3 : K) = 0 := by
    apply g.injective
    rw [map_ofNat, map_zero]
    decide
  have h1 : (1 : K) = 0 := by
    calc (1 : K) = 3 - 2 := by norm_num
      _ = 0 := by rw [h2, h3, sub_zero]
  exact one_ne_zero h1
-- @endregion

end Lumenary.UniversalProperties
