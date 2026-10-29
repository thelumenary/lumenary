/-
The Lumenary — formal mathematics
Representable functors: the power-set functor is represented by a two-element set, the
forgetful functor on groups by ℤ, products and quotients by their universal properties, and
representations correspond exactly to universal elements, which are unique up to unique
isomorphism.

What is proved here. Independently: the contravariant power-set functor is represented by
`Bool` (characteristic functions); a homomorphism out of ℤ is determined by the image of `1`,
giving a natural bijection `Hom(ℤ, G) ≃ G`; the product `A × B` represents "pairs of maps"
and the quotient `X ⧸ ~` corepresents "maps that respect `~`"; representations of a functor
`F : C ⥤ Type` correspond to universal elements of `F`, and a universal element is unique up
to a unique isomorphism; a functor whose value at the one-point type has two distinct
elements is not corepresentable, so the *covariant* power-set functor is not.
From Mathlib: the forgetful functor `GrpCat ⥤ Type` is corepresentable (Joël Riou's
`GrpCat.coyonedaObjIsoForget`), free monoids (`FreeMonoid.lift`), and limits as
representing objects of the cone functor (`IsLimit.ofRepresentableBy`).

Mathlib's conventions: `F.RepresentableBy Y` (for `F : Cᵒᵖ ⥤ Type`) is a natural bijection
`(X ⟶ Y) ≃ F(X)`, and `F.CorepresentableBy X` (for `F : C ⥤ Type`) is a natural bijection
`(X ⟶ Y) ≃ F(Y)`. Morphisms in the category `Type` are functions wrapped as `↾f`.
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.FreeMonoid.Basic

namespace Lumenary.RepresentableFunctors

open CategoryTheory Opposite

universe u v

/-! ### The power-set functor and characteristic functions -/

-- @region representable_functors.powerset
-- @provenance definition
/-- The **contravariant power-set functor** `𝒫 : Setᵒᵖ ⥤ Set`. It sends a set `X` to the set
of its subsets, and a function `f : Y → X` to the preimage map `S ↦ f⁻¹(S)`, which goes from
subsets of `X` to subsets of `Y` — backwards, hence `Typeᵒᵖ`. -/
def powerset : Typeᵒᵖ ⥤ Type where
  obj X := Set X.unop
  map f := ↾fun S => (f.unop : _ → _) ⁻¹' S
-- @endregion

-- @region representable_functors.powerset_representable
-- @provenance independent
/-- **The power-set functor is represented by the two-element set `Bool`.** Subsets `S ⊆ X`
correspond to characteristic functions `χ : X → Bool` (`S = {x | χ x = true}`), and the
correspondence is natural: the characteristic function of `f⁻¹(S)` is `χ_S ∘ f`.
Building `χ_S` from `S` needs to decide `x ∈ S`, which uses classical logic. -/
theorem powerset_representable : Nonempty (powerset.RepresentableBy Bool) :=
  ⟨{ homEquiv := fun {X} =>
    { toFun := fun χ => {x | χ x = true}
      invFun := fun (S : Set X) => ↾fun x => @decide (x ∈ S) (Classical.propDecidable _)
      left_inv := fun χ => by
        ext x
        simp
      right_inv := fun (S : Set X) => by
        apply Set.ext
        intro x
        simp }
     homEquiv_comp := fun _ _ => rfl }⟩
-- @endregion

/-! ### Groups: the forgetful functor is represented by ℤ -/

section Groups

variable {G H : Type u} [Group G] [Group H]

-- @region representable_functors.int_hom_eq_zpow
-- @provenance independent
/-- A group homomorphism `φ : ℤ → G` is determined by `g = φ(1)`: it must send `n` to `gⁿ`.
(In Mathlib the integers *as a multiplicative group* are `Multiplicative ℤ`, and `ofAdd n` is
`n` seen there.) Proof by induction over the integers: `φ(n + 1) = φ(n) φ(1)` and
`φ(n − 1) = φ(n) φ(1)⁻¹`. -/
theorem int_hom_eq_zpow (φ : Multiplicative ℤ →* G) (n : ℤ) :
    φ (Multiplicative.ofAdd n) = φ (Multiplicative.ofAdd 1) ^ n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    calc φ (Multiplicative.ofAdd ((k : ℤ) + 1))
        = φ (Multiplicative.ofAdd (k : ℤ) * Multiplicative.ofAdd 1) := rfl
      _ = φ (Multiplicative.ofAdd (k : ℤ)) * φ (Multiplicative.ofAdd 1) := φ.map_mul _ _
      _ = φ (Multiplicative.ofAdd 1) ^ (k : ℤ) * φ (Multiplicative.ofAdd 1) := by rw [ih]
      _ = φ (Multiplicative.ofAdd 1) ^ ((k : ℤ) + 1) := (zpow_add_one _ _).symm
  | pred k ih =>
    calc φ (Multiplicative.ofAdd (-(k : ℤ) - 1))
        = φ (Multiplicative.ofAdd (-(k : ℤ)) * (Multiplicative.ofAdd 1)⁻¹) := rfl
      _ = φ (Multiplicative.ofAdd (-(k : ℤ))) * (φ (Multiplicative.ofAdd 1))⁻¹ := by
          rw [φ.map_mul, φ.map_inv]
      _ = φ (Multiplicative.ofAdd 1) ^ (-(k : ℤ)) * (φ (Multiplicative.ofAdd 1))⁻¹ := by rw [ih]
      _ = φ (Multiplicative.ofAdd 1) ^ (-(k : ℤ) - 1) := (zpow_sub_one _ _).symm
-- @endregion

-- @region representable_functors.int_hom_equiv
-- @provenance definition
/-- **`Hom(ℤ, G) ≃ G`**: evaluating at `1` is a bijection from group homomorphisms `ℤ → G` to
elements of `G`; the inverse sends `g` to `n ↦ gⁿ` (Mathlib's `zpowersHom`). Injectivity is
`int_hom_eq_zpow`. The pair `(ℤ, 1)` is a universal element of the forgetful functor. -/
def intHomEquiv : (Multiplicative ℤ →* G) ≃ G where
  toFun φ := φ (Multiplicative.ofAdd 1)
  invFun g := zpowersHom G g
  left_inv φ := by
    refine MonoidHom.ext fun n => ?_
    have h := int_hom_eq_zpow φ (Multiplicative.toAdd n)
    rw [ofAdd_toAdd] at h
    simp [h]
  right_inv g := by simp
-- @endregion

-- @region representable_functors.int_hom_equiv_natural
-- @provenance independent
/-- The bijection `Hom(ℤ, G) ≃ G` is **natural in `G`**: composing with a homomorphism
`f : G → H` on the left corresponds to applying `f` to the element. This is what makes it a
natural isomorphism `Hom(ℤ, −) ≅ U` with the forgetful functor `U`, not just a family of
bijections. -/
theorem int_hom_equiv_natural (f : G →* H) (φ : Multiplicative ℤ →* G) :
    intHomEquiv (f.comp φ) = f (intHomEquiv φ) :=
  rfl
-- @endregion

end Groups

-- @region representable_functors.forget_grp_corepresentable
-- @provenance library
/-- **The forgetful functor `Grp ⥤ Set` is corepresentable**, in Mathlib's category `GrpCat`
of groups. This applies Mathlib's instance `GrpCat.forget_isCorepresentable`, built from the
natural isomorphism `GrpCat.coyonedaObjIsoForget : Hom(ℤ, −) ≅ forget` (with `ℤ` lifted to
the right universe). -/
theorem forget_grp_corepresentable : (forget GrpCat.{u}).IsCorepresentable :=
  inferInstance
-- @endregion

/-! ### Universal elements -/

section Universal

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type v)

-- @region representable_functors.is_universal
-- @provenance definition
/-- An element `x ∈ F(A)` of a functor `F : C ⥤ Set` is **universal** if every element of
every `F(B)` is obtained from `x` along exactly one arrow: for all `B` and `y ∈ F(B)` there is
a unique `f : A ⟶ B` with `F(f)(x) = y`. Example: `1 ∈ U(ℤ)` for the forgetful functor on
groups. -/
def IsUniversal {A : C} (x : F.obj A) : Prop :=
  ∀ (B : C) (y : F.obj B), ∃! f : A ⟶ B, F.map f x = y
-- @endregion

variable {F}

-- @region representable_functors.universal_of_corepresentable
-- @provenance independent
/-- **A representation gives a universal element**: if `e : Hom(A, −) ≅ F`, then
`x = e(id_A)` is universal. Given `y ∈ F(B)`, the arrow is `e⁻¹(y)`; it works because
`F(f)(e(id_A)) = e(id_A ≫ f) = e(f)` by naturality, and it is unique because `e` is
injective. -/
theorem universal_of_corepresentable {A : C} (e : F.CorepresentableBy A) :
    IsUniversal F (e.homEquiv (𝟙 A)) := by
  intro B y
  refine ⟨e.homEquiv.symm y, ?_, ?_⟩
  · show F.map (e.homEquiv.symm y) (e.homEquiv (𝟙 A)) = y
    rw [← e.homEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  · intro f hf
    rw [← hf, ← e.homEquiv_comp, Category.id_comp, Equiv.symm_apply_apply]
-- @endregion

-- @region representable_functors.corepresentable_of_universal
-- @provenance definition
/-- **A universal element gives a representation**: if `x ∈ F(A)` is universal, then
`f ↦ F(f)(x)` is a natural bijection `Hom(A, B) ≃ F(B)`. Bijectivity is exactly the
"exists unique" in the definition; naturality is functoriality of `F`. -/
noncomputable def corepresentableOfUniversal {A : C} {x : F.obj A} (h : IsUniversal F x) :
    F.CorepresentableBy A where
  homEquiv {B} := Equiv.ofBijective (fun f : A ⟶ B => F.map f x)
    ⟨fun _ g hfg => (h B (F.map g x)).unique hfg rfl,
     fun y => (h B y).exists⟩
  homEquiv_comp g f := Functor.map_comp_apply F f g x
-- @endregion

-- @region representable_functors.corepresentable_equiv_universal
-- @provenance independent
/-- **Representations of `F` by `A` correspond exactly to universal elements of `F(A)`.**
The two constructions above are mutually inverse: a representation is determined by where it
sends `id_A` (Mathlib's `CorepresentableBy.ext`), and `F(id_A)(x) = x`. -/
theorem corepresentable_equiv_universal {A : C} :
    Nonempty (F.CorepresentableBy A ≃ {x : F.obj A // IsUniversal F x}) :=
  ⟨{ toFun := fun e => ⟨e.homEquiv (𝟙 A), universal_of_corepresentable e⟩
     invFun := fun x => corepresentableOfUniversal x.2
     left_inv := fun e => by
       apply Functor.CorepresentableBy.ext
       exact Functor.map_id_apply F A _
     right_inv := fun x => by
       apply Subtype.ext
       exact Functor.map_id_apply F A _ }⟩
-- @endregion

-- @region representable_functors.universal_unique
-- @provenance independent
/-- **Universal elements are unique up to unique isomorphism.** If `(A, x)` and `(A', x')`
are both universal for `F`, there is an isomorphism `e : A ≅ A'` with `F(e)(x) = x'`, and it is
the *only* arrow `A ⟶ A'` sending `x` to `x'`.
Proof: universality gives `f : A ⟶ A'` with `F(f)(x) = x'` and `g : A' ⟶ A` with
`F(g)(x') = x`. Then `g ∘ f` and `id_A` both send `x` to `x`, so they are equal by the
uniqueness clause for `(A, x)`; likewise `f ∘ g = id_{A'}`. -/
theorem universal_unique {A A' : C} {x : F.obj A} {x' : F.obj A'}
    (h : IsUniversal F x) (h' : IsUniversal F x') :
    ∃ e : A ≅ A', F.map e.hom x = x' ∧ ∀ f : A ⟶ A', F.map f x = x' → f = e.hom := by
  obtain ⟨f, hf, hf_uniq⟩ := h A' x'
  obtain ⟨g, hg, -⟩ := h' A x
  have hgf : f ≫ g = 𝟙 A := by
    apply (h A x).unique
    · rw [Functor.map_comp_apply, hf, hg]
    · rw [Functor.map_id_apply]
  have hfg : g ≫ f = 𝟙 A' := by
    apply (h' A' x').unique
    · rw [Functor.map_comp_apply, hg, hf]
    · rw [Functor.map_id_apply]
  exact ⟨⟨f, g, hgf, hfg⟩, hf, fun f' hf' => hf_uniq f' hf'⟩
-- @endregion

-- @region representable_functors.subsingleton_of_corepresentable
-- @provenance independent
/-- **A necessary condition.** If a functor `F : Set ⥤ Set` is corepresentable, then `F` of a
one-point set has at most one element — because there is exactly one map from any set to a
point. So a functor whose value at the point has two distinct elements cannot be
corepresentable: not every functor to `Set` is representable. -/
theorem subsingleton_of_corepresentable {F : Type ⥤ Type} {A : Type}
    (e : F.CorepresentableBy A) : Subsingleton (F.obj PUnit) := by
  constructor
  intro y y'
  rw [← e.homEquiv.apply_symm_apply y, ← e.homEquiv.apply_symm_apply y']
  congr 1
  ext a
-- @endregion

end Universal

/-! ### Variance matters: the covariant power set is not corepresentable -/

-- @region representable_functors.image_powerset
-- @provenance definition
/-- The **covariant power-set functor**: a set goes to its set of subsets, and `f : X → Y` to
the direct-image map `S ↦ f(S)`. Same objects as `powerset`, arrows the other way. -/
def imagePowerset : Type ⥤ Type where
  obj X := Set X
  map f := ↾fun S => (f : _ → _) '' S
  map_id X := by
    ext S
    simp
  map_comp f g := by
    ext S
    simp [Set.image_image]
-- @endregion

-- @region representable_functors.image_powerset_not_corepresentable
-- @provenance independent
/-- **The covariant power-set functor is not corepresentable** (while the contravariant one is
represented by `Bool`). Its value at a point, `Set PUnit = {∅, {⋆}}`, has two elements, which
`subsingleton_of_corepresentable` forbids. -/
theorem image_powerset_not_corepresentable (A : Type) :
    IsEmpty (imagePowerset.CorepresentableBy A) := by
  constructor
  intro e
  have hsub := subsingleton_of_corepresentable e
  have h : (∅ : Set PUnit) = Set.univ := hsub.elim _ _
  have hmem : PUnit.unit ∈ (∅ : Set PUnit) := by
    rw [h]
    exact Set.mem_univ _
  exact hmem
-- @endregion

/-! ### Products, quotients and free objects as representing objects -/

-- @region representable_functors.pairs_of_maps
-- @provenance definition
/-- The functor `X ↦ Hom(X, A) × Hom(X, B)` (pairs of maps out of `X`), contravariant in `X`:
a map `f : Y → X` turns a pair `(p, q)` into `(p ∘ f, q ∘ f)`. -/
def pairsOfMaps (A B : Type) : Typeᵒᵖ ⥤ Type where
  obj X := (X.unop → A) × (X.unop → B)
  map f := ↾fun pq => (pq.1 ∘ f.unop, pq.2 ∘ f.unop)
-- @endregion

-- @region representable_functors.product_represents
-- @provenance independent
/-- **The product represents pairs of maps**: `Hom(X, A × B) ≃ Hom(X, A) × Hom(X, B)`,
naturally in `X`, by `h ↦ (π₁ ∘ h, π₂ ∘ h)` with inverse `(p, q) ↦ ⟨p, q⟩`. This is exactly the
universal property of the product, read as a representation. -/
theorem product_represents (A B : Type) : Nonempty ((pairsOfMaps A B).RepresentableBy (A × B)) :=
  ⟨{ homEquiv :=
      { toFun := fun h => (Prod.fst ∘ h, Prod.snd ∘ h)
        invFun := fun pq => ↾fun x => (pq.1 x, pq.2 x)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
     homEquiv_comp := fun _ _ => rfl }⟩
-- @endregion

-- @region representable_functors.respecting_maps
-- @provenance definition
/-- For an equivalence relation `s` on `X`, the covariant functor sending `Y` to the maps
`X → Y` that are constant on equivalence classes (`a ≈ b → f a = f b`). -/
def respectingMaps {X : Type} (s : Setoid X) : Type ⥤ Type where
  obj Y := {f : X → Y // ∀ a b, a ≈ b → f a = f b}
  map g := ↾fun f => ⟨(g : _ → _) ∘ f.1, fun a b hab => by simp [f.2 a b hab]⟩
-- @endregion

-- @region representable_functors.quotient_corepresents
-- @provenance independent
/-- **The quotient corepresents maps that respect the relation**:
`Hom(X ⧸ ~, Y) ≃ {f : X → Y | a ~ b → f a = f b}`, naturally in `Y`, by composing with the
quotient map. Surjectivity is `Quotient.lift` ("a respecting map factors through the
quotient") and injectivity holds because every element of `X ⧸ ~` is a class `[a]`. -/
theorem quotient_corepresents {X : Type} (s : Setoid X) :
    Nonempty ((respectingMaps s).CorepresentableBy (Quotient s)) :=
  ⟨{ homEquiv :=
      { toFun := fun h => ⟨(h : _ → _) ∘ Quotient.mk s, fun a b hab => by
          simp [Quotient.sound hab]⟩
        invFun := fun f => ↾Quotient.lift f.1 f.2
        left_inv := fun h => by
          ext q
          induction q using Quotient.ind
          rfl
        right_inv := fun _ => rfl }
     homEquiv_comp := fun _ _ => rfl }⟩
-- @endregion

-- @region representable_functors.free_monoid_universal
-- @provenance library
/-- **The free monoid represents "maps of the generators"**: every function `f : α → M` into a
monoid extends to exactly one monoid homomorphism `FreeMonoid α → M` (words are sent to
products). This applies Mathlib's `FreeMonoid.lift` and `FreeMonoid.hom_eq`; it says that
`(FreeMonoid α, of)` is a universal element of `M ↦ (α → M)`. -/
theorem free_monoid_universal {α M : Type*} [Monoid M] (f : α → M) :
    ∃! φ : FreeMonoid α →* M, ∀ a, φ (FreeMonoid.of a) = f a :=
  ⟨FreeMonoid.lift f, fun a => FreeMonoid.lift_eval_of f a,
    fun ψ hψ => FreeMonoid.hom_eq fun a => by rw [hψ a, FreeMonoid.lift_eval_of]⟩
-- @endregion

-- @region representable_functors.limit_of_representable
-- @provenance library
/-- **Limits are representing objects.** For a diagram `K : J ⥤ C`, a representation of the
functor `X ↦ {cones over K with apex X}` by an object `L` makes the cone corresponding to `id_L`
a limit cone. This applies Mathlib's `IsLimit.ofRepresentableBy`. -/
theorem limit_of_representable {J C : Type*} [Category J] [Category C] {K : J ⥤ C} {L : C}
    (h : K.cones.RepresentableBy L) :
    Nonempty (Limits.IsLimit (Limits.IsLimit.OfNatIso.limitCone h)) :=
  ⟨Limits.IsLimit.ofRepresentableBy h⟩
-- @endregion

end Lumenary.RepresentableFunctors
