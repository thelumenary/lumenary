/-
The Lumenary — formal mathematics
Natural transformations: naturality squares, uniformity, the double dual, the determinant,
functor categories and equivalences of categories.

What is proved here. Using Mathlib's categories (`CategoryTheory.Functor`, `NatTrans`), we prove
that naturality is a strong *uniformity* condition: every natural transformation from the
functor `X ↦ X × X` to the identity functor on types is one of the two projections, and the only
natural transformation from the identity functor on types to itself is the identity. We check
the naturality square of the double-dual map `V → V**` by computation, and prove that a line over
a field with more than three elements carries no automorphism-invariant pairing (the reason
`V ≅ V*` is not natural even when restricted to isomorphisms). The determinant is assembled into
a genuine natural transformation `GLₙ ⟶ (−)ˣ` of functors `CommRingCat ⥤ GrpCat`. For
equivalences, the direction "an equivalence is faithful, full and essentially surjective" is
proved by hand, mirroring the lesson's proof; the converse (which needs the axiom of choice) is
Mathlib's `Functor.asEquivalence`. Finally, a two-object category with an isomorphism between
its objects is equivalent, but not isomorphic, to the one-object category.

What Mathlib provides. `NatTrans`, the functor category instance `Functor.category`,
`NatTrans.comp_app`, `NatIso.isIso_of_isIso_app`, `Module.Dual.eval` and
`Module.Dual.eval_naturality`, `Module.bijective_dual_eval`, `Matrix.GeneralLinearGroup.map_det`,
`Functor.IsEquivalence` and `Functor.asEquivalence`. Not formalised here: the equivalence between
finite-dimensional vector spaces and matrices, and the failure of `V → V**` to be onto in
infinite dimension.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace Lumenary.NaturalTransformations

open CategoryTheory

universe v₁ v₂ u₁ u₂ u

/-! ### Naturality as uniformity: functors on types -/

-- @region natural_transformations.sq
-- @provenance definition
/-- The **squaring functor** on types: `X ↦ X × X`, and a function `f : X → Y` acts on pairs
coordinatewise, `(a, b) ↦ (f a, f b)`. (In this Mathlib, morphisms in the category of types are
wrapped functions; `↾g` turns a function `g` into a morphism.) -/
def sq : Type u ⥤ Type u where
  obj X := X × X
  map f := ↾(Prod.map f f)
-- @endregion

-- @region natural_transformations.natural_sq_to_id
-- @provenance independent
/-- **Every natural family of maps `X × X → X` is a projection.** Suppose `α X : X × X → X` is
given for every type `X`, and is natural: `α Y (f a, f b) = f (α X (a, b))` for every function
`f : X → Y`. Then either `α X (a, b) = a` for all `X, a, b`, or `α X (a, b) = b` for all.

Proof (as in the lesson). Look at one test case: the pair `(true, false)` in the two-element type
`B`. For any `X` and `(a, b)`, the function `f : B → X` with `f true = a`, `f false = b` sends
`(true, false)` to `(a, b)`, so naturality gives `α X (a, b) = f (α B (true, false))`. Hence the
whole family is decided by one value, `α B (true, false)`, which is `true` (projection to `a`) or
`false` (projection to `b`). `ULift` moves `Bool` into the universe `u`. -/
theorem natural_sq_to_id (α : ∀ X : Type u, X × X → X)
    (nat : ∀ (X Y : Type u) (f : X → Y) (p : X × X), α Y (f p.1, f p.2) = f (α X p)) :
    (∀ (X : Type u) (p : X × X), α X p = p.1) ∨ (∀ (X : Type u) (p : X × X), α X p = p.2) := by
  -- Every component is determined by the single value `α B (true, false)`.
  have key : ∀ (X : Type u) (p : X × X),
      α X p = (if (α (ULift.{u} Bool) (⟨true⟩, ⟨false⟩)).down then p.1 else p.2) := by
    intro X p
    have h := nat (ULift.{u} Bool) X (fun b => if b.down then p.1 else p.2) (⟨true⟩, ⟨false⟩)
    simpa using h
  rcases h : α (ULift.{u} Bool) (⟨true⟩, ⟨false⟩) with ⟨b⟩
  cases b
  · right
    intro X p
    rw [key, h]
    rfl
  · left
    intro X p
    rw [key, h]
    rfl
-- @endregion

-- @region natural_transformations.nat_trans_sq_to_id
-- @provenance independent
/-- The same theorem for Mathlib's bundled natural transformations: every `α : sq ⟶ 𝟭 (Type u)`
is the first or the second projection. The naturality square of `α` at `f`, applied to an
element (`NatTrans.naturality_apply`), is exactly the hypothesis of `natural_sq_to_id`. -/
theorem natTrans_sq_to_id (α : sq ⟶ 𝟭 (Type u)) :
    (∀ (X : Type u) (p : X × X), α.app X p = p.1) ∨
      (∀ (X : Type u) (p : X × X), α.app X p = p.2) := by
  apply natural_sq_to_id (fun X => α.app X)
  intro X Y f p
  exact NatTrans.naturality_apply α (↾f) p
-- @endregion

-- @region natural_transformations.natural_id_to_id
-- @provenance independent
/-- **The identity functor on types has only the identity as natural endo-transformation.**
If `α X : X → X` is natural, then for `x : X` take `f : PUnit → X` with value `x`; naturality
says `α X (f ()) = f (α PUnit ())`, and the right side is `x` whatever `α PUnit ()` is. -/
theorem natural_id_to_id (α : ∀ X : Type u, X → X)
    (nat : ∀ (X Y : Type u) (f : X → Y) (x : X), α Y (f x) = f (α X x)) :
    ∀ (X : Type u) (x : X), α X x = x := by
  intro X x
  exact nat PUnit X (fun _ => x) PUnit.unit
-- @endregion

-- @region natural_transformations.nat_trans_id_eq
-- @provenance independent
/-- Bundled form: the only natural transformation `𝟭 (Type u) ⟶ 𝟭 (Type u)` is the identity
`𝟙 _`, i.e. the endomorphism monoid of the identity functor on types is trivial. -/
theorem natTrans_id_eq (α : 𝟭 (Type u) ⟶ 𝟭 (Type u)) : α = 𝟙 _ := by
  ext X x
  exact natural_id_to_id (fun X => α.app X)
    (fun X Y f x => by simpa using NatTrans.naturality_apply α (↾f) x) X x
-- @endregion

-- @region natural_transformations.reverse_nat
-- @provenance definition
/-- **List reversal is a natural transformation** from the list functor to itself
(`ofTypeFunctor List` is Mathlib's functor `X ↦ List X`, acting on functions by `List.map`).
The naturality square says `reverse (map f xs) = map f (reverse xs)`: it does not matter whether
we relabel the entries before or after reversing. This is core Lean's `List.map_reverse`. -/
def reverseNat : ofTypeFunctor List ⟶ ofTypeFunctor List where
  app X := ↾List.reverse
  naturality X Y f := by
    ext xs
    exact (List.map_reverse ..).symm
-- @endregion

/-! ### The double dual -/

section DoubleDual

variable {R : Type u} [CommRing R]

-- @region natural_transformations.double_dual_naturality
-- @provenance independent
/-- **The double-dual map is natural.** `Module.Dual.eval R V : V → V**` sends `v` to
"evaluate at `v`", `φ ↦ φ v`. For every linear `f : V → W` the square
`f** ∘ ev_V = ev_W ∘ f` commutes: both sides send `v` and `φ ∈ W*` to `φ (f v)`, since
`f** (ev_V v) φ = ev_V v (f* φ) = (φ ∘ f) v`. Lean checks the two sides agree by computation
(`rfl`) after applying both to `v` and `φ`; Mathlib states the same fact as
`Module.Dual.eval_naturality`. -/
theorem double_dual_naturality {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] (f : V →ₗ[R] W) :
    f.dualMap.dualMap ∘ₗ Module.Dual.eval R V = Module.Dual.eval R W ∘ₗ f := by
  ext v φ
  rfl
-- @endregion

-- @region natural_transformations.double_dual_bijective
-- @provenance library
/-- **In finite dimension the double-dual map is an isomorphism**, so `ev` is a natural
isomorphism from the identity functor to the double-dual functor on finite-dimensional spaces.
This applies Mathlib's `Module.bijective_dual_eval` (finite-dimensional spaces are reflexive).
Without finite dimension it fails: `ev` is still injective but no longer onto. -/
theorem double_dual_bijective {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Function.Bijective (Module.Dual.eval K V) :=
  Module.bijective_dual_eval K V
-- @endregion

-- @region natural_transformations.no_invariant_pairing
-- @provenance independent
/-- **A line has no automorphism-invariant pairing over a field with more than three elements.**
A natural isomorphism `V → V*` on the groupoid of vector spaces and linear isomorphisms would
give, for `V = K`, a linear map `φ : K → K*` with `φ (μ v) (μ w) = φ v w` for every unit `μ`
(see the lesson). If some unit `λ` has `λ² ≠ 1`, such a `φ` must be zero, so it is not an
isomorphism. Proof: by linearity `φ v w = v w · φ 1 1`; invariance under `λ` gives
`λ² · φ 1 1 = φ 1 1`, so `(λ² − 1) · φ 1 1 = 0` and `φ 1 1 = 0`. -/
theorem no_invariant_pairing {K : Type u} [Field K] (φ : K →ₗ[K] Module.Dual K K)
    (hφ : ∀ (μ : Kˣ) (v w : K), φ (μ * v) (μ * w) = φ v w) (lam : Kˣ) (hlam : lam ^ 2 ≠ 1) :
    φ = 0 := by
  -- Step 1: `φ` is determined by the number `φ 1 1`.
  have h1 : ∀ v w : K, φ v w = v * w * φ 1 1 := by
    intro v w
    have hv : φ v = v • φ 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [hv, LinearMap.smul_apply, smul_eq_mul]
    have hw : φ 1 w = w * φ 1 1 := by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [hw, mul_assoc]
  -- Step 2: invariance under `λ` forces `φ 1 1 = 0`.
  have h2 : φ 1 1 = 0 := by
    have hinv := hφ lam 1 1
    rw [h1, h1, mul_one, one_mul, one_mul] at hinv
    have h3 : ((lam : K) * lam - 1) * φ 1 1 = 0 := by rw [sub_mul, hinv, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exfalso
      apply hlam
      ext
      rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one]
      exact sub_eq_zero.mp h
    · exact h
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [h1, h2, mul_zero]
  rfl
-- @endregion

end DoubleDual

/-! ### The determinant as a natural transformation -/

section Determinant

variable (n : Type) [Fintype n] [DecidableEq n]

-- @region natural_transformations.gl_functor
-- @provenance definition
/-- The **general linear group functor** `GLₙ : CommRingCat ⥤ GrpCat`: a commutative ring `R`
goes to the group of invertible `n × n` matrices over `R`, and a ring homomorphism `f : R → S`
goes to the group homomorphism applying `f` to every entry (`Matrix.GeneralLinearGroup.map`). -/
noncomputable def glFunctor : CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.GeneralLinearGroup n R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map f.hom)
-- @endregion

-- @region natural_transformations.units_functor
-- @provenance definition
/-- The **units functor** `(−)ˣ : CommRingCat ⥤ GrpCat`: a ring goes to its group of units, a
ring homomorphism to its restriction to units (`Units.map`). -/
def unitsFunctor : CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of Rˣ
  map f := GrpCat.ofHom (Units.map f.hom.toMonoidHom)
-- @endregion

-- @region natural_transformations.det_nat
-- @provenance definition
/-- **The determinant is natural in the ring.** Its components are the group homomorphisms
`det : GLₙ(R) → Rˣ`; the naturality square for `f : R → S` says
`det (f(M)) = f (det M)`: applying `f` to the entries and then taking the determinant gives the
same as taking the determinant and then applying `f`, because the determinant is a polynomial
in the entries with integer coefficients. This is Mathlib's `Matrix.GeneralLinearGroup.map_det`. -/
noncomputable def detNat : glFunctor.{u} n ⟶ unitsFunctor.{u} where
  app R := GrpCat.ofHom Matrix.GeneralLinearGroup.det
  naturality R S f := by
    ext g
    exact Matrix.GeneralLinearGroup.map_det f.hom g
-- @endregion

end Determinant

/-! ### Functor categories -/

section FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- @region natural_transformations.comp_app
-- @provenance library
/-- **Vertical composition is computed componentwise.** In the functor category `C ⥤ D`
(Mathlib's instance `Functor.category`), the composite of `α : F ⟶ G` and `β : G ⟶ H` has
components `(α ≫ β).app X = α.app X ≫ β.app X`. This applies Mathlib's `NatTrans.comp_app`. -/
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X :=
  NatTrans.comp_app α β X
-- @endregion

-- @region natural_transformations.is_iso_of_components
-- @provenance library
/-- **A natural transformation whose components are isomorphisms is a natural isomorphism**:
it is invertible in the functor category, because the inverse components are automatically
natural. This applies Mathlib's `NatIso.isIso_of_isIso_app`. -/
theorem isIso_of_components {F G : C ⥤ D} (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  NatIso.isIso_of_isIso_app α
-- @endregion

end FunctorCategory

/-! ### Equivalences of categories -/

section Equivalences

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- @region natural_transformations.faithful_of_unit_iso
-- @provenance independent
/-- **A functor with a quasi-inverse is faithful.** If `η : 𝟭 C ≅ F ⋙ G`, then naturality of `η`
lets us recover every morphism `k : X ⟶ Y` from `F.map k`:
`k = η_X ≫ G.map (F.map k) ≫ η_Y⁻¹` (diagrammatic order: first `η_X`). So `F.map f = F.map g`
forces `f = g`. -/
theorem faithful_of_unitIso (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) : F.Faithful where
  map_injective {X Y} {f g} h := by
    have key : ∀ k : X ⟶ Y, k = η.hom.app X ≫ G.map (F.map k) ≫ η.inv.app Y := by
      intro k
      calc k = k ≫ η.hom.app Y ≫ η.inv.app Y := by simp
        _ = (k ≫ η.hom.app Y) ≫ η.inv.app Y := by rw [Category.assoc]
        _ = (η.hom.app X ≫ G.map (F.map k)) ≫ η.inv.app Y := by
          rw [show k ≫ η.hom.app Y = η.hom.app X ≫ G.map (F.map k) from η.hom.naturality k]
        _ = η.hom.app X ≫ G.map (F.map k) ≫ η.inv.app Y := by rw [Category.assoc]
    rw [key f, key g, h]
-- @endregion

-- @region natural_transformations.ess_surj_of_counit_iso
-- @provenance independent
/-- **A functor with a quasi-inverse is essentially surjective**: every object `Y` of `D` is
isomorphic to `F (G Y)`, by the component `ε_Y` of `ε : G ⋙ F ≅ 𝟭 D`. -/
theorem essSurj_of_counitIso (F : C ⥤ D) (G : D ⥤ C) (ε : G ⋙ F ≅ 𝟭 D) : F.EssSurj where
  mem_essImage Y := ⟨G.obj Y, ⟨ε.app Y⟩⟩
-- @endregion

-- @region natural_transformations.full_of_equivalence
-- @provenance independent
/-- **A functor with a quasi-inverse is full.** Given `h : F X ⟶ F Y`, put
`f = η_X ≫ G.map h ≫ η_Y⁻¹ : X ⟶ Y`. Naturality of `η` gives `G.map (F.map f) = G.map h`, and
`G` is faithful (by `faithful_of_unitIso` applied to `G`, with `ε⁻¹ : 𝟭 D ≅ G ⋙ F`), so
`F.map f = h`. This is the proof in the lesson, step by step. -/
theorem full_of_equivalence (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G)
    (ε : G ⋙ F ≅ 𝟭 D) : F.Full where
  map_surjective {X Y} h := by
    have hG : G.Faithful := faithful_of_unitIso G F ε.symm
    refine ⟨η.hom.app X ≫ G.map h ≫ η.inv.app Y, G.map_injective ?_⟩
    -- Naturality of `η` at `f`: `f ≫ η_Y = η_X ≫ G.map (F.map f)`.
    have hnat := η.hom.naturality (η.hom.app X ≫ G.map h ≫ η.inv.app Y)
    simp only [Functor.id_map, Functor.comp_map, Functor.id_obj] at hnat
    calc G.map (F.map (η.hom.app X ≫ G.map h ≫ η.inv.app Y))
        = η.inv.app X ≫ η.hom.app X ≫ G.map (F.map (η.hom.app X ≫ G.map h ≫ η.inv.app Y)) := by
          simp
      _ = η.inv.app X ≫ (η.hom.app X ≫ G.map h ≫ η.inv.app Y) ≫ η.hom.app Y := by rw [hnat]
      _ = G.map h := by simp
-- @endregion

-- @region natural_transformations.equivalence_iff
-- @provenance library
/-- **Characterisation of equivalences.** A functor `F` has a quasi-inverse `G` (with natural
isomorphisms `𝟭 C ≅ F ⋙ G` and `G ⋙ F ≅ 𝟭 D`) if and only if it is full, faithful and
essentially surjective. (→) is `Functor.IsEquivalence.mk'` (the three lemmas above prove it by
hand). (←) is Mathlib's `Functor.asEquivalence`, which *chooses* for each object `Y` of `D` an
object `X` with `F X ≅ Y` — this direction uses the axiom of choice. -/
theorem equivalence_iff (F : C ⥤ D) :
    (∃ G : D ⥤ C, Nonempty (𝟭 C ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 D)) ↔
      F.Full ∧ F.Faithful ∧ F.EssSurj := by
  constructor
  · rintro ⟨G, ⟨η⟩, ⟨ε⟩⟩
    have := Functor.IsEquivalence.mk' G η ε
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨h₁, h₂, h₃⟩
    have : F.IsEquivalence := {}
    exact ⟨F.inv, ⟨F.asEquivalence.unitIso⟩, ⟨F.asEquivalence.counitIso⟩⟩
-- @endregion

end Equivalences

/-! ### Equivalent but not isomorphic -/

-- @region natural_transformations.codiscrete_equivalence
-- @provenance definition
/-- **Two isomorphic objects are "the same" as one object.** `Codiscrete Bool` is the category
with two objects and exactly one morphism between any two (so the two objects are isomorphic);
`Codiscrete Unit` has one object and only its identity. Collapsing and picking an object are
quasi-inverse functors: any two functors into a codiscrete category are naturally isomorphic
(Mathlib's `Codiscrete.natIso`). -/
def codiscreteEquivalence : Codiscrete Bool ≌ Codiscrete Unit :=
  CategoryTheory.Equivalence.mk (Codiscrete.functorOfFun fun _ => ())
    (Codiscrete.functorOfFun fun _ => true) Codiscrete.natIso Codiscrete.natIso
-- @endregion

-- @region natural_transformations.codiscrete_not_isomorphic
-- @provenance independent
/-- **Equivalent categories need not be isomorphic.** There are no functors
`F : Codiscrete Bool ⥤ Codiscrete Unit` and `G` back with `F ⋙ G = 𝟭` (on the nose): `F` would
have to be injective on objects, but it sends both objects to the only object. -/
theorem codiscrete_not_isomorphic :
    ¬ ∃ (F : Codiscrete Bool ⥤ Codiscrete Unit) (G : Codiscrete Unit ⥤ Codiscrete Bool),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ := by
  rintro ⟨F, G, h, -⟩
  have h1 : G.obj (F.obj ⟨true⟩) = ⟨true⟩ := congrArg (fun H => H.obj ⟨true⟩) h
  have h2 : G.obj (F.obj ⟨false⟩) = ⟨false⟩ := congrArg (fun H => H.obj ⟨false⟩) h
  have hU : ∀ a b : Codiscrete Unit, a = b := fun ⟨()⟩ ⟨()⟩ => rfl
  rw [hU (F.obj ⟨true⟩) (F.obj ⟨false⟩), h2] at h1
  exact Bool.false_ne_true (congrArg Codiscrete.as h1)
-- @endregion

end Lumenary.NaturalTransformations
