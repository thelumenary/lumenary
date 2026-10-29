/-
The Lumenary — formal mathematics
Categories: the axioms, examples (matrices, preorders, monoids), isomorphisms and the uniqueness
of inverses, monomorphisms and epimorphisms in sets, the epimorphism `ℤ → ℚ` of rings, and duality.

We use Mathlib's `CategoryTheory.Category` throughout, so that learners meet the real library.
Mathlib writes composition in *diagrammatic* order: `f ≫ g` means "first `f`, then `g`", which
the lesson writes `g ∘ f`. Identities are `𝟙 X`.

Proved here (`independent`): a left inverse equals a right inverse (so inverses are unique); the
category of matrices (objects are natural numbers, which have no elements to speak of); in a
partial order regarded as a category isomorphic objects are equal; isomorphisms in the
one-object category of a monoid are exactly its invertible elements; monomorphisms of sets are
the injections and epimorphisms the surjections (stated for functions between Lean types);
ring homomorphisms out of `ℚ` are determined by their values on `ℤ` although `ℤ → ℚ` is not
surjective; and a morphism is a monomorphism exactly when its opposite is an epimorphism.
Mathlib provides (`library`): the same facts for its category `Type u`
(`CategoryTheory.mono_iff_injective`, `CategoryTheory.epi_iff_surjective`), uniqueness of
inverses (`IsIso.inv_eq_of_hom_inv_id`), the preorder and one-object categories, and duality
(`CategoryTheory.op_epi_iff`).
-/
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Category.Ring.Basic

namespace Lumenary.Categories

open CategoryTheory

universe u v

/-! ### Inverses are unique -/

-- @region categories.left_inv_eq_right_inv
-- @provenance independent
/-- **A left inverse equals a right inverse.** In any category, if `g ∘ f = id_X` and
`f ∘ h = id_Y` then `g = h`. In Mathlib's diagrammatic notation `g ∘ f` is `f ≫ g`.
The proof is the one-line calculation of the lesson:
`g = g ∘ id_Y = g ∘ (f ∘ h) = (g ∘ f) ∘ h = id_X ∘ h = h`, using only the identity and
associativity axioms. Consequently an isomorphism has exactly one inverse. -/
theorem left_inv_eq_right_inv {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}
    {g h : Y ⟶ X} (hg : f ≫ g = 𝟙 X) (hh : h ≫ f = 𝟙 Y) : g = h :=
  calc g = 𝟙 Y ≫ g := (Category.id_comp g).symm
    _ = (h ≫ f) ≫ g := by rw [hh]
    _ = h ≫ (f ≫ g) := Category.assoc h f g
    _ = h ≫ 𝟙 X := by rw [hg]
    _ = h := Category.comp_id h
-- @endregion

-- @region categories.inverse_unique
-- @provenance independent
/-- **Inverses are unique.** If `g` and `g'` are both two-sided inverses of `f`, then `g = g'`.
This is `left_inv_eq_right_inv` applied to the left inverse `g` and the right inverse `g'`. -/
theorem inverse_unique {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y} {g g' : Y ⟶ X}
    (hg : f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y) (hg' : f ≫ g' = 𝟙 X ∧ g' ≫ f = 𝟙 Y) : g = g' :=
  left_inv_eq_right_inv hg.1 hg'.2
-- @endregion

-- @region categories.inv_eq_library
-- @provenance library
/-- Mathlib's version: if `f` is an isomorphism (`IsIso f`), its chosen inverse `inv f` equals
any `g` with `f ≫ g = 𝟙 X`. This applies `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`. -/
theorem inv_eq_library {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ X) (hg : f ≫ g = 𝟙 X) : inv f = g :=
  IsIso.inv_eq_of_hom_inv_id hg
-- @endregion

/-! ### A category whose objects have no elements: matrices -/

-- @region categories.mat
-- @provenance definition
/-- The objects of the category of matrices: one object for each natural number `dim`
(a wrapper around `ℕ`, so that Lean does not confuse this category with the order on `ℕ`). -/
structure Mat where
  /-- The size of the column vectors at this object. -/
  dim : ℕ
-- @endregion

-- @region categories.mat_category
-- @provenance definition
/-- **The category of rational matrices.** Objects are natural numbers `m, n, …`; a morphism
`m ⟶ n` is an `n × m` matrix (it turns column vectors of length `m` into vectors of length
`n`); composition is matrix multiplication (`f ≫ g = g * f`, "first `f`, then `g`") and the
identity on `n` is the identity matrix. The axioms are the associativity and unit laws of
matrix multiplication (`Matrix.mul_assoc`, `Matrix.one_mul`, `Matrix.mul_one`). The objects are
just numbers: a morphism is not a function between sets of elements. -/
instance matCategory : Category.{0} Mat where
  Hom m n := Matrix (Fin n.dim) (Fin m.dim) ℚ
  id n := (1 : Matrix (Fin n.dim) (Fin n.dim) ℚ)
  comp f g := g * f
  id_comp f := Matrix.mul_one f
  comp_id f := Matrix.one_mul f
  assoc f g h := (Matrix.mul_assoc h g f).symm
-- @endregion

/-! ### Preorders and monoids as categories -/

-- @region categories.preorder_hom_unique
-- @provenance library
/-- In a preorder regarded as a category (Mathlib's instance `Preorder.smallCategory`), there is
a morphism `x ⟶ y` exactly when `x ≤ y`, and **any two morphisms `x ⟶ y` are equal**: a morphism
carries no information beyond the fact `x ≤ y`. This applies `Subsingleton.elim` to Mathlib's
instance saying that hom-types of a preorder category are subsingletons. -/
theorem preorder_hom_unique {α : Type u} [Preorder α] {x y : α} (f g : x ⟶ y) : f = g :=
  Subsingleton.elim f g
-- @endregion

-- @region categories.preorder_iso_eq
-- @provenance independent
/-- In a **partial order** regarded as a category, isomorphic objects are equal: an isomorphism
`x ≅ y` provides morphisms `x ⟶ y` and `y ⟶ x`, that is `x ≤ y` and `y ≤ x`, and antisymmetry
gives `x = y`. (In a preorder that is not antisymmetric, distinct objects can be isomorphic.) -/
theorem preorder_iso_eq {α : Type u} [PartialOrder α] {x y : α} (e : x ≅ y) : x = y :=
  le_antisymm (leOfHom e.hom) (leOfHom e.inv)
-- @endregion

-- @region categories.monoid_comp
-- @provenance library
/-- **A monoid is a category with one object.** Mathlib's `SingleObj M` has a single object
`star M`; its morphisms are the elements of `M`, the identity is `1` and composition is
multiplication: "first `x`, then `y`" is `y * x`. This applies `SingleObj.comp_as_mul`. -/
theorem monoid_comp (M : Type u) [Monoid M] (x y : SingleObj.star M ⟶ SingleObj.star M) :
    x ≫ y = y * x :=
  SingleObj.comp_as_mul M x y
-- @endregion

-- @region categories.monoid_is_iso_iff
-- @provenance independent
/-- In the one-object category of a monoid `M`, **the isomorphisms are exactly the invertible
elements (units) of `M`.** An inverse of the morphism `x` is an element `y` with
`x ≫ y = y * x = 1` and `y ≫ x = x * y = 1`. So "isomorphism" generalises "invertible element"
— for the monoid `(ℤ, ×)` only `1` and `-1` are isomorphisms. -/
theorem monoid_isIso_iff (M : Type u) [Monoid M] (x : SingleObj.star M ⟶ SingleObj.star M) :
    IsIso x ↔ IsUnit (show M from x) := by
  constructor
  · intro hx
    -- the inverse of `x` in the category is a two-sided inverse in the monoid
    have h1 : x * inv x = 1 := IsIso.inv_hom_id x
    have h2 : inv x * x = 1 := IsIso.hom_inv_id x
    exact ⟨⟨x, inv x, h1, h2⟩, rfl⟩
  · rintro ⟨u, hu⟩
    refine ⟨⟨(u⁻¹ : Mˣ), ?_, ?_⟩⟩
    · show (u⁻¹ : Mˣ) * x = 1
      rw [← hu, Units.inv_mul]
    · show x * (u⁻¹ : Mˣ) = 1
      rw [← hu, Units.mul_inv]
-- @endregion

/-! ### Monomorphisms and epimorphisms of sets -/

-- @region categories.mono_iff_injective
-- @provenance independent
/-- **In sets, the monomorphisms are the injections.** A function `f : X → Y` is a
monomorphism if it can be cancelled on the left: `f ∘ g = f ∘ h` implies `g = h` for all
`g, h : Z → X`. (Stated here for Lean types and functions, the type-theoretic version of
**Set**.) If `f` is a monomorphism and `f a = f b`, test it against the two maps from a
one-element set picking out `a` and `b`; conversely an injection can be cancelled pointwise. -/
theorem mono_iff_injective {X Y : Type u} (f : X → Y) :
    (∀ (Z : Type u) (g h : Z → X), f ∘ g = f ∘ h → g = h) ↔ Function.Injective f := by
  constructor
  · intro hf a b hab
    -- test maps from the one-element type `PUnit`
    have := hf PUnit (fun _ => a) (fun _ => b) (funext fun _ => hab)
    exact congrFun this PUnit.unit
  · intro hf Z g h hgh
    funext z
    exact hf (congrFun hgh z)
-- @endregion

-- @region categories.epi_iff_surjective
-- @provenance independent
/-- **In sets, the epimorphisms are the surjections.** A function `f : X → Y` is an
epimorphism if `g ∘ f = h ∘ f` implies `g = h` for all `g, h : Y → Z`.
If `f` is an epimorphism, compare two maps into the two-element "set of truth values":
`g y = (y is in the image of f)` and `h y = true`. They agree after `f`, so they agree, so every
`y` is in the image. Conversely, if `f` is surjective, every `y` is some `f x`, where `g` and `h`
agree. (`ULift` only moves the type of propositions into the universe of `Y`.) -/
theorem epi_iff_surjective {X Y : Type u} (f : X → Y) :
    (∀ (Z : Type u) (g h : Y → Z), g ∘ f = h ∘ f → g = h) ↔ Function.Surjective f := by
  constructor
  · intro hf y
    let g : Y → ULift.{u} Prop := fun y => ULift.up (∃ x, f x = y)
    let h : Y → ULift.{u} Prop := fun _ => ULift.up True
    have hgh : g ∘ f = h ∘ f := by
      funext x
      simp only [Function.comp, g, h, ULift.up.injEq, eq_iff_iff, iff_true]
      exact ⟨x, rfl⟩
    have hy : g y = h y := congrFun (hf _ g h hgh) y
    simp only [g, h, ULift.up.injEq, eq_iff_iff, iff_true] at hy
    exact hy
  · intro hf Z g h hgh
    funext y
    obtain ⟨x, rfl⟩ := hf y
    exact congrFun hgh x
-- @endregion

-- @region categories.types_mono_epi_library
-- @provenance library
/-- Mathlib's versions for its category `Type u` (whose morphisms wrap functions): a morphism is
a monomorphism iff it is injective and an epimorphism iff it is surjective. This applies
`CategoryTheory.mono_iff_injective` and `CategoryTheory.epi_iff_surjective`. -/
theorem types_mono_epi_library {X Y : Type u} (f : X ⟶ Y) :
    (Mono f ↔ Function.Injective f) ∧ (Epi f ↔ Function.Surjective f) :=
  ⟨CategoryTheory.mono_iff_injective f, CategoryTheory.epi_iff_surjective f⟩
-- @endregion

/-! ### An epimorphism that is not surjective: `ℤ → ℚ` in rings -/

-- @region categories.rat_hom_eq_of_eq_on_int
-- @provenance independent
/-- **The inclusion `ℤ → ℚ` is an epimorphism of rings**: two ring homomorphisms
`f, g : ℚ → R` that agree on the integers agree everywhere.
Proof, as in the lesson: write `q = a / b` with `b ≠ 0`. In `R`, `f (1/b)` is a two-sided
inverse of `f b`, and `g (1/b)` is a two-sided inverse of `g b = f b`; inverses in a monoid are
unique (Mathlib's monoid lemma `left_inv_eq_right_inv`), so `f (1/b) = g (1/b)`, and then
`f q = f a · f (1/b) = g a · g (1/b) = g q`. -/
theorem rat_hom_eq_of_eq_on_int {R : Type u} [Ring R] (f g : ℚ →+* R)
    (h : ∀ n : ℤ, f n = g n) : f = g := by
  ext q
  have hb : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  -- `f (1/b)` and `g (1/b)` are inverses of the same element `f b = g b`
  have hfb : f (q.den : ℚ) = g (q.den : ℚ) := by
    exact_mod_cast h q.den
  have hinv : f (q.den : ℚ)⁻¹ = g (q.den : ℚ)⁻¹ := by
    have left : f (q.den : ℚ)⁻¹ * f (q.den : ℚ) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb, map_one]
    have right : g (q.den : ℚ) * g (q.den : ℚ)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hb, map_one]
    rw [hfb] at left
    exact _root_.left_inv_eq_right_inv left right
  calc f q = f ((q.num : ℚ) * (q.den : ℚ)⁻¹) := by rw [← div_eq_mul_inv, Rat.num_div_den]
    _ = f q.num * f (q.den : ℚ)⁻¹ := by rw [map_mul]
    _ = g q.num * g (q.den : ℚ)⁻¹ := by rw [h q.num, hinv]
    _ = g ((q.num : ℚ) * (q.den : ℚ)⁻¹) := by rw [map_mul]
    _ = g q := by rw [← div_eq_mul_inv, Rat.num_div_den]
-- @endregion

-- @region categories.int_to_rat_epi
-- @provenance independent
/-- The same fact stated in Mathlib's category `RingCat` of rings: the morphism
`ℤ ⟶ ℚ` given by the inclusion is an epimorphism (`Epi`). Two morphisms `g, h : ℚ ⟶ R` with
`ι ≫ g = ι ≫ h` agree on every integer `n`, so `rat_hom_eq_of_eq_on_int` makes them equal. -/
theorem int_to_rat_epi : Epi (RingCat.ofHom (Int.castRingHom ℚ)) := by
  constructor
  intro R g h hgh
  apply RingCat.hom_ext
  apply rat_hom_eq_of_eq_on_int
  intro n
  have := congrArg (fun φ => φ.hom n) hgh
  simp only [RingCat.hom_comp, RingCat.hom_ofHom, RingHom.comp_apply, Int.coe_castRingHom]
    at this
  exact this
-- @endregion

-- @region categories.rat_hom_ext_library
-- @provenance library
/-- Mathlib's stronger statement: *any* two ring homomorphisms from `ℚ` to a semiring are equal
(they automatically agree on `ℤ`). This applies `RingHom.ext_rat`. -/
theorem rat_hom_ext_library {R : Type u} [Semiring R] (f g : ℚ →+* R) : f = g :=
  RingHom.ext_rat f g
-- @endregion

-- @region categories.int_cast_not_surjective
-- @provenance independent
/-- …but the inclusion `ℤ → ℚ` is **not surjective**: `1/2` is not an integer. If `n = 1/2` in
`ℚ`, then `2n = 1` in `ℚ`, hence in `ℤ`, which is impossible for an integer `n`. So in the
category of rings, epimorphisms need not be surjective. -/
theorem int_cast_not_surjective : ¬ Function.Surjective (Int.cast : ℤ → ℚ) := by
  intro hsurj
  obtain ⟨n, hn⟩ := hsurj (1 / 2)
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hn]
    norm_num
  have h3 : 2 * n = 1 := by exact_mod_cast h2
  omega
-- @endregion

/-! ### Duality -/

-- @region categories.mono_iff_epi_op
-- @provenance independent
/-- **Duality.** A morphism `f : X ⟶ Y` of `C` is a monomorphism exactly when the corresponding
morphism `f.op : Y ⟶ X` of the opposite category `Cᵒᵖ` is an epimorphism. Composition in `Cᵒᵖ`
is composition in `C` reversed (`(g ≫ f).op = f.op ≫ g.op`), so "cancellable on the left" in
`C` is literally "cancellable on the right" in `Cᵒᵖ`. -/
theorem mono_iff_epi_op {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Epi f.op := by
  constructor
  · intro hf
    constructor
    intro Z g h hgh
    -- `f.op ≫ g = (g.unop ≫ f).op`
    apply Quiver.Hom.unop_inj
    apply hf.right_cancellation
    exact Quiver.Hom.op_inj (by simp at hgh ⊢; exact hgh)
  · intro hf
    constructor
    intro Z g h hgh
    apply Quiver.Hom.op_inj
    apply hf.left_cancellation
    simpa using congrArg Quiver.Hom.op hgh
-- @endregion

-- @region categories.mono_comp
-- @provenance independent
/-- **A composite of monomorphisms is a monomorphism.** If `f : X ⟶ Y` and `g : Y ⟶ Z` are
monomorphisms and `a ≫ (f ≫ g) = b ≫ (f ≫ g)`, then `(a ≫ f) ≫ g = (b ≫ f) ≫ g`, so cancelling
`g` gives `a ≫ f = b ≫ f`, and cancelling `f` gives `a = b`. By duality (reverse every arrow)
the same proof shows that a composite of epimorphisms is an epimorphism. -/
theorem mono_comp {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  constructor
  intro W a b hab
  have h1 : (a ≫ f) ≫ g = (b ≫ f) ≫ g := by
    rw [Category.assoc, Category.assoc]
    exact hab
  have h2 : a ≫ f = b ≫ f := hg.right_cancellation _ _ h1
  exact hf.right_cancellation _ _ h2
-- @endregion

-- @region categories.epi_comp_library
-- @provenance library
/-- The dual statement, as Mathlib states it: a composite of epimorphisms is an epimorphism.
This applies the instance `CategoryTheory.epi_comp`. -/
theorem epi_comp_library {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Epi f] [Epi g] : Epi (f ≫ g) :=
  epi_comp f g
-- @endregion

-- @region categories.op_epi_iff_library
-- @provenance library
/-- Mathlib's version of the same duality, `CategoryTheory.op_epi_iff`. -/
theorem op_epi_iff_library {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Epi f.op ↔ Mono f :=
  CategoryTheory.op_epi_iff f
-- @endregion

end Lumenary.Categories
