/-
The Lumenary — formal mathematics
Monoidal categories: the pentagon and triangle axioms, Kelly's identity `λ_I = ρ_I`, the
commutativity of `End(I)`, the Eckmann–Hilton argument, coherence, symmetric braidings,
monoid objects, and a twisted associator on graded vector spaces.

What is proved here. Independently: the Eckmann–Hilton argument for two unital operations on a
type; the commutativity of the endomorphism monoid of the unit object in *any* monoidal category
(the human proof, step by step, from the interchange law and naturality of the unitors); that the
braiding of the cartesian monoidal category of types squares to the identity; and, by finite
computation, that the "carry" cochain on `ℤ/3` satisfies the 3-cocycle (pentagon) condition while
a naive guess does not.

What Mathlib provides. `MonoidalCategory` (with the pentagon and triangle axioms as fields),
Kelly's `unitors_equal`, Mac Lane's coherence theorem for the free monoidal category
(`FreeMonoidalCategory.subsingleton_hom`), the cartesian monoidal structure on types,
`Mon (Type u) ≌ MonCat` (monoid objects in `(Type, ×)` are monoids), and
`Monad.monadMonEquiv` (monads are monoids in endofunctors). We cite these as library results.
Not formalised: the strictification theorem, braided-but-not-symmetric examples, and the
identification of monoid objects in `(Ab, ⊗)` with rings.
-/
import Mathlib.CategoryTheory.Monad.EquivMon
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic

namespace Lumenary.MonoidalCategories

open CategoryTheory MonoidalCategory

universe u v

/-! ### The axioms, and Kelly's identity -/

section Axioms

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

-- @region monoidal_categories.pentagon
-- @provenance library
/-- **The pentagon axiom.** The two ways of rebracketing `((W ⊗ X) ⊗ Y) ⊗ Z` into
`W ⊗ (X ⊗ (Y ⊗ Z))` using associators agree. In Mathlib this is a field of `MonoidalCategory`
(composition is written `≫`, in diagrammatic order, and `f ▷ Z`, `W ◁ g` are whiskerings). -/
theorem pentagon (W X Y Z : C) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom :=
  MonoidalCategory.pentagon W X Y Z
-- @endregion

-- @region monoidal_categories.triangle
-- @provenance library
/-- **The triangle axiom**: `(X ⊗ I) ⊗ Y ⟶ X ⊗ (I ⊗ Y) ⟶ X ⊗ Y` equals `ρ_X ⊗ Y`.
A field of Mathlib's `MonoidalCategory`. -/
theorem triangle (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y :=
  MonoidalCategory.triangle X Y
-- @endregion

-- @region monoidal_categories.unitors_equal
-- @provenance library
/-- **Kelly's identity** `λ_I = ρ_I : I ⊗ I ⟶ I`. It is *not* an axiom: it follows from the
pentagon and triangle axioms (Kelly 1964). Mathlib's `unitors_equal`. -/
theorem unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
  CategoryTheory.MonoidalCategory.unitors_equal
-- @endregion

-- @region monoidal_categories.end_unit_comm
-- @provenance independent
/-- **The endomorphisms of the unit object commute.** For `f g : I ⟶ I`, `f ≫ g = g ≫ f`.

Human proof. Write `u = λ_I = ρ_I : I ⊗ I ≅ I` (Kelly's identity). Naturality of the unitors says
`I ◁ g` is `g` conjugated by `u`, and `f ▷ I` is `f` conjugated by `u`. The interchange law says
`I ◁ g` and `f ▷ I` commute (both orders equal `f ⊗ g`). Conjugating back by `u`, `g` and `f`
commute. -/
theorem end_unit_comm (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  -- naturality of the unitors at `g` and at `f`
  have hl : 𝟙_ C ◁ g ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ g :=
    MonoidalCategory.leftUnitor_naturality g
  have hr : f ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ f := by
    rw [unitors_equal]
    exact MonoidalCategory.rightUnitor_naturality f
  -- the interchange law: `I ◁ g ≫ f ▷ I = f ▷ I ≫ I ◁ g`
  have hx : 𝟙_ C ◁ g ≫ f ▷ 𝟙_ C = f ▷ 𝟙_ C ≫ 𝟙_ C ◁ g := whisker_exchange f g
  -- conjugate back by the isomorphism `λ_I`
  have key : (λ_ (𝟙_ C)).hom ≫ g ≫ f = (λ_ (𝟙_ C)).hom ≫ f ≫ g := by
    calc (λ_ (𝟙_ C)).hom ≫ g ≫ f = (𝟙_ C ◁ g ≫ (λ_ (𝟙_ C)).hom) ≫ f := by
          rw [hl, Category.assoc]
      _ = 𝟙_ C ◁ g ≫ (f ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom) := by rw [Category.assoc, hr]
      _ = (𝟙_ C ◁ g ≫ f ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom := by rw [Category.assoc]
      _ = (f ▷ 𝟙_ C ≫ 𝟙_ C ◁ g) ≫ (λ_ (𝟙_ C)).hom := by rw [hx]
      _ = f ▷ 𝟙_ C ≫ ((λ_ (𝟙_ C)).hom ≫ g) := by rw [Category.assoc, hl]
      _ = (λ_ (𝟙_ C)).hom ≫ f ≫ g := by rw [← Category.assoc, hr, Category.assoc]
  exact ((cancel_epi (λ_ (𝟙_ C)).hom).mp key).symm
-- @endregion

end Axioms

/-! ### Eckmann–Hilton -/

-- @region monoidal_categories.eckmann_hilton
-- @provenance independent
/-- **The Eckmann–Hilton argument.** Suppose a type carries two binary operations `m₁`, `m₂`
with units `e₁`, `e₂`, satisfying the interchange law
`m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)`. Then the units agree, the operations agree, and
the operation is commutative. (Mathlib: `EckmannHilton.one`, `EckmannHilton.mul`,
`EckmannHilton.mul_comm`.)

Proof. Interchange with `(a, b, c, d) = (e₂, e₁, e₁, e₂)` gives `e₁ = e₂ =: e`. Then
`m₁ a b = m₁ (m₂ a e) (m₂ e b) = m₂ (m₁ a e) (m₁ e b) = m₂ a b`, and
`m₁ a b = m₁ (m₂ e a) (m₂ b e) = m₂ (m₁ e b) (m₁ a e) = m₂ b a = m₁ b a`. -/
theorem eckmann_hilton {X : Type u} (m₁ m₂ : X → X → X) (e₁ e₂ : X)
    (h₁l : ∀ x, m₁ e₁ x = x) (h₁r : ∀ x, m₁ x e₁ = x)
    (h₂l : ∀ x, m₂ e₂ x = x) (h₂r : ∀ x, m₂ x e₂ = x)
    (interchange : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    e₁ = e₂ ∧ m₁ = m₂ ∧ ∀ a b, m₁ a b = m₁ b a := by
  have units : e₁ = e₂ := by
    have h := interchange e₂ e₁ e₁ e₂
    rw [h₂l, h₂r, h₁l, h₁r, h₁l, h₂l] at h
    exact h
  subst units
  have same : m₁ = m₂ := by
    funext a b
    calc m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by rw [h₂r, h₂l]
      _ = m₂ (m₁ a e₁) (m₁ e₁ b) := interchange a e₁ e₁ b
      _ = m₂ a b := by rw [h₁r, h₁l]
  refine ⟨rfl, same, fun a b => ?_⟩
  calc m₁ a b = m₁ (m₂ e₁ a) (m₂ b e₁) := by rw [h₂l, h₂r]
    _ = m₂ (m₁ e₁ b) (m₁ a e₁) := interchange e₁ a b e₁
    _ = m₂ b a := by rw [h₁l, h₁r]
    _ = m₁ b a := by rw [same]
-- @endregion

/-! ### Coherence -/

-- @region monoidal_categories.coherence
-- @provenance library
/-- **Mac Lane's coherence theorem**, in Mathlib's form: in the free monoidal category on a type
`C` (objects are formal bracketed words in `C` and `I`, morphisms are built from associators,
unitors and identities), any two parallel morphisms are equal.
Mathlib's `FreeMonoidalCategory.subsingleton_hom`. -/
theorem coherence (C : Type u) (X Y : FreeMonoidalCategory C) (f g : X ⟶ Y) : f = g :=
  Subsingleton.elim f g
-- @endregion

/-! ### The cartesian monoidal category of types -/

-- @region monoidal_categories.types_symmetric
-- @provenance independent
/-- **`(Type, ×, PUnit)` is symmetric.** The braiding `X × Y ≅ Y × X` swaps the coordinates, so
braiding twice is the identity. Checked on elements: `(x, y) ↦ (y, x) ↦ (x, y)`. -/
theorem types_symmetric (X Y : Type u) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by
  ext ⟨x, y⟩ <;> rfl
-- @endregion

-- @region monoidal_categories.monoid_objects_in_types
-- @provenance library
/-- **Monoid objects in `(Type, ×, PUnit)` are monoids.** The category of monoid objects is
equivalent to the category of monoids (Mathlib's `Mon.monTypeEquivalenceMon`). -/
theorem monoid_objects_in_types : Nonempty (Mon (Type u) ≌ MonCat.{u}) :=
  ⟨monTypeEquivalenceMon⟩
-- @endregion

attribute [local instance] endofunctorMonoidalCategory

-- @region monoidal_categories.monads_are_monoids
-- @provenance library
/-- **Monads are monoid objects in the strict monoidal category `(C ⥤ C, ∘, 𝟭)`**
(Mathlib's `Monad.monadMonEquiv`). -/
theorem monads_are_monoids (C : Type u) [Category.{v} C] :
    Nonempty (Monad C ≌ Mon (C ⥤ C)) :=
  ⟨Monad.monadMonEquiv C⟩
-- @endregion

/-! ### A twisted associator: the pentagon becomes a cocycle condition -/

-- @region monoidal_categories.carry_cocycle
-- @provenance definition
/-- The **carry cochain** on `ℤ/3` with parameter `p`: `ω(a, b, c) = p · a · carry(b, c)` in
`ℤ/3`, where `carry(b, c) = 1` if `b + c` wraps around (as integers `b + c ≥ 3`) and `0`
otherwise. Read `ω(a, b, c)` as the exponent of the cube root of unity `ζ = e^{2πi/3}` that
the associator `(δ_a ⊗ δ_b) ⊗ δ_c ⟶ δ_a ⊗ (δ_b ⊗ δ_c)` multiplies by, in the category of
`ℤ/3`-graded vector spaces. -/
def carryCochain (p : Fin 3) (a b c : Fin 3) : Fin 3 :=
  p * a * (if 3 ≤ b.val + c.val then 1 else 0)
-- @endregion

-- @region monoidal_categories.carry_pentagon
-- @provenance independent
/-- **The pentagon holds for the twisted associator.** For simple objects the pentagon axiom of
`Vec_{ℤ/3}^ω` says exactly that `ω` is a 3-cocycle:
`ω(b,c,d) + ω(a,b+c,d) + ω(a,b,c) = ω(a+b,c,d) + ω(a,b,c+d)` (exponents of `ζ`, added in `ℤ/3`).
We check it for all `3 · 3⁴ = 243` cases by computation (`decide`). The lesson gives the general
proof for `ℤ/n`. -/
theorem carry_pentagon : ∀ p a b c d : Fin 3,
    carryCochain p b c d + carryCochain p a (b + c) d + carryCochain p a b c =
      carryCochain p (a + b) c d + carryCochain p a b (c + d) := by
  decide
-- @endregion

-- @region monoidal_categories.naive_not_cocycle
-- @provenance independent
/-- **A naive associator fails the pentagon.** Twisting by the carry of the *first* two indices,
`ω'(a, b, c) = carry(a, b)`, does *not* satisfy the cocycle condition:
`(a, b, c, d) = (1, 2, 0, 0)` is a counterexample (the two sides are `2` and `1` in `ℤ/3`).
Checked by computation. -/
theorem naive_not_cocycle :
    let ω' : Fin 3 → Fin 3 → Fin 3 → Fin 3 := fun a b _ => if 3 ≤ a.val + b.val then 1 else 0
    ¬ ∀ a b c d : Fin 3,
      ω' b c d + ω' a (b + c) d + ω' a b c = ω' (a + b) c d + ω' a b (c + d) := by
  decide
-- @endregion

end Lumenary.MonoidalCategories
