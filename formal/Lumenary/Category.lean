/-
The Lumenary — formal mathematics
Category: a first, minimal look at categories (a preview for the category-theory Wonder Trails).

* `Category`: objects, morphisms, identities, composition and the three laws.
* `typesCategory`: Lean types and functions form a category.
* `Monoid'`, `Group'`: monoids and groups as plain structures; `Int` with `+` is a group,
  `Int` with `×` is only a monoid; a monoid is a category with one object.
* The universal property of the product `A × B` in the category of types.

Mathlib analogue: `CategoryTheory.Category`, `CategoryTheory.types`, `Monoid`, `Group`,
`CategoryTheory.Limits.prod.lift`. Our versions are deliberately tiny and were not checked
against Mathlib; Mathlib's definitions carry more structure (notation, universes, simp sets).
-/
import Lumenary.Integers

namespace Lumenary.Category

universe u v w

-- @region category.category
-- @provenance definition
/-- A **category** has objects, and for any two objects `X` and `Y` a type `Hom X Y` of
morphisms (arrows) from `X` to `Y`, together with
* an identity arrow `id X : Hom X X` for every object, and
* composition: from `f : Hom X Y` and `g : Hom Y Z` we get `comp f g : Hom X Z`,
such that identities do nothing (`id_comp`, `comp_id`) and composition is associative.

**Order of composition:** `comp f g` means "first `f`, then `g`" (diagrammatic order).
Mathlib uses the same order and writes it `f ≫ g`; ordinary function composition `g ∘ f`
lists the same two steps the other way round. -/
class Category.{v₁, u₁} (Obj : Type u₁) : Type (max u₁ (v₁ + 1)) where
  /-- The arrows from `X` to `Y`. -/
  Hom : Obj → Obj → Type v₁
  /-- The identity arrow on `X`. -/
  id : (X : Obj) → Hom X X
  /-- `comp f g`: first `f`, then `g`. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Doing nothing first changes nothing. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Doing nothing afterwards changes nothing. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- Composing three arrows does not depend on the bracketing. -/
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)
-- @endregion

-- @region category.types_category
-- @provenance definition
/-- **Types and functions form a category.** Objects are Lean types (in universe `u`),
arrows `X → Y` are functions, and `comp f g` is `g ∘ f` (first `f`, then `g`).
All three laws hold by `rfl` (see `Lumenary.Composition.comp_assoc` for why).

This is the category of Lean *types*, the type-theoretic analogue of the category **Set**
of sets and functions used in set-theoretic mathematics; Lean types are not ZFC sets, but
they play the same role here. (Mathlib analogue: `CategoryTheory.types`.) -/
instance typesCategory : Category.{u, u + 1} (Type u) where
  Hom X Y := X → Y
  id _ := fun x => x
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
-- @endregion

/-! ### Monoids and groups -/

-- @region category.monoid
-- @provenance definition
/-- A **monoid**: a set `M` with an associative operation `mul` and a two-sided identity `one`.
We bundle the operation as data (a structure, not a class) so that one type can carry
several monoid structures, e.g. `Int` with `+` and `Int` with `×`.
(Mathlib analogue: the class `Monoid`, which writes `mul` as `*` and `one` as `1`.) -/
structure Monoid' (M : Type u) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a
-- @endregion

-- @region category.group
-- @provenance definition
/-- A **group**: a monoid in which every element `a` has an inverse `inv a` with
`mul (inv a) a = one`. Together with the monoid laws this one-sided law already implies
`mul a (inv a) = one` (proved below as `Group'.mul_inv_cancel`); Mathlib's `Group` uses the
same axiom, `inv_mul_cancel`. -/
structure Group' (G : Type u) extends Monoid' G where
  inv : G → G
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
-- @endregion

-- @region category.group_mul_inv_cancel
-- @provenance independent
/-- A left inverse is also a right inverse: `a · a⁻¹ = 1`.
Write `b` for `a⁻¹` and `c` for `b⁻¹`. Then
`a·b = 1·(a·b) = (c·b)·(a·b) = c·(b·(a·b)) = c·((b·a)·b) = c·(1·b) = c·b = 1`. -/
theorem Group'.mul_inv_cancel {G : Type u} (g : Group' G) (a : G) :
    g.mul a (g.inv a) = g.one := by
  generalize hb : g.inv a = b
  have hba : g.mul b a = g.one := by
    rw [← hb]
    exact g.inv_mul_cancel a
  have hcb : g.mul (g.inv b) b = g.one := g.inv_mul_cancel b
  calc g.mul a b
      = g.mul g.one (g.mul a b) := (g.one_mul _).symm
    _ = g.mul (g.mul (g.inv b) b) (g.mul a b) := by rw [hcb]
    _ = g.mul (g.inv b) (g.mul b (g.mul a b)) := g.mul_assoc _ _ _
    _ = g.mul (g.inv b) (g.mul (g.mul b a) b) := by rw [g.mul_assoc b a b]
    _ = g.mul (g.inv b) (g.mul g.one b) := by rw [hba]
    _ = g.mul (g.inv b) b := by rw [g.one_mul b]
    _ = g.one := hcb
-- @endregion

-- @region category.int_add
-- @provenance definition
/-- The integers under addition form a group: the operation is `+`, the identity is `0`,
and the inverse of `a` is `-a`. (We still call the operation `mul`; Mathlib instead has a
separate `AddGroup` with additive notation.) -/
def intAdd : Group' Int where
  mul a b := a + b
  one := 0
  inv a := -a
  mul_assoc := Int.add_assoc
  one_mul := Int.zero_add
  mul_one := Int.add_zero
  inv_mul_cancel := Int.add_left_neg
-- @endregion

-- @region category.int_mul
-- @provenance definition
/-- The integers under multiplication form a monoid with identity `1`. -/
def intMul : Monoid' Int where
  mul a b := a * b
  one := 1
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
-- @endregion

-- @region category.int_mul_not_group
-- @provenance independent
/-- …but the integers under multiplication are **not** a group: not every integer has a
multiplicative inverse. Indeed `2 · b = 1` has no integer solution
(`Lumenary.Integers.no_int_half`). -/
theorem int_mul_not_group : ¬ ∀ a : Int, ∃ b, a * b = 1 := by
  intro h
  obtain ⟨b, hb⟩ := h 2        -- `hb : 2 * b = 1`
  exact Lumenary.Integers.no_int_half ⟨b, hb⟩
-- @endregion

-- @region category.monoid_as_category
-- @provenance definition
/-- **A monoid is a category with one object.** Take a single object (the only element of
`Unit`); its arrows are the elements of `M`; composing arrows is multiplying; the identity
arrow is `one`. The category laws are exactly the monoid laws.
(Declared with `abbrev` so that Lean can unfold it when it is used as an instance.) -/
abbrev monoidAsCategory {M : Type u} (m : Monoid' M) : Category.{u, 0} Unit where
  Hom _ _ := M
  id _ := m.one
  comp f g := m.mul f g
  id_comp f := m.one_mul f
  comp_id f := m.mul_one f
  assoc f g h := m.mul_assoc f g h
-- @endregion

/-! ### Products in the category of types -/

variable {Z : Type u} {A : Type v} {B : Type w}

-- @region category.pair
-- @provenance definition
/-- Given `f : Z → A` and `g : Z → B`, `pair f g : Z → A × B` sends `z` to `(f z, g z)`. -/
def pair (f : Z → A) (g : Z → B) : Z → A × B := fun z => (f z, g z)
-- @endregion

-- @region category.fst_comp_pair
-- @provenance independent
/-- Following `pair f g` by the first projection gives back `f`. -/
theorem fst_comp_pair (f : Z → A) (g : Z → B) : Prod.fst ∘ pair f g = f := rfl
-- @endregion

-- @region category.snd_comp_pair
-- @provenance independent
/-- Following `pair f g` by the second projection gives back `g`. -/
theorem snd_comp_pair (f : Z → A) (g : Z → B) : Prod.snd ∘ pair f g = g := rfl
-- @endregion

-- @region category.pair_unique
-- @provenance independent
/-- **Universal property of the product, uniqueness half.** Any `h : Z → A × B` whose two
coordinates are `f` and `g` *is* `pair f g`. Together with `fst_comp_pair` and
`snd_comp_pair` (existence), this says: maps into `A × B` are the same thing as pairs of
maps into `A` and into `B`. -/
theorem pair_unique {f : Z → A} {g : Z → B} (h : Z → A × B)
    (hf : Prod.fst ∘ h = f) (hg : Prod.snd ∘ h = g) : h = pair f g := by
  funext z
  show h z = (f z, g z)
  rw [← hf, ← hg]
  -- The goal is now `h z = ((h z).1, (h z).2)`: every pair is built from its coordinates.
  rfl
-- @endregion

end Lumenary.Category
