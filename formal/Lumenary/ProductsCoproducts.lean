/-
The Lumenary — formal mathematics
Products, coproducts, initial and terminal objects.

What is proved here. We state the universal property of a binary product by hand
(`IsBinaryProduct`), in any Mathlib category, and prove the lesson's central theorem: two
products of the same pair are isomorphic by a *unique* isomorphism compatible with the
projections. We construct products in the category of types (pairs) and in a meet-semilattice
regarded as a category (meets), and prove conversely that in a partial order every product is the
meet. Coproducts are *defined* as products in the opposite category, exactly as in the lesson;
unpacking that definition gives the familiar "copairing" map, and disjoint unions (`Sum`) are
coproducts of types. Terminal objects are unique up to unique isomorphism. Finally, using only the
universal property of the free product of groups, we prove that `ℤ ∗ ℤ` is not commutative, while
`ℤ × ℤ` is.

What Mathlib provides. `CategoryTheory.Limits.BinaryFan`, `prod.lift`, `HasBinaryProducts`,
`IsTerminal`, `IsInitial`, `Types.isTerminalPUnit`, `Types.isInitialPEmpty`,
`CommRingCat.zIsInitial`, `GrpCat.isZero_of_subsingleton`, `Cone.isLimitEquivIsTerminal`, and the
coproduct of monoids and groups `Monoid.Coprod` (`M ∗ N`) with `Monoid.Coprod.lift`. Our
`IsBinaryProduct` is a teaching version of Mathlib's `IsLimit (BinaryFan.mk π₁ π₂)`;
`ofHasBinaryProduct` shows that Mathlib's chosen products satisfy it.
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.Perm.Fin

namespace Lumenary.ProductsCoproducts

open CategoryTheory Limits Opposite Monoid.Coprod

universe v u

/-! ### The universal property of a product -/

section General

variable {C : Type u} [Category.{v} C]

-- @region products_coproducts.is_binary_product
-- @provenance definition
/-- **The universal property of a product.** Projections `π₁ : P ⟶ A` and `π₂ : P ⟶ B` make `P`
a product of `A` and `B` when every pair `f : X ⟶ A`, `g : X ⟶ B` factors through `P` by exactly
one morphism `lift f g : X ⟶ P`. Mathlib composes in diagrammatic order: `h ≫ π₁` means
"first `h`, then `π₁`", i.e. `π₁ ∘ h`. -/
structure IsBinaryProduct {A B P : C} (π₁ : P ⟶ A) (π₂ : P ⟶ B) where
  /-- The induced morphism `⟨f, g⟩ : X ⟶ P`. -/
  lift : ∀ {X : C}, (X ⟶ A) → (X ⟶ B) → (X ⟶ P)
  /-- `π₁ ∘ ⟨f, g⟩ = f`. -/
  lift_fst : ∀ {X : C} (f : X ⟶ A) (g : X ⟶ B), lift f g ≫ π₁ = f
  /-- `π₂ ∘ ⟨f, g⟩ = g`. -/
  lift_snd : ∀ {X : C} (f : X ⟶ A) (g : X ⟶ B), lift f g ≫ π₂ = g
  /-- Uniqueness: any `h` with `π₁ ∘ h = f` and `π₂ ∘ h = g` is `⟨f, g⟩`. -/
  uniq : ∀ {X : C} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ P), h ≫ π₁ = f → h ≫ π₂ = g → h = lift f g
-- @endregion

namespace IsBinaryProduct

variable {A B P Q : C} {π₁ : P ⟶ A} {π₂ : P ⟶ B} {ρ₁ : Q ⟶ A} {ρ₂ : Q ⟶ B}

-- @region products_coproducts.is_binary_product.hom_ext
-- @provenance independent
/-- **Morphisms into a product are determined by their components.** If `h` and `k` agree after
both projections, both equal `lift (h ≫ π₁) (h ≫ π₂)` by the uniqueness clause. -/
theorem hom_ext (hP : IsBinaryProduct π₁ π₂) {X : C} {h k : X ⟶ P} (h₁ : h ≫ π₁ = k ≫ π₁)
    (h₂ : h ≫ π₂ = k ≫ π₂) : h = k := by
  rw [hP.uniq _ _ h rfl rfl, hP.uniq _ _ k h₁.symm h₂.symm]
-- @endregion

-- @region products_coproducts.is_binary_product.iso
-- @provenance definition
/-- **Two products are isomorphic.** The comparison maps are `⟨π₁, π₂⟩ : P ⟶ Q` and
`⟨ρ₁, ρ₂⟩ : Q ⟶ P`. Each composite commutes with the projections, so by `hom_ext` it is the
identity — the proof in the lesson, verbatim. -/
def iso (hP : IsBinaryProduct π₁ π₂) (hQ : IsBinaryProduct ρ₁ ρ₂) : P ≅ Q where
  hom := hQ.lift π₁ π₂
  inv := hP.lift ρ₁ ρ₂
  hom_inv_id := hP.hom_ext (by rw [Category.assoc, hP.lift_fst, hQ.lift_fst, Category.id_comp])
    (by rw [Category.assoc, hP.lift_snd, hQ.lift_snd, Category.id_comp])
  inv_hom_id := hQ.hom_ext (by rw [Category.assoc, hQ.lift_fst, hP.lift_fst, Category.id_comp])
    (by rw [Category.assoc, hQ.lift_snd, hP.lift_snd, Category.id_comp])
-- @endregion

-- @region products_coproducts.is_binary_product.iso_unique
-- @provenance independent
/-- **…by a unique isomorphism compatible with the projections.** Any isomorphism `i : P ≅ Q`
with `ρ₁ ∘ i = π₁` and `ρ₂ ∘ i = π₂` is the comparison isomorphism `iso hP hQ`: its forward map
satisfies the defining equations of `lift π₁ π₂`, so uniqueness in `Q`'s universal property
identifies them (and an isomorphism is determined by its forward map). -/
theorem iso_unique (hP : IsBinaryProduct π₁ π₂) (hQ : IsBinaryProduct ρ₁ ρ₂) (i : P ≅ Q)
    (h₁ : i.hom ≫ ρ₁ = π₁) (h₂ : i.hom ≫ ρ₂ = π₂) : i = iso hP hQ := by
  ext
  exact hQ.uniq π₁ π₂ i.hom h₁ h₂
-- @endregion

end IsBinaryProduct

-- @region products_coproducts.of_has_binary_product
-- @provenance definition
/-- **Mathlib's products satisfy our universal property.** When `A` and `B` have a (chosen)
product `A ⨯ B` in Mathlib, its projections `prod.fst`, `prod.snd` form an `IsBinaryProduct`;
the induced map is Mathlib's `prod.lift`, and uniqueness is `prod.hom_ext`. -/
noncomputable def ofHasBinaryProduct (A B : C) [HasBinaryProduct A B] :
    IsBinaryProduct (prod.fst : A ⨯ B ⟶ A) prod.snd where
  lift f g := prod.lift f g
  lift_fst f g := prod.lift_fst f g
  lift_snd f g := prod.lift_snd f g
  uniq f g h h₁ h₂ := prod.hom_ext (by rw [h₁, prod.lift_fst]) (by rw [h₂, prod.lift_snd])
-- @endregion

-- @region products_coproducts.product_is_terminal_cone
-- @provenance library
/-- **A product is a terminal cone.** A cone over the pair `(A, B)` is an object with two maps to
`A` and `B` (a `BinaryFan`); cones and their morphisms form a category, and a cone is a limit —
here, a product — exactly when it is a terminal object of that category. This applies Mathlib's
`Cone.isLimitEquivIsTerminal`. -/
theorem product_is_terminal_cone {A B : C} (c : BinaryFan A B) :
    Nonempty (IsLimit c) ↔ Nonempty (IsTerminal c) :=
  ⟨fun ⟨h⟩ => ⟨Cone.isLimitEquivIsTerminal c h⟩,
    fun ⟨h⟩ => ⟨(Cone.isLimitEquivIsTerminal c).symm h⟩⟩
-- @endregion

/-! ### Coproducts are products in the opposite category -/

-- @region products_coproducts.is_binary_coproduct
-- @provenance definition
/-- **A coproduct in `C` is a product in `Cᵒᵖ`.** Injections `ι₁ : A ⟶ S`, `ι₂ : B ⟶ S` make
`S` a coproduct of `A` and `B` when the reversed arrows `ι₁.op : op S ⟶ op A`,
`ι₂.op : op S ⟶ op B` make `op S` a product of `op A` and `op B` in the opposite category.
This *is* the definition — duality is built in. -/
abbrev IsBinaryCoproduct {A B S : C} (ι₁ : A ⟶ S) (ι₂ : B ⟶ S) : Type _ :=
  IsBinaryProduct ι₁.op ι₂.op
-- @endregion

namespace IsBinaryCoproduct

variable {A B S : C} {ι₁ : A ⟶ S} {ι₂ : B ⟶ S}

-- @region products_coproducts.is_binary_coproduct.desc
-- @provenance definition
/-- **Unpacking the dual definition: copairing.** Maps `f : A ⟶ Y` and `g : B ⟶ Y` in `C` are
maps `op Y ⟶ op A` and `op Y ⟶ op B` in `Cᵒᵖ`; the product property gives `op Y ⟶ op S`, i.e. a
map `[f, g] : S ⟶ Y` in `C`. -/
def desc (hS : IsBinaryCoproduct ι₁ ι₂) {Y : C} (f : A ⟶ Y) (g : B ⟶ Y) : S ⟶ Y :=
  (hS.lift f.op g.op).unop
-- @endregion

-- @region products_coproducts.is_binary_coproduct.inl_desc
-- @provenance independent
/-- **The copairing restricts correctly:** `[f, g] ∘ ι₁ = f` and `[f, g] ∘ ι₂ = g`. These are the
product equations in `Cᵒᵖ`, read backwards (`unop` of `lift f.op g.op ≫ ι₁.op = f.op`). -/
theorem inl_desc (hS : IsBinaryCoproduct ι₁ ι₂) {Y : C} (f : A ⟶ Y) (g : B ⟶ Y) :
    ι₁ ≫ hS.desc f g = f ∧ ι₂ ≫ hS.desc f g = g :=
  ⟨congrArg Quiver.Hom.unop (hS.lift_fst f.op g.op),
    congrArg Quiver.Hom.unop (hS.lift_snd f.op g.op)⟩
-- @endregion

-- @region products_coproducts.is_binary_coproduct.desc_unique
-- @provenance independent
/-- **…and uniquely:** any `h : S ⟶ Y` with `h ∘ ι₁ = f` and `h ∘ ι₂ = g` is `[f, g]`. This is
the uniqueness clause in `Cᵒᵖ`, applied to `h.op`. -/
theorem desc_unique (hS : IsBinaryCoproduct ι₁ ι₂) {Y : C} (f : A ⟶ Y) (g : B ⟶ Y) (h : S ⟶ Y)
    (h₁ : ι₁ ≫ h = f) (h₂ : ι₂ ≫ h = g) : h = hS.desc f g :=
  congrArg Quiver.Hom.unop
    (hS.uniq f.op g.op h.op (congrArg Quiver.Hom.op h₁) (congrArg Quiver.Hom.op h₂))
-- @endregion

end IsBinaryCoproduct

/-! ### Terminal objects are unique -/

-- @region products_coproducts.terminal_unique
-- @provenance independent
/-- **Terminal objects are unique up to unique isomorphism.** If `T` and `T'` are terminal, the
unique maps `T ⟶ T'` and `T' ⟶ T` compose to endomorphisms of a terminal object, which must be
identities because a terminal object has only one endomorphism. (Mathlib: `IsTerminal.uniqueUpToIso`.)
Dually for initial objects. -/
theorem terminal_unique {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') :
    ∃ i : T ≅ T', ∀ j : T ≅ T', j = i :=
  ⟨⟨hT'.from T, hT.from T', hT.hom_ext _ _, hT'.hom_ext _ _⟩,
    fun _ => Iso.ext (hT'.hom_ext _ _)⟩
-- @endregion

end General

/-! ### Products and coproducts of types -/

-- @region products_coproducts.types_product
-- @provenance definition
/-- **In the category of types, the product is the type of pairs.** Given `f : X → A` and
`g : X → B`, the unique map `X → A × B` compatible with the projections is
`x ↦ (f x, g x)`: any compatible `h` has first and second coordinates `f x` and `g x`. -/
def typesProduct (A B : Type u) :
    IsBinaryProduct (C := Type u) (↾(Prod.fst : A × B → A)) (↾(Prod.snd : A × B → B)) where
  lift f g := ↾fun x => (f x, g x)
  lift_fst _ _ := rfl
  lift_snd _ _ := rfl
  uniq f g h h₁ h₂ := by
    -- `ext` reduces to the two coordinates of `h x`.
    ext x
    · simpa using ConcreteCategory.congr_hom h₁ x
    · simpa using ConcreteCategory.congr_hom h₂ x
-- @endregion

-- @region products_coproducts.types_coproduct
-- @provenance definition
/-- **In the category of types, the coproduct is the disjoint union** `A ⊕ B`, with the
injections `Sum.inl`, `Sum.inr`. Following the definition, we exhibit a product in `(Type u)ᵒᵖ`:
the induced map is "case analysis" `Sum.elim f g`, and it is unique because a function on
`A ⊕ B` is determined by its values on the two summands. -/
def typesCoproduct (A B : Type u) :
    IsBinaryCoproduct (C := Type u) (↾(Sum.inl : A → A ⊕ B)) (↾(Sum.inr : B → A ⊕ B)) where
  lift f g := (↾(Sum.elim f.unop g.unop)).op
  lift_fst _ _ := rfl
  lift_snd _ _ := rfl
  uniq f g h h₁ h₂ := by
    apply Quiver.Hom.unop_inj
    ext x
    rcases x with a | b
    · exact ConcreteCategory.congr_hom (congrArg Quiver.Hom.unop h₁) a
    · exact ConcreteCategory.congr_hom (congrArg Quiver.Hom.unop h₂) b
-- @endregion

-- @region products_coproducts.types_terminal
-- @provenance library
/-- **In the category of types, a one-element type is terminal and the empty type is initial.**
Every type has exactly one map to `PUnit` and exactly one map from `PEmpty`. These are Mathlib's
`Types.isTerminalPUnit` and `Types.isInitialPEmpty`. -/
theorem types_terminal_initial :
    Nonempty (IsTerminal (PUnit : Type u)) ∧ Nonempty (IsInitial (PEmpty : Type u)) :=
  ⟨⟨Types.isTerminalPUnit⟩, ⟨Types.isInitialPEmpty⟩⟩
-- @endregion

/-! ### Products and coproducts in a poset: meets and joins -/

section Order

variable {α : Type u}

-- @region products_coproducts.inf_is_product
-- @provenance definition
/-- **In a poset regarded as a category, the product is the meet.** There is a morphism `x ⟶ y`
exactly when `x ≤ y`, and then only one, so the equations in the universal property are
automatic; what remains is existence: `x ≤ a` and `x ≤ b` imply `x ≤ a ⊓ b`. -/
def infIsProduct [SemilatticeInf α] (a b : α) :
    IsBinaryProduct (homOfLE (inf_le_left : a ⊓ b ≤ a)) (homOfLE inf_le_right) where
  lift f g := homOfLE (le_inf (leOfHom f) (leOfHom g))
  lift_fst _ _ := Subsingleton.elim _ _
  lift_snd _ _ := Subsingleton.elim _ _
  uniq _ _ _ _ _ := Subsingleton.elim _ _
-- @endregion

-- @region products_coproducts.product_eq_inf
-- @provenance independent
/-- **Conversely, every product in a poset is the meet.** If `p` (with `p ≤ a`, `p ≤ b`) is a
product of `a` and `b`, then `p ≤ a ⊓ b` because `a ⊓ b` is a lower bound, and `a ⊓ b ≤ p` by
the universal property applied to the cone `a ⊓ b`. Antisymmetry gives `p = a ⊓ b`. So a pair
with no greatest lower bound has no product. -/
theorem product_eq_inf [SemilatticeInf α] {a b p : α} {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (hp : IsBinaryProduct π₁ π₂) : p = a ⊓ b :=
  le_antisymm (le_inf (leOfHom π₁) (leOfHom π₂))
    (leOfHom (hp.lift (homOfLE inf_le_left) (homOfLE inf_le_right)))
-- @endregion

-- @region products_coproducts.sup_is_coproduct
-- @provenance definition
/-- **Dually, the coproduct in a poset is the join** `a ⊔ b`: in the opposite poset, `a ⊔ b` is
the meet. -/
def supIsCoproduct [SemilatticeSup α] (a b : α) :
    IsBinaryCoproduct (homOfLE (le_sup_left : a ≤ a ⊔ b)) (homOfLE le_sup_right) where
  lift f g := (homOfLE (sup_le (leOfHom f.unop) (leOfHom g.unop))).op
  lift_fst _ _ := Subsingleton.elim _ _
  lift_snd _ _ := Subsingleton.elim _ _
  uniq _ _ _ _ _ := Subsingleton.elim _ _
-- @endregion

end Order

/-! ### Initial and terminal objects in algebra -/

-- @region products_coproducts.int_initial
-- @provenance library
/-- **`ℤ` is initial among commutative rings**: for every commutative ring `R` there is exactly one
ring homomorphism `ℤ → R`, namely `n ↦ n · 1`. This is Mathlib's `CommRingCat.zIsInitial`
(uniqueness is `RingHom.ext_int`). -/
theorem int_initial : Nonempty (IsInitial (CommRingCat.of ℤ)) :=
  ⟨CommRingCat.zIsInitial⟩
-- @endregion

-- @region products_coproducts.trivial_group_zero
-- @provenance library
/-- **The trivial group is both initial and terminal in `Grp`** (a *zero object*): from any group
there is one homomorphism to it, and to any group there is one homomorphism from it (sending the
identity to the identity). This applies Mathlib's `GrpCat.isZero_of_subsingleton`. -/
theorem trivial_group_zero : IsZero (GrpCat.of PUnit) :=
  GrpCat.isZero_of_subsingleton _
-- @endregion

/-! ### The coproduct of groups is not the product -/

-- @region products_coproducts.free_product_not_comm
-- @provenance independent
/-- **`ℤ ∗ ℤ` is not commutative.** In `Grp`, the coproduct of `ℤ` with itself is the free product
`ℤ ∗ ℤ` (Mathlib's `Monoid.Coprod`, written multiplicatively). Let `x` and `y` be the generators of
the two copies. By the universal property there is a homomorphism `φ : ℤ ∗ ℤ → S₃` sending `x` to
the transposition `(0 1)` and `y` to `(1 2)`. If `x y = y x`, then `φ` would make these two
transpositions commute, and they do not (checked by `decide`). Contrast `prod_comm`. -/
theorem free_product_not_comm :
    ∃ x y : Multiplicative ℤ ∗ Multiplicative ℤ, x * y ≠ y * x := by
  refine ⟨Monoid.Coprod.inl (Multiplicative.ofAdd 1), Monoid.Coprod.inr (Multiplicative.ofAdd 1),
    fun h => ?_⟩
  -- The homomorphism given by the universal property of the coproduct.
  let φ := Monoid.Coprod.lift (zpowersHom (Equiv.Perm (Fin 3)) (Equiv.swap 0 1))
    (zpowersHom (Equiv.Perm (Fin 3)) (Equiv.swap 1 2))
  have hφ := congrArg φ h
  simp only [φ, map_mul, Monoid.Coprod.lift_apply_inl, Monoid.Coprod.lift_apply_inr,
    zpowersHom_apply, toAdd_ofAdd, zpow_one] at hφ
  exact absurd hφ (by decide)
-- @endregion

-- @region products_coproducts.prod_comm
-- @provenance independent
/-- **`ℤ × ℤ` is commutative**: the product of two abelian groups is abelian, componentwise. So the
product and the coproduct of `ℤ` with itself in `Grp` are genuinely different groups. -/
theorem prod_comm (x y : Multiplicative ℤ × Multiplicative ℤ) : x * y = y * x :=
  Prod.ext (mul_comm x.1 y.1) (mul_comm x.2 y.2)
-- @endregion

end Lumenary.ProductsCoproducts
