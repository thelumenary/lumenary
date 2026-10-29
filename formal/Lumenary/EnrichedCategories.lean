/-
The Lumenary — formal mathematics
Enriched categories: Lawvere's metric spaces as categories enriched in `([0, ∞], ≥, +, 0)`,
preorders as categories enriched in truth values, ordinary categories as `Set`-enriched
categories, and rings as one-object `Ab`-enriched categories.

What is proved here. We build Lawvere's monoidal category `Dist` (objects `[0, ∞]`, an arrow
`a ⟶ b` exactly when `a ≥ b`, tensor `+`, unit `0`) and prove that Mathlib's
`EnrichedCategory Dist X` structures on a type `X` correspond exactly to Lawvere metrics on `X`
(`d x x = 0` and the triangle inequality). We do the same for truth values `(Prop, →, ∧, True)`
and preorders. We prove that enriched functors between Lawvere metric spaces are exactly the
non-expansive maps, that the supremum distance makes non-expansive maps into a Lawvere metric
space, that every (pseudo-e)metric space is a Lawvere metric space, and that the "uphill
distance" on `ℝ` is a Lawvere metric which is not symmetric.

What Mathlib provides. `CategoryTheory.EnrichedCategory`, `EnrichedFunctor`, the equivalence
between `Type`-enriched categories and ordinary categories
(`enrichedCategoryTypeEquivCategory`), and the ring structure on endomorphisms in a preadditive
category. Not formalised here: strict 2-categories as `Cat`-enriched categories, Lawvere's
Cauchy completion, and `V`-natural transformations for general `V`.
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Topology.EMetricSpace.Defs

namespace Lumenary.EnrichedCategories

open CategoryTheory MonoidalCategory ENNReal

universe u v

/-! ### Lawvere's base of enrichment -/

-- @region enriched_categories.dist
-- @provenance definition
/-- **Lawvere's monoidal category `([0, ∞], ≥, +, 0)`.** Its objects are the extended
non-negative reals; we use the order dual of `ℝ≥0∞`, so that (by Mathlib's category structure on
a preorder) there is exactly one arrow `a ⟶ b` when `a ≥ b` as distances, and none otherwise. -/
abbrev Dist : Type := ℝ≥0∞ᵒᵈ
-- @endregion

-- @region enriched_categories.dist_monoidal
-- @provenance definition
/-- The monoidal structure on `Dist`: `a ⊗ b = a + b`, unit `0`. Addition is monotone, so it
acts on arrows, and the associator and unitors are the equalities `(a + b) + c = a + (b + c)`,
`0 + a = a`, `a + 0 = a`. In a category with at most one arrow between two objects every diagram
commutes, so the pentagon and triangle axioms hold automatically. -/
instance distMonoidal : MonoidalCategory Dist where
  tensorObj a b := a + b
  whiskerLeft a _ _ f := homOfLE (add_le_add_right (leOfHom f) a)
  whiskerRight f b := homOfLE (add_le_add_left (leOfHom f) b)
  tensorUnit := 0
  associator a b c := eqToIso (add_assoc a b c)
  leftUnitor a := eqToIso (zero_add a)
  rightUnitor a := eqToIso (add_zero a)
  id_tensorHom_id _ _ := Subsingleton.elim _ _
  tensorHom_comp_tensorHom _ _ _ _ := Subsingleton.elim _ _
  whiskerLeft_id _ _ := Subsingleton.elim _ _
  id_whiskerRight _ _ := Subsingleton.elim _ _
  associator_naturality _ _ _ := Subsingleton.elim _ _
  leftUnitor_naturality _ := Subsingleton.elim _ _
  rightUnitor_naturality _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _
-- @endregion

-- @region enriched_categories.lawvere_metric
-- @provenance definition
/-- A **Lawvere metric** on `X`: distances `d x y ∈ [0, ∞]` with `d x x = 0` and the triangle
inequality. Symmetry, finiteness and "`d x y = 0 → x = y`" are *not* required. -/
structure LawvereMetric (X : Type u) where
  /-- The distance from `x` to `y`. -/
  d : X → X → ℝ≥0∞
  /-- Every point is at distance `0` from itself. -/
  self : ∀ x, d x x = 0
  /-- The triangle inequality. -/
  triangle : ∀ x y z, d x z ≤ d x y + d y z
-- @endregion

-- @region enriched_categories.lawvere_metric.ext
-- @provenance independent
/-- Two Lawvere metrics with the same distance function are equal. -/
@[ext]
theorem LawvereMetric.ext {X : Type u} {M N : LawvereMetric X} (h : M.d = N.d) : M = N := by
  cases M
  cases N
  cases h
  rfl
-- @endregion

-- @region enriched_categories.lawvere_equiv_enriched
-- @provenance independent
/-- **Lawvere's observation: metric spaces are enriched categories.** On any type `X`,
`Dist`-enriched category structures (in Mathlib's sense) correspond exactly to Lawvere metrics.
* the hom-object `X(x, y)` is the distance `d x y`;
* an identity `0 ⟶ X(x, x)` exists iff `0 ≥ d x x`, i.e. `d x x = 0`;
* a composition `X(x, y) ⊗ X(y, z) ⟶ X(x, z)` exists iff `d x y + d y z ≥ d x z` — the
  triangle inequality *is* composition;
* the unit and associativity axioms hold automatically, since `Dist` is thin. -/
def lawvereEquivEnriched (X : Type u) : LawvereMetric X ≃ EnrichedCategory Dist X where
  toFun M :=
    { Hom := fun x y => OrderDual.toDual (M.d x y)
      id := fun x => homOfLE (by
        show M.d x x ≤ 0
        rw [M.self])
      comp := fun x y z => homOfLE (M.triangle x y z)
      id_comp := fun _ _ => Subsingleton.elim _ _
      comp_id := fun _ _ => Subsingleton.elim _ _
      assoc := fun _ _ _ _ => Subsingleton.elim _ _ }
  invFun E :=
    { d := fun x y => OrderDual.ofDual (E.Hom x y)
      self := fun x => le_antisymm (leOfHom (E.id x)) zero_le
      triangle := fun x y z => leOfHom (E.comp x y z) }
  left_inv M := by
    ext x y
    rfl
  right_inv E := by
    -- the hom-objects agree definitionally, and identities and compositions are arrows in a
    -- thin category, so `congr` closes the goal (using `Subsingleton`)
    rcases E with ⟨Hom, id, comp, _, _, _⟩
    congr
-- @endregion

/-! ### Examples of Lawvere metrics -/

-- @region enriched_categories.of_pseudo_emetric
-- @provenance library
/-- **Every (pseudo-extended) metric space is a Lawvere metric space**, using Mathlib's
`edist_self` and `edist_triangle`. Lawvere's notion drops symmetry and allows `d x y = 0` for
`x ≠ y`. -/
def ofPseudoEMetric (X : Type u) [PseudoEMetricSpace X] : LawvereMetric X where
  d := edist
  self := edist_self
  triangle := edist_triangle
-- @endregion

-- @region enriched_categories.uphill
-- @provenance definition
/-- The **uphill distance** on `ℝ` (think of heights): going from `x` up to `y` costs `y - x`,
going down is free. In `ℝ≥0∞`, `d x y = ofReal (y - x)`, where `ofReal` truncates negative
numbers to `0`. -/
noncomputable def uphill : LawvereMetric ℝ where
  d x y := ENNReal.ofReal (y - x)
  self x := by simp
  triangle x y z := by
    calc ENNReal.ofReal (z - x) = ENNReal.ofReal ((y - x) + (z - y)) := by ring_nf
      _ ≤ ENNReal.ofReal (y - x) + ENNReal.ofReal (z - y) := ENNReal.ofReal_add_le
-- @endregion

-- @region enriched_categories.uphill_not_symmetric
-- @provenance independent
/-- **Lawvere metrics need not be symmetric**: in the uphill distance, `d 0 1 = 1` but
`d 1 0 = 0`. -/
theorem uphill_not_symmetric : uphill.d 0 1 = 1 ∧ uphill.d 1 0 = 0 := by
  constructor
  · simp [uphill]
  · simp [uphill]
-- @endregion

-- @region enriched_categories.underlying_preorder
-- @provenance independent
/-- **The underlying ordinary category of a Lawvere metric space** is a preorder: there is an
arrow `x → y` (an arrow `0 ⟶ X(x, y)` in `Dist`) exactly when `d x y = 0`, and this relation is
reflexive and transitive by `d x x = 0` and the triangle inequality. -/
theorem underlying_preorder {X : Type u} (M : LawvereMetric X) :
    (∀ x, M.d x x = 0) ∧ (∀ x y z, M.d x y = 0 → M.d y z = 0 → M.d x z = 0) := by
  refine ⟨M.self, fun x y z hxy hyz => ?_⟩
  apply le_antisymm _ zero_le
  calc M.d x z ≤ M.d x y + M.d y z := M.triangle x y z
    _ = 0 := by rw [hxy, hyz, add_zero]
-- @endregion

-- @region enriched_categories.yoneda_isometry
-- @provenance independent
/-- **The enriched Yoneda lemma for Lawvere metric spaces.** Send `x` to the "distance-to"
function `d(-, x)`. Comparing these functions with the closed structure of `Dist` (truncated
subtraction) recovers the metric:
`d x y = sup_z (d z y - d z x)`.
So `x ↦ d(-, x)` is an isometric embedding of `X` into a space of functions — the Yoneda
embedding, which for symmetric metric spaces is the Kuratowski–Fréchet embedding.
Proof: each term is `≤ d x y` because `d z y ≤ d z x + d x y` (triangle inequality, via
`tsub_le_iff_left`), and the term `z = x` equals `d x y - 0 = d x y`. -/
theorem yoneda_isometry {X : Type u} (M : LawvereMetric X) (x y : X) :
    ⨆ z, (M.d z y - M.d z x) = M.d x y := by
  apply le_antisymm
  · exact iSup_le fun z => tsub_le_iff_left.mpr (M.triangle z x y)
  · exact le_iSup_of_le x (by rw [M.self, tsub_zero])
-- @endregion

/-! ### Enriched functors are non-expansive maps -/

-- @region enriched_categories.non_expansive_equiv
-- @provenance independent
/-- **`Dist`-enriched functors are exactly non-expansive (1-Lipschitz) maps.** A `Dist`-functor
`F : X → Y` consists of a map on points with an arrow `X(x, y) ⟶ Y(F x, F y)` in `Dist` for all
`x, y`, i.e. `d (F x) (F y) ≤ d x y`; the functor axioms are automatic. -/
def nonExpansiveEquiv {X : Type u} {Y : Type v} [EnrichedCategory Dist X]
    [EnrichedCategory Dist Y] :
    { f : X → Y // ∀ x x', OrderDual.ofDual (EnrichedCategory.Hom (V := Dist) (f x) (f x')) ≤
        OrderDual.ofDual (EnrichedCategory.Hom (V := Dist) x x') } ≃
      EnrichedFunctor Dist X Y where
  toFun f :=
    { obj := f.1
      map := fun x x' => homOfLE (f.2 x x')
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ _ => Subsingleton.elim _ _ }
  invFun F := ⟨F.obj, fun x x' => leOfHom (F.map x x')⟩
  left_inv _ := rfl
  right_inv F := by
    rcases F with ⟨obj, map, _, _⟩
    simp only [EnrichedFunctor.mk.injEq, heq_eq_eq, true_and]
    funext x x'
    exact Subsingleton.elim _ _
-- @endregion

-- @region enriched_categories.sup_metric
-- @provenance independent
/-- **The enriched functor category.** For a Lawvere metric `N` on `Y`, the maps `X → Y` carry the
Lawvere metric `d(f, g) = sup_x d(f x, g x)`. Self-distance: `sup_x 0 = 0`. Triangle:
`d(f x, h x) ≤ d(f x, g x) + d(g x, h x) ≤ d(f, g) + d(g, h)` for each `x`, and take the
supremum. (This is the hom-object of the `Dist`-enriched category of `Dist`-functors.) -/
noncomputable def supMetric (X : Type u) {Y : Type v} (N : LawvereMetric Y) :
    LawvereMetric (X → Y) where
  d f g := ⨆ x, N.d (f x) (g x)
  self f := by simp [N.self]
  triangle f g h := by
    apply iSup_le
    intro x
    calc N.d (f x) (h x) ≤ N.d (f x) (g x) + N.d (g x) (h x) := N.triangle _ _ _
      _ ≤ (⨆ x, N.d (f x) (g x)) + ⨆ x, N.d (g x) (h x) :=
        add_le_add (le_iSup (fun x => N.d (f x) (g x)) x) (le_iSup (fun x => N.d (g x) (h x)) x)
-- @endregion

-- @region enriched_categories.dist_closed
-- @provenance library
/-- **`Dist` is closed**: the internal hom is truncated subtraction, `[a, b] = b - a`, because
`a + c ≥ b ↔ c ≥ b - a` (Mathlib's `tsub_le_iff_left` in `ℝ≥0∞`). So `Dist`-categories can be
enriched over themselves, which is what makes `supMetric` a hom-object. -/
theorem dist_closed (a b c : ℝ≥0∞) : b - a ≤ c ↔ b ≤ a + c :=
  tsub_le_iff_left
-- @endregion

/-! ### Truth values and preorders -/

-- @region enriched_categories.truth_monoidal
-- @provenance definition
/-- **Truth values as a monoidal category.** `Prop` is a preorder under implication, hence a
category with an arrow `p ⟶ q` exactly when `p → q`; the tensor is `∧` and the unit is `True`.
Again all coherence axioms hold because the category is thin. -/
instance truthMonoidal : MonoidalCategory Prop where
  tensorObj p q := p ∧ q
  whiskerLeft p _ _ f := homOfLE fun h => ⟨h.1, leOfHom f h.2⟩
  whiskerRight f q := homOfLE fun h => ⟨leOfHom f h.1, h.2⟩
  tensorUnit := True
  associator p q r := eqToIso (propext and_assoc)
  leftUnitor p := eqToIso (true_and p)
  rightUnitor p := eqToIso (and_true p)
  id_tensorHom_id _ _ := Subsingleton.elim _ _
  tensorHom_comp_tensorHom _ _ _ _ := Subsingleton.elim _ _
  whiskerLeft_id _ _ := Subsingleton.elim _ _
  id_whiskerRight _ _ := Subsingleton.elim _ _
  associator_naturality _ _ _ := Subsingleton.elim _ _
  leftUnitor_naturality _ := Subsingleton.elim _ _
  rightUnitor_naturality _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _
-- @endregion

-- @region enriched_categories.preorder_equiv_enriched
-- @provenance independent
/-- **Preorders are exactly the categories enriched in truth values.** A `Prop`-enriched category
on `X` is a relation `x ≤ y` (the hom-object) with an identity `True → (x ≤ x)` (reflexivity)
and a composition `(x ≤ y) ∧ (y ≤ z) → (x ≤ z)` (transitivity). -/
def preorderEquivEnriched (X : Type u) :
    { r : X → X → Prop // (∀ x, r x x) ∧ ∀ x y z, r x y → r y z → r x z } ≃
      EnrichedCategory Prop X where
  toFun r :=
    { Hom := r.1
      id := fun x => homOfLE fun _ => r.2.1 x
      comp := fun x y z => homOfLE fun h => r.2.2 x y z h.1 h.2
      id_comp := fun _ _ => Subsingleton.elim _ _
      comp_id := fun _ _ => Subsingleton.elim _ _
      assoc := fun _ _ _ _ => Subsingleton.elim _ _ }
  invFun E :=
    ⟨E.Hom, fun x => leOfHom (E.id x) trivial, fun x y z h₁ h₂ => leOfHom (E.comp x y z) ⟨h₁, h₂⟩⟩
  left_inv _ := rfl
  right_inv E := by
    -- the hom-objects agree definitionally, and identities and compositions are arrows in a
    -- thin category, so `congr` closes the goal (using `Subsingleton`)
    rcases E with ⟨Hom, id, comp, _, _, _⟩
    congr
-- @endregion

/-! ### Sets and abelian groups -/

-- @region enriched_categories.set_enriched
-- @provenance library
/-- **Locally small categories are exactly the categories enriched in `(Type, ×, PUnit)`**
(Mathlib's `enrichedCategoryTypeEquivCategory`). -/
theorem set_enriched (C : Type u) : Nonempty (EnrichedCategory (Type v) C ≃ Category.{v} C) :=
  ⟨enrichedCategoryTypeEquivCategory C⟩
-- @endregion

-- @region enriched_categories.end_ring
-- @provenance library
/-- **In an `Ab`-enriched (preadditive) category, the endomorphisms of an object form a ring**,
with addition from the enrichment and multiplication given by composition (Mathlib's instance
`CategoryTheory.End` ring). A one-object `Ab`-enriched category is therefore a ring. -/
theorem end_ring {C : Type u} [Category.{v} C] [Preadditive C] (X : C) :
    Nonempty (Ring (End X)) :=
  ⟨inferInstance⟩
-- @endregion

end Lumenary.EnrichedCategories
