/-
The Lumenary — formal mathematics
Elementary topos theory: the subobject classifier of the Sierpiński topos, done by hand, and
Mathlib's theorem that every presheaf category is an elementary topos.

The Sierpiński topos is the category of presheaves on the two-element poset `{0 < 1}`. A presheaf
is just a pair of types with a "restriction" map `A₁ → A₀`, and everything can be computed
explicitly. We prove *independently* (from the definitions) that
* the object `Ω` of sieves classifies subobjects: subpresheaves of `A` correspond bijectively to
  natural maps `A ⟶ Ω` (`subEquivHom`), with `χ` and "pull back `true`" mutually inverse;
* the subpresheaves of any `A` form a Heyting algebra (`Sub.instHeytingAlgebra`), with the
  implication computed "at every later stage";
* the terminal presheaf has exactly three subobjects (`sub_one_trichotomy`), one of which has no
  complement (`sub_one_not_boolean`): the internal logic of this topos is not classical.

What Mathlib provides (cited with library provenance): presheaf categories `Cᵒᵖ ⥤ Type u` on a
small category have finite limits, a subobject classifier (`HasSubobjectClassifier`, built from
the presheaf of sieves) and internal homs for the pointwise (= cartesian) product. As far as we
can find, Mathlib does not yet have the Heyting algebra of subobjects in a general topos, its
internal language, or ETCS; our concrete Sierpiński development is not linked to Mathlib's
general classifier.
-/
import Mathlib.CategoryTheory.Topos.Sheaf
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Order.Heyting.Basic

namespace Lumenary.ElementaryTopoi

/-! ### Presheaves on `{0 < 1}` -/

-- @region elementary_topoi.psh
-- @provenance definition
/-- A **presheaf on the poset `{0 < 1}`**: a type `A₁` of "sections at stage 1", a type `A₀` of
"sections at stage 0", and the restriction map `res : A₁ → A₀` along `0 ≤ 1`. (A functor
`{0 < 1}ᵒᵖ ⥤ Type` is exactly this data: the identities must go to identities, so only `res` is
free.) The category of these is the **Sierpiński topos**, also the arrow category of `Type`. -/
structure Psh where
  /-- Sections at stage `1`. -/
  A1 : Type
  /-- Sections at stage `0`. -/
  A0 : Type
  /-- Restriction from stage `1` to stage `0`. -/
  res : A1 → A0
-- @endregion

-- @region elementary_topoi.hom
-- @provenance definition
/-- A **morphism of presheaves** (natural transformation) `A ⟶ B`: maps at each stage that commute
with restriction, `B.res (f1 x) = f0 (A.res x)`. -/
@[ext]
structure Hom (A B : Psh) where
  /-- The component at stage `1`. -/
  f1 : A.A1 → B.A1
  /-- The component at stage `0`. -/
  f0 : A.A0 → B.A0
  /-- Naturality: restricting then mapping equals mapping then restricting. -/
  comm : ∀ x, B.res (f1 x) = f0 (A.res x)
-- @endregion

-- @region elementary_topoi.sub
-- @provenance definition
/-- A **subpresheaf** of `A`: a subset at each stage, closed under restriction. Subobjects of a
presheaf (monomorphisms into it, up to isomorphism) correspond exactly to subpresheaves, because
monomorphisms of presheaves are the pointwise injective natural transformations. -/
@[ext]
structure Sub (A : Psh) where
  /-- The part at stage `1`. -/
  S1 : Set A.A1
  /-- The part at stage `0`. -/
  S0 : Set A.A0
  /-- Restricting a section in the subpresheaf stays in the subpresheaf. -/
  closed : ∀ x, x ∈ S1 → A.res x ∈ S0
-- @endregion

/-! ### The subobject classifier `Ω` -/

-- @region elementary_topoi.omega
-- @provenance definition
/-- The **subobject classifier** `Ω`. Its stage-`0` sections are the sieves on `0`, i.e. truth
values `Prop`. A sieve on `1` is a downward-closed set of arrows into `1`; it is determined by two
propositions — "contains `id₁`" (true *now*) and "contains `0 ≤ 1`" (true *after restriction*) —
with the first implying the second. Restriction forgets the first. -/
def Omega : Psh where
  A1 := {p : Prop × Prop // p.1 → p.2}
  A0 := Prop
  res p := p.1.2
-- @endregion

-- @region elementary_topoi.top1
-- @provenance definition
/-- The maximal sieve on `1`: the value of `true` at stage `1`. -/
def top1 : Omega.A1 := ⟨(True, True), fun _ => trivial⟩
-- @endregion

-- @region elementary_topoi.eq_top1_iff
-- @provenance independent
/-- A sieve on `1` is the maximal sieve exactly when it contains the identity. (The second
component is then forced by the closure condition `p.1 → p.2`.) -/
theorem eq_top1_iff (p : Omega.A1) : p = top1 ↔ p.1.1 := by
  constructor
  · rintro rfl
    trivial
  · intro h
    obtain ⟨⟨a, b⟩, hab⟩ := p
    have hb : b := hab h
    apply Subtype.ext
    simp only [top1, Prod.mk.injEq]
    exact ⟨propext ⟨fun _ => trivial, fun _ => h⟩, propext ⟨fun _ => trivial, fun _ => hb⟩⟩
-- @endregion

-- @region elementary_topoi.chi
-- @provenance definition
/-- The **characteristic map** `χ_S : A ⟶ Ω` of a subpresheaf `S`. A section `x` at stage `1` is
sent to the sieve "`x ∈ S` now, and `res x ∈ S` after restriction"; a section at stage `0` to the
proposition `y ∈ S`. Naturality holds by definition. -/
def chi {A : Psh} (S : Sub A) : Hom A Omega where
  f1 x := ⟨(x ∈ S.S1, A.res x ∈ S.S0), S.closed x⟩
  f0 y := y ∈ S.S0
  comm _ := rfl
-- @endregion

-- @region elementary_topoi.pullback_true
-- @provenance definition
/-- The **pullback of `true` along `φ : A ⟶ Ω`**. Pullbacks of presheaves are computed stage by
stage, so this is the subpresheaf of sections that `φ` sends to `true` (the maximal sieve at stage
`1`, the proposition `True` at stage `0`). Closure under restriction comes from naturality of `φ`. -/
def pullbackTrue {A : Psh} (φ : Hom A Omega) : Sub A where
  S1 := {x | φ.f1 x = top1}
  S0 := {y | φ.f0 y}
  closed x hx := by
    have h1 : (φ.f1 x).1.1 := (eq_top1_iff _).1 hx
    have h2 : Omega.res (φ.f1 x) := (φ.f1 x).2 h1
    show φ.f0 (A.res x)
    rw [← φ.comm x]
    exact h2
-- @endregion

-- @region elementary_topoi.pullback_true_chi
-- @provenance independent
/-- Pulling `true` back along `χ_S` recovers `S`: the square
`S ↪ A`, `χ_S : A → Ω`, `true : 1 → Ω` is a pullback. -/
theorem pullbackTrue_chi {A : Psh} (S : Sub A) : pullbackTrue (chi S) = S := by
  ext x
  · show (chi S).f1 x = top1 ↔ x ∈ S.S1
    rw [eq_top1_iff]
    rfl
  · rfl
-- @endregion

-- @region elementary_topoi.chi_pullback_true
-- @provenance independent
/-- Conversely, every natural map `φ : A ⟶ Ω` is the characteristic map of the subpresheaf it
classifies. At stage `1` the "now" component is recovered by `eq_top1_iff` and the "after
restriction" component by naturality of `φ`. -/
theorem chi_pullbackTrue {A : Psh} (φ : Hom A Omega) : chi (pullbackTrue φ) = φ := by
  apply Hom.ext
  · funext x
    apply Subtype.ext
    show ((φ.f1 x = top1), φ.f0 (A.res x)) = (φ.f1 x).1
    rw [← φ.comm x]
    apply Prod.ext
    · exact propext (eq_top1_iff (φ.f1 x))
    · rfl
  · rfl
-- @endregion

-- @region elementary_topoi.chi_unique
-- @provenance independent
/-- **Uniqueness** in the definition of a subobject classifier: if pulling `true` back along `φ`
gives `S`, then `φ` is `χ_S`. -/
theorem chi_unique {A : Psh} (S : Sub A) (φ : Hom A Omega) (h : pullbackTrue φ = S) :
    φ = chi S := by
  rw [← h, chi_pullbackTrue]
-- @endregion

-- @region elementary_topoi.sub_equiv_hom
-- @provenance definition
/-- **`Ω` classifies subobjects**: subpresheaves of `A` are in bijection with natural maps
`A ⟶ Ω`, via `χ` and pulling back `true`. This is the subobject-classifier axiom for the
Sierpiński topos, in the form "`Sub(A) ≅ Hom(A, Ω)`". -/
def subEquivHom (A : Psh) : Sub A ≃ Hom A Omega where
  toFun := chi
  invFun := pullbackTrue
  left_inv := pullbackTrue_chi
  right_inv := chi_pullbackTrue
-- @endregion

/-! ### Subobjects form a Heyting algebra -/

namespace Sub

variable {A : Psh}

-- @region elementary_topoi.sub.inst_le
-- @provenance definition
/-- Subpresheaves are ordered by inclusion at both stages. -/
instance instLE : LE (Sub A) := ⟨fun S T => S.S1 ⊆ T.S1 ∧ S.S0 ⊆ T.S0⟩
-- @endregion

-- @region elementary_topoi.sub.inst_lt
-- @provenance definition
/-- The strict order: `S < T` when `S ≤ T` but not `T ≤ S`. -/
instance instLT : LT (Sub A) := ⟨fun S T => S ≤ T ∧ ¬ T ≤ S⟩
-- @endregion

-- @region elementary_topoi.sub.inst_max
-- @provenance definition
/-- Union of subpresheaves, stage by stage (closed under restriction because each part is). -/
instance instMax : Max (Sub A) :=
  ⟨fun S T => ⟨S.S1 ∪ T.S1, S.S0 ∪ T.S0, fun x hx => hx.elim
    (fun h => Or.inl (S.closed x h)) (fun h => Or.inr (T.closed x h))⟩⟩
-- @endregion

-- @region elementary_topoi.sub.inst_min
-- @provenance definition
/-- Intersection of subpresheaves, stage by stage. -/
instance instMin : Min (Sub A) :=
  ⟨fun S T => ⟨S.S1 ∩ T.S1, S.S0 ∩ T.S0, fun x hx => ⟨S.closed x hx.1, T.closed x hx.2⟩⟩⟩
-- @endregion

-- @region elementary_topoi.sub.to_pair
-- @provenance definition
/-- Forget closure: a subpresheaf as a pair of subsets. This map is injective and preserves `⊔`,
`⊓` and `≤`, which transfers the distributive-lattice laws from `Set A₁ × Set A₀`. -/
def toPair (S : Sub A) : Set A.A1 × Set A.A0 := (S.S1, S.S0)
-- @endregion

-- @region elementary_topoi.sub.to_pair_injective
-- @provenance independent
/-- A subpresheaf is determined by its two parts. -/
theorem toPair_injective : Function.Injective (toPair (A := A)) := by
  intro S T h
  simp only [toPair, Prod.mk.injEq] at h
  exact Sub.ext h.1 h.2
-- @endregion

-- @region elementary_topoi.sub.inst_distrib_lattice
-- @provenance definition
/-- Subpresheaves form a **distributive lattice** (transferred along `toPair`). -/
instance instDistribLattice : DistribLattice (Sub A) :=
  toPair_injective.distribLattice _ Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)
-- @endregion

-- @region elementary_topoi.sub.inst_bounded_order
-- @provenance definition
/-- The empty and the whole subpresheaf are the least and greatest elements. -/
instance instBoundedOrder : BoundedOrder (Sub A) where
  top := ⟨Set.univ, Set.univ, fun _ _ => trivial⟩
  le_top _ := ⟨Set.subset_univ _, Set.subset_univ _⟩
  bot := ⟨∅, ∅, fun _ h => h⟩
  bot_le _ := ⟨Set.empty_subset _, Set.empty_subset _⟩
-- @endregion

-- @region elementary_topoi.sub.himp
-- @provenance definition
/-- **Heyting implication** of subpresheaves. At stage `0` it is the usual
`{y | y ∈ S → y ∈ T}`. At stage `1`, a section `x` belongs to `S ⇒ T` when the implication holds
*at every stage reachable from `x`*: now, and after restriction. This is the Kripke clause for
implication; the second conjunct is exactly what makes the result closed under restriction. -/
def himp (S T : Sub A) : Sub A where
  S1 := {x | (x ∈ S.S1 → x ∈ T.S1) ∧ (A.res x ∈ S.S0 → A.res x ∈ T.S0)}
  S0 := {y | y ∈ S.S0 → y ∈ T.S0}
  closed _ hx := hx.2
-- @endregion

-- @region elementary_topoi.sub.le_himp_iff
-- @provenance independent
/-- The **residuation law** `U ≤ (S ⇒ T) ↔ U ⊓ S ≤ T`, which makes subpresheaves a Heyting
algebra. The forward direction is modus ponens. For the backward direction at stage `1`, the
"after restriction" clause uses that `U` itself is closed under restriction. -/
theorem le_himp_iff (U S T : Sub A) : U ≤ himp S T ↔ U ⊓ S ≤ T := by
  constructor
  · rintro ⟨h1, h0⟩
    exact ⟨fun x hx => (h1 hx.1).1 hx.2, fun y hy => h0 hy.1 hy.2⟩
  · rintro ⟨h1, h0⟩
    refine ⟨fun x hx => ⟨fun hs => h1 ⟨hx, hs⟩, fun hs => h0 ⟨U.closed x hx, hs⟩⟩,
      fun y hy hs => h0 ⟨hy, hs⟩⟩
-- @endregion

-- @region elementary_topoi.sub.inst_heyting_algebra
-- @provenance definition
/-- **The subobjects of any presheaf on `{0 < 1}` form a Heyting algebra.** Negation is
`¬S = S ⇒ ⊥`. -/
instance instHeytingAlgebra : HeytingAlgebra (Sub A) :=
  HeytingAlgebra.ofHImp himp le_himp_iff
-- @endregion

end Sub

/-! ### The terminal presheaf: three truth values, and a failure of excluded middle -/

-- @region elementary_topoi.one
-- @provenance definition
/-- The **terminal presheaf** `1`: one section at each stage. Its subobjects are the global truth
values of the topos. -/
def one : Psh := ⟨Unit, Unit, fun _ => ()⟩
-- @endregion

-- @region elementary_topoi.later
-- @provenance definition
/-- The **middle truth value**: the subobject of `1` that is empty at stage `1` but full at stage
`0` — "not true now, but true after restriction". -/
def later : Sub one := ⟨∅, Set.univ, fun _ h => h.elim⟩
-- @endregion

-- @region elementary_topoi.sub_one_trichotomy
-- @provenance independent
/-- The terminal presheaf has **exactly three subobjects**: `⊥`, `later` and `⊤` (the case split
on two propositions uses classical logic, as it must: this is a statement *about* the topos, made
in our classical metatheory). -/
theorem sub_one_trichotomy (S : Sub one) : S = ⊥ ∨ S = later ∨ S = ⊤ := by
  by_cases h1 : () ∈ S.S1
  · right; right
    have h0 : () ∈ S.S0 := S.closed () h1
    ext ⟨⟩
    · exact ⟨fun _ => trivial, fun _ => h1⟩
    · exact ⟨fun _ => trivial, fun _ => h0⟩
  · by_cases h0 : () ∈ S.S0
    · right; left
      ext ⟨⟩
      · exact ⟨fun h => (h1 h).elim, fun h => h.elim⟩
      · exact ⟨fun _ => trivial, fun _ => h0⟩
    · left
      ext ⟨⟩
      · exact ⟨fun h => (h1 h).elim, fun h => h.elim⟩
      · exact ⟨fun h => (h0 h).elim, fun h => h.elim⟩
-- @endregion

-- @region elementary_topoi.sub_one_not_boolean
-- @provenance independent
/-- **The Sierpiński topos is not Boolean.** The subobject `later` of `1` has no complement: no
`T` with `later ⊓ T = ⊥` and `later ⊔ T = ⊤`. (Disjointness forces `T` to be empty at stage `0`,
closure then forces it to be empty at stage `1`, and then the union misses stage `1`.) -/
theorem sub_one_not_boolean : ¬ ∃ T : Sub one, later ⊓ T = ⊥ ∧ later ⊔ T = ⊤ := by
  rintro ⟨T, hinf, hsup⟩
  have hT0 : () ∉ T.S0 := fun h => by
    have : () ∈ (later ⊓ T).S0 := ⟨trivial, h⟩
    rw [hinf] at this
    exact this
  have hT1 : () ∉ T.S1 := fun h => hT0 (T.closed () h)
  have : () ∈ (later ⊔ T).S1 := by
    rw [hsup]
    trivial
  rcases this with h | h
  · exact h
  · exact hT1 h
-- @endregion

-- @region elementary_topoi.excluded_middle_fails
-- @provenance independent
/-- **Excluded middle fails internally**: `later ⊔ ¬later ≠ ⊤` in the Heyting algebra of
subobjects of `1`. Here `¬later = later ⇨ ⊥` is computed by the Heyting structure above. -/
theorem excluded_middle_fails : later ⊔ laterᶜ ≠ ⊤ := fun h =>
  sub_one_not_boolean ⟨laterᶜ, inf_compl_self later, h⟩
-- @endregion

-- @region elementary_topoi.not_not_later
-- @provenance independent
/-- Yet `later` is "not not true": its double negation is `⊤`, while `later ≠ ⊤`. So
`¬¬p → p` fails too — a hallmark of intuitionistic logic. -/
theorem not_not_later : laterᶜᶜ = ⊤ ∧ later ≠ ⊤ := by
  refine ⟨?_, fun h => ?_⟩
  · apply le_antisymm le_top
    rw [le_compl_iff_disjoint_right, disjoint_iff]
    -- `laterᶜ` is empty at stage `0` (since `later` is full there) and hence at stage `1`.
    ext ⟨⟩
    · exact ⟨fun hx => (hx.2.2 trivial).elim, fun hx => hx.elim⟩
    · exact ⟨fun hx => hx.2 trivial, fun hx => hx.elim⟩
  · have : () ∈ (⊤ : Sub one).S1 := trivial
    rw [← h] at this
    exact this
-- @endregion

/-! ### Mathlib: every presheaf category is an elementary topos -/

open CategoryTheory Limits MonoidalCategory

universe u

-- @region elementary_topoi.presheaf_category_is_topos
-- @provenance library
/-- **Every presheaf category on a small category is an elementary topos**: it has finite limits,
a subobject classifier (Mathlib's `HasSubobjectClassifier` instance from
`Mathlib.CategoryTheory.Topos.Sheaf`, whose `Ω` is the presheaf of sieves), and internal homs
(`MonoidalClosed`, from `Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes`) for the pointwise
product — which is the categorical product, see `presheaf_tensor_eq_prod`. All three are
instances found by `inferInstance`. -/
theorem presheaf_category_is_topos (C : Type u) [SmallCategory C] :
    HasFiniteLimits (Cᵒᵖ ⥤ Type u) ∧ HasSubobjectClassifier (Cᵒᵖ ⥤ Type u) ∧
      Nonempty (MonoidalClosed (Cᵒᵖ ⥤ Type u)) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance⟩⟩
-- @endregion

-- @region elementary_topoi.presheaf_tensor_eq_prod
-- @provenance library
/-- The monoidal product used by the closed structure above is the pointwise cartesian product:
`(F ⊗ G)(c) = F(c) × G(c)`, by definition of Mathlib's monoidal structure on functor categories.
Mathlib also makes it a `CartesianMonoidalCategory` (chosen finite products), so `MonoidalClosed`
here is cartesian closedness. -/
theorem presheaf_tensor_eq_prod (C : Type u) [SmallCategory C] (F G : Cᵒᵖ ⥤ Type u) (c : Cᵒᵖ) :
    (F ⊗ G).obj c = (F.obj c × G.obj c) :=
  rfl
-- @endregion

end Lumenary.ElementaryTopoi
