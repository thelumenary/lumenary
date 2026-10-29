/-
The Lumenary — formal mathematics
Products by maps: a first universal property.

Proved here (`@provenance independent`), mirroring the lesson: the pairing `⟨f, g⟩` of two
functions satisfies `π₁ ∘ ⟨f, g⟩ = f` and `π₂ ∘ ⟨f, g⟩ = g` and is the *only* function that
does; functions `X → A × B` therefore correspond exactly to pairs of functions; for finite
types this gives `|A × B|^|X| = |A|^|X| · |B|^|X|`; `A × B` (and also `B × A` with swapped
projections) has the universal property; any type with the universal property is in bijection
with `A × B` by the pairing of its two maps, and that is the only compatible map; and two
"fake products" that fail existence or uniqueness.

From the library (`@provenance library`): Mathlib's equivalence
`Equiv.arrowProdEquivProdArrow`. We work with Lean *types* and functions, the type-theoretic
counterpart of sets and functions. In Mathlib the general notion of a product in a category is
`CategoryTheory.Limits.BinaryFan.IsLimit`; our `IsProduct` is that notion written out by hand
for types, without the category-theory library.
-/
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

namespace Lumenary.IntroUniversalProperties

universe u

/-! ### Pairing -/

-- @region intro_universal_properties.pair
-- @provenance definition
/-- The **pairing** `⟨f, g⟩ : X → A × B` of `f : X → A` and `g : X → B` sends `x` to the
ordered pair `(f x, g x)`. -/
def pair {X A B : Type u} (f : X → A) (g : X → B) : X → A × B :=
  fun x => (f x, g x)
-- @endregion

-- @region intro_universal_properties.fst_comp_pair
-- @provenance independent
/-- First projection after pairing gives back `f`: `π₁ ∘ ⟨f, g⟩ = f`. Both sides send `x` to
`f x`, so Lean accepts `rfl` ("true by computation"). -/
theorem fst_comp_pair {X A B : Type u} (f : X → A) (g : X → B) :
    Prod.fst ∘ pair f g = f :=
  rfl
-- @endregion

-- @region intro_universal_properties.snd_comp_pair
-- @provenance independent
/-- Second projection after pairing gives back `g`: `π₂ ∘ ⟨f, g⟩ = g`. -/
theorem snd_comp_pair {X A B : Type u} (f : X → A) (g : X → B) :
    Prod.snd ∘ pair f g = g :=
  rfl
-- @endregion

-- @region intro_universal_properties.pair_unique
-- @provenance independent
/-- **Uniqueness.** If `h : X → A × B` satisfies `π₁ ∘ h = f` and `π₂ ∘ h = g`, then
`h = ⟨f, g⟩`. Proof, as in the lesson: for each `x`, the pair `h x` has first coordinate
`f x` and second coordinate `g x`, and a pair is determined by its two coordinates
(`Prod.ext`). -/
theorem pair_unique {X A B : Type u} {f : X → A} {g : X → B} (h : X → A × B)
    (h₁ : Prod.fst ∘ h = f) (h₂ : Prod.snd ∘ h = g) : h = pair f g := by
  funext x
  apply Prod.ext
  · -- first coordinates: `(h x).1 = f x`
    exact congrFun h₁ x
  · -- second coordinates: `(h x).2 = g x`
    exact congrFun h₂ x
-- @endregion

/-! ### Maps into a product are pairs of maps -/

-- @region intro_universal_properties.maps_into_prod_equiv
-- @provenance definition
/-- Functions `X → A × B` correspond one-to-one with pairs of functions `(X → A, X → B)`.
Forward: compose with the two projections. Backward: pair. The two round trips are the
identity: one by `fst_comp_pair`/`snd_comp_pair`, the other by `pair_unique`. -/
def mapsIntoProdEquiv (X A B : Type u) : (X → A × B) ≃ (X → A) × (X → B) where
  toFun h := (Prod.fst ∘ h, Prod.snd ∘ h)
  invFun fg := pair fg.1 fg.2
  left_inv h := (pair_unique h rfl rfl).symm
  right_inv _ := rfl
-- @endregion

-- @region intro_universal_properties.maps_into_prod_equiv_library
-- @provenance library
/-- Mathlib already has this correspondence, for dependent functions too:
`Equiv.arrowProdEquivProdArrow`. Here we just specialise it to ordinary functions. -/
def mapsIntoProdEquivLibrary (X A B : Type u) : (X → A × B) ≃ (X → A) × (X → B) :=
  Equiv.arrowProdEquivProdArrow X (fun _ => A) (fun _ => B)
-- @endregion

-- @region intro_universal_properties.card_maps_into_prod
-- @provenance independent
/-- **Counting.** For finite types, `|A × B|^|X| = |A|^|X| · |B|^|X|`. The left side counts
functions `X → A × B`, the right side counts pairs of functions, and `mapsIntoProdEquiv`
matches them up one-to-one. -/
theorem card_maps_into_prod (X A B : Type u) [Fintype X] [DecidableEq X] [Fintype A]
    [Fintype B] :
    Fintype.card (A × B) ^ Fintype.card X =
      Fintype.card A ^ Fintype.card X * Fintype.card B ^ Fintype.card X := by
  calc Fintype.card (A × B) ^ Fintype.card X
      = Fintype.card (X → A × B) := Fintype.card_fun.symm
    _ = Fintype.card ((X → A) × (X → B)) := Fintype.card_congr (mapsIntoProdEquiv X A B)
    _ = Fintype.card (X → A) * Fintype.card (X → B) := Fintype.card_prod _ _
    _ = Fintype.card A ^ Fintype.card X * Fintype.card B ^ Fintype.card X := by
        rw [Fintype.card_fun, Fintype.card_fun]
-- @endregion

/-! ### The universal property, and what it determines -/

-- @region intro_universal_properties.is_product
-- @provenance definition
/-- `IsProduct p q` says that the type `P` with maps `p : P → A` and `q : P → B` has the
**universal property of the product**: for every type `X` and every pair of maps
`f : X → A`, `g : X → B` there is **exactly one** `h : X → P` with `p ∘ h = f` and
`q ∘ h = g`. (`∃!` is Lean's "there exists exactly one".) -/
def IsProduct {A B P : Type u} (p : P → A) (q : P → B) : Prop :=
  ∀ (X : Type u) (f : X → A) (g : X → B), ∃! h : X → P, p ∘ h = f ∧ q ∘ h = g
-- @endregion

-- @region intro_universal_properties.prod_is_product
-- @provenance independent
/-- The set of ordered pairs `A × B`, with its two projections, has the universal property:
existence is the pairing `⟨f, g⟩`, uniqueness is `pair_unique`. -/
theorem prod_isProduct (A B : Type u) : IsProduct (Prod.fst : A × B → A) Prod.snd := by
  intro X f g
  refine ⟨pair f g, ⟨fst_comp_pair f g, snd_comp_pair f g⟩, ?_⟩
  rintro h ⟨h₁, h₂⟩
  exact pair_unique h h₁ h₂
-- @endregion

-- @region intro_universal_properties.swap_is_product
-- @provenance independent
/-- A *different* type can be a product of `A` and `B`: `B × A`, with the first map reading
off the **second** coordinate and the second map the **first**. Given `f` and `g`, the unique
compatible map is `x ↦ (g x, f x)`. -/
theorem swap_isProduct (A B : Type u) : IsProduct (Prod.snd : B × A → A) Prod.fst := by
  intro X f g
  refine ⟨fun x => (g x, f x), ⟨rfl, rfl⟩, ?_⟩
  rintro h ⟨h₁, h₂⟩
  funext x
  exact Prod.ext (congrFun h₂ x) (congrFun h₁ x)
-- @endregion

-- @region intro_universal_properties.eq_id_of_is_product
-- @provenance independent
/-- **The key trick.** If `(P, p, q)` is a product and `k : P → P` is compatible with the maps
(`p ∘ k = p` and `q ∘ k = q`), then `k` is the identity. Reason: apply the universal property
with `X = P`, `f = p`, `g = q`. Both `k` and `id` are compatible maps, and there is only one. -/
theorem eq_id_of_isProduct {A B P : Type u} {p : P → A} {q : P → B} (hP : IsProduct p q)
    (k : P → P) (hk₁ : p ∘ k = p) (hk₂ : q ∘ k = q) : k = id := by
  obtain ⟨_, _, huniq⟩ := hP P p q
  have hk : k = _ := huniq k ⟨hk₁, hk₂⟩
  have hid : id = _ := huniq id ⟨rfl, rfl⟩
  exact hk.trans hid.symm
-- @endregion

-- @region intro_universal_properties.is_product_bijective
-- @provenance independent
/-- **A product is determined up to a unique compatible bijection.** If `(P, p, q)` has the
universal property, then `⟨p, q⟩ : P → A × B` is a bijection. (It is compatible with the maps
by `fst_comp_pair`/`snd_comp_pair`, and it is the *only* compatible map by `pair_unique`.)

Proof, as in the lesson. The universal property of `P`, applied to the projections of `A × B`,
gives `ψ : A × B → P` with `p ∘ ψ = π₁` and `q ∘ ψ = π₂`. Then `ψ ∘ ⟨p, q⟩ : P → P` is
compatible with `p` and `q`, so it is the identity by `eq_id_of_isProduct`; and
`⟨p, q⟩ ∘ ψ : A × B → A × B` is compatible with the projections, so it is the identity by
`pair_unique`. A map with a two-sided inverse is a bijection. -/
theorem isProduct_bijective {A B P : Type u} {p : P → A} {q : P → B} (hP : IsProduct p q) :
    Function.Bijective (pair p q) := by
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, _⟩ := hP (A × B) (Prod.fst : A × B → A) (Prod.snd : A × B → B)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨ψ, ?_, ?_⟩
  · -- `ψ ∘ ⟨p, q⟩ = id` on `P`
    have h : ψ ∘ pair p q = id := by
      apply eq_id_of_isProduct hP
      · calc p ∘ (ψ ∘ pair p q) = (p ∘ ψ) ∘ pair p q := rfl
          _ = Prod.fst ∘ pair p q := by rw [hψ₁]
          _ = p := fst_comp_pair p q
      · calc q ∘ (ψ ∘ pair p q) = (q ∘ ψ) ∘ pair p q := rfl
          _ = Prod.snd ∘ pair p q := by rw [hψ₂]
          _ = q := snd_comp_pair p q
    exact congrFun h
  · -- `⟨p, q⟩ ∘ ψ = id` on `A × B`
    have h : pair p q ∘ ψ = id := by
      have hu : pair p q ∘ ψ = pair (Prod.fst : A × B → A) (Prod.snd : A × B → B) :=
        pair_unique (pair p q ∘ ψ) hψ₁ hψ₂
      rw [hu]
      rfl
    exact congrFun h
-- @endregion

/-! ### Two fake products -/

-- @region intro_universal_properties.not_is_product_empty
-- @provenance independent
/-- **Existence can fail.** Take `A = B = Unit` (one element each) and `P = Empty`. There is no
map at all from `Unit` to `Empty`, so the pair of maps `Unit → Unit` cannot factor through `P`. -/
theorem not_isProduct_empty :
    ¬ IsProduct (fun e : Empty => (Empty.elim e : Unit)) (fun e : Empty => (Empty.elim e : Unit)) := by
  intro hP
  obtain ⟨h, _, _⟩ := hP Unit id id
  exact (h ()).elim
-- @endregion

-- @region intro_universal_properties.not_is_product_bool
-- @provenance independent
/-- **Uniqueness can fail.** Take `A = B = Unit` and `P = Bool` (two elements), with the only
possible maps `P → Unit`. Then *both* constant maps `Unit → Bool` are compatible, so there is
not exactly one. The universal property needs its "exactly". -/
theorem not_isProduct_bool : ¬ IsProduct (fun _ : Bool => ()) (fun _ : Bool => ()) := by
  intro hP
  obtain ⟨_, _, huniq⟩ := hP Unit id id
  have ht : (fun _ : Unit => true) = _ := huniq (fun _ => true) ⟨rfl, rfl⟩
  have hf : (fun _ : Unit => false) = _ := huniq (fun _ => false) ⟨rfl, rfl⟩
  have h : (fun _ : Unit => true) = (fun _ : Unit => false) := ht.trans hf.symm
  exact Bool.noConfusion (congrFun h ())
-- @endregion

end Lumenary.IntroUniversalProperties
