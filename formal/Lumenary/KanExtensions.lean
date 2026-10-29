/-
The Lumenary — formal mathematics
Kan extensions: left and right Kan extensions, their pointwise formulas, limits and adjoints
as Kan extensions.

What is proved here. The first part is an independent formalisation of Kan extensions in the
*thin* case: preorders are categories with at most one arrow between two objects, monotone
maps are functors, and a natural transformation `f ⇒ g` exists exactly when `f ≤ g`
pointwise. For monotone `k : C → D` and `f : C → E` with `E` a complete lattice, the pointwise
formula `Lan_k f (d) = ⨆_{k c ≤ d} f c` (a colimit over the comma category `(k ↓ d)`) is proved
to be a left Kan extension, `Lan_k` is proved left adjoint to precomposition with `k`, and
dually for `Ran`. Limits are right Kan extensions along `C → Unit`, and Mac Lane's criterion
"G has a left adjoint iff `Ran_G id` exists and is preserved by `G`" is proved for complete
lattices. These are genuine special cases, not the general theorems.

The second part cites Mathlib's general theory (`CategoryTheory.Functor.leftKanExtension`,
`Functor.lanAdjunction`, `leftKanExtensionObjIsoColimit`), developed by Joël Riou and others:
the left Kan extension functor is a left adjoint, pointwise Kan extensions are computed by
colimits over comma categories, and they exist when the source is small and the target is
cocomplete.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

namespace Lumenary.KanExtensions

/-! ### Kan extensions between preorders (thin categories) -/

section Thin

/- `C` is any type in the formulas: a colimit in a complete lattice is the supremum of the
values, whatever the arrows of the diagram are. `C` needs an order only where `f` is a functor
(monotone) — in `lan_comp_of_embedding` and `lan_gc`. -/
variable {C D E : Type*} [Preorder D] [CompleteLattice E]

-- @region kan_extensions.lan
-- @provenance definition
/-- The **pointwise left Kan extension** of `f : C → E` along `k : C → D`, for a preorder `D`
and a complete lattice `E` (the order of `C`, if any, plays no role in the formula):
`lan k f d = ⨆ { f c | k c ≤ d }`.
This is the formula `(Lan_k f)(d) = colim_{(k ↓ d)} f`: in a thin category the comma category
`(k ↓ d)` is the set of `c` with `k c ≤ d`, and a colimit in a complete lattice is a supremum. -/
def lan (k : C → D) (f : C → E) (d : D) : E :=
  ⨆ (c : C) (_ : k c ≤ d), f c
-- @endregion

-- @region kan_extensions.ran
-- @provenance definition
/-- The **pointwise right Kan extension**: `ran k f d = ⨅ { f c | d ≤ k c }`, the limit of `f`
over the comma category `(d ↓ k)`. -/
def ran (k : C → D) (f : C → E) (d : D) : E :=
  ⨅ (c : C) (_ : d ≤ k c), f c
-- @endregion

-- @region kan_extensions.lan_monotone
-- @provenance independent
/-- `lan k f` is a functor, i.e. monotone: if `d ≤ d'` then every `c` with `k c ≤ d` also has
`k c ≤ d'`, so the supremum can only grow. (This is how a pointwise Kan extension acts on
arrows: an arrow `d → d'` induces a functor `(k ↓ d) → (k ↓ d')` and hence a map of colimits.) -/
theorem lan_monotone (k : C → D) (f : C → E) : Monotone (lan k f) := by
  intro d d' h
  exact iSup₂_le fun c hc => le_iSup₂_of_le c (hc.trans h) le_rfl
-- @endregion

-- @region kan_extensions.le_lan_comp
-- @provenance independent
/-- The **unit** `f ⇒ (Lan_k f) ∘ k`: `f c ≤ lan k f (k c)`, because `c` itself lies in the
comma category `(k ↓ k c)` (via the identity `k c ≤ k c`). -/
theorem le_lan_comp (k : C → D) (f : C → E) (c : C) : f c ≤ lan k f (k c) :=
  le_iSup₂_of_le c le_rfl le_rfl
-- @endregion

-- @region kan_extensions.lan_le_iff
-- @provenance independent
/-- The **universal property** of the left Kan extension. For every monotone `g : D → E`:
`Lan_k f ≤ g` if and only if `f ≤ g ∘ k`.
(→) compose with the unit: `f c ≤ lan k f (k c) ≤ g (k c)`.
(←) each term `f c` with `k c ≤ d` satisfies `f c ≤ g (k c) ≤ g d` by monotonicity of `g`.
In a thin category, arrows are unique when they exist, so this *is* the statement that every
`f ⇒ g ∘ k` factors uniquely through the unit. -/
theorem lan_le_iff (k : C → D) (f : C → E) {g : D → E} (hg : Monotone g) :
    lan k f ≤ g ↔ ∀ c, f c ≤ g (k c) := by
  constructor
  · intro h c
    exact (le_lan_comp k f c).trans (h (k c))
  · intro h d
    exact iSup₂_le fun c hc => (h c).trans (hg hc)
-- @endregion

-- @region kan_extensions.lan_unique
-- @provenance independent
/-- **Uniqueness**: any monotone `L : D → E` with the universal property of a left Kan
extension equals the pointwise formula. As always with universal properties, the proof plays
the two universal properties against each other. -/
theorem lan_unique (k : C → D) (f : C → E) {L : D → E} (hL : Monotone L)
    (huniv : ∀ g : D → E, Monotone g → (L ≤ g ↔ ∀ c, f c ≤ g (k c))) :
    L = lan k f := by
  apply le_antisymm
  · exact (huniv (lan k f) (lan_monotone k f)).2 (le_lan_comp k f)
  · exact (lan_le_iff k f hL).2 ((huniv L hL).1 le_rfl)
-- @endregion

-- @region kan_extensions.lan_comp_of_embedding
-- @provenance independent
/-- **Kan extension along a fully faithful functor is a genuine extension.** If `k` is an order
embedding (`k c ≤ k c' ↔ c ≤ c'`, the thin version of "fully faithful") and `f` is monotone,
then `lan k f (k c) = f c`: the unit is an isomorphism. The comma category `(k ↓ k c)` then
has the terminal object `c`, and a colimit over a category with a terminal object is the value
there. -/
theorem lan_comp_of_embedding [Preorder C] {k : C → D} (hk : ∀ c c', k c ≤ k c' ↔ c ≤ c') {f : C → E}
    (hf : Monotone f) (c : C) : lan k f (k c) = f c := by
  apply le_antisymm
  · exact iSup₂_le fun c' hc' => hf ((hk c' c).1 hc')
  · exact le_lan_comp k f c
-- @endregion

-- @region kan_extensions.lan_gc
-- @provenance independent
/-- **`Lan_k` is left adjoint to restriction along `k`.** On monotone maps (functors),
`Lan_k ⊣ k^*` where `k^* g = g ∘ k`: this is a Galois connection between the preorders of
functors `C →o E` and `D →o E` (ordered pointwise, i.e. by the existence of natural
transformations). It is `lan_le_iff` read as an adjunction. -/
theorem lan_gc [Preorder C] (k : C →o D) :
    GaloisConnection (fun f : C →o E => (⟨lan k f, lan_monotone k f⟩ : D →o E))
      (fun g : D →o E => g.comp k) := by
  intro f g
  exact lan_le_iff k f g.monotone
-- @endregion

-- @region kan_extensions.ran_monotone
-- @provenance independent
/-- `ran k f` is monotone: if `d ≤ d'`, every `c` with `d' ≤ k c` also has `d ≤ k c`, so the
infimum defining `ran k f d` is taken over a larger family and can only be smaller. -/
theorem ran_monotone (k : C → D) (f : C → E) : Monotone (ran k f) := by
  intro d d' h
  exact le_iInf₂ fun c hc => iInf₂_le_of_le c (h.trans hc) le_rfl
-- @endregion

-- @region kan_extensions.ran_comp_le
-- @provenance independent
/-- The **counit** of the right Kan extension: `(Ran_k f) ∘ k ⇒ f`, i.e.
`ran k f (k c) ≤ f c`, because `c` lies in `(k c ↓ k)`. -/
theorem ran_comp_le (k : C → D) (f : C → E) (c : C) : ran k f (k c) ≤ f c :=
  iInf₂_le_of_le c le_rfl le_rfl
-- @endregion

-- @region kan_extensions.le_ran_iff
-- @provenance independent
/-- The universal property of the **right** Kan extension, dual to `lan_le_iff`: for monotone
`g : D → E`, `g ≤ Ran_k f` if and only if `g ∘ k ≤ f`. -/
theorem le_ran_iff (k : C → D) (f : C → E) {g : D → E} (hg : Monotone g) :
    g ≤ ran k f ↔ ∀ c, g (k c) ≤ f c := by
  constructor
  · intro h c
    exact (h (k c)).trans (ran_comp_le k f c)
  · intro h d
    exact le_iInf₂ fun c hc => (hg hc).trans (h c)
-- @endregion

-- @region kan_extensions.ran_const_eq_iinf
-- @provenance independent
/-- **A limit is a right Kan extension along the functor to the terminal category.** Along
`! : C → Unit`, the comma category `(() ↓ !)` is all of `C`, so `Ran_! f` at the unique object
is `⨅ c, f c`, the infimum — which is the limit of `f` in the complete lattice `E`. -/
theorem ran_const_eq_iInf (f : C → E) : ran (fun _ : C => ()) f () = ⨅ c, f c := by
  simp [ran]
-- @endregion

-- @region kan_extensions.lan_const_eq_isup
-- @provenance independent
/-- Dually, a **colimit is a left Kan extension along `! : C → Unit`**: `Lan_! f () = ⨆ c, f c`. -/
theorem lan_const_eq_iSup (f : C → E) : lan (fun _ : C => ()) f () = ⨆ c, f c := by
  simp [lan]
-- @endregion

end Thin

/-! ### Adjoints as Kan extensions (Mac Lane X.7, thin case) -/

section Adjoint

variable {A X : Type*} [CompleteLattice A] [CompleteLattice X]

-- @region kan_extensions.left_adjoint_eq_ran
-- @provenance independent
/-- **A left adjoint is a right Kan extension of the identity.** If `F ⊣ G` (a Galois
connection `F x ≤ a ↔ x ≤ G a`), then `F = Ran_G id`, i.e.
`F x = ⨅ { a | x ≤ G a }`. In words: `F x` is the best approximation of `x` from above by
things of the form "an `a` with `x ≤ G a`". -/
theorem left_adjoint_eq_ran {F : X → A} {G : A → X} (gc : GaloisConnection F G) :
    F = ran G id := by
  funext x
  apply le_antisymm
  · exact le_iInf₂ fun a hx => (gc x a).2 hx
  · exact iInf₂_le_of_le (F x) (gc.le_u_l x) le_rfl
-- @endregion

-- @region kan_extensions.right_adjoint_eq_lan
-- @provenance independent
/-- Dually, **a right adjoint is a left Kan extension of the identity**: if `F ⊣ G` then
`G = Lan_F id`, i.e. `G a = ⨆ { x | F x ≤ a }` — the best approximation of `a` from below. -/
theorem right_adjoint_eq_lan {F : X → A} {G : A → X} (gc : GaloisConnection F G) :
    G = lan F id := by
  funext a
  apply le_antisymm
  · exact le_iSup₂_of_le (G a) (gc.l_u_le a) le_rfl
  · exact iSup₂_le fun x hx => (gc x a).1 hx
-- @endregion

-- @region kan_extensions.exists_left_adjoint_iff
-- @provenance independent
/-- **Mac Lane's criterion for adjoints, for complete lattices.** A monotone `G : A → X` has a
left adjoint if and only if `G` *preserves* the right Kan extension `Ran_G id`, meaning
`G ∘ Ran_G id = Ran_G G`:
`G (⨅ { a | x ≤ G a }) = ⨅ { G a | x ≤ G a }` for every `x`.
In a complete lattice `Ran_G id` always exists (it is the formula); the content is preservation.
The left adjoint is then `Ran_G id` (see `left_adjoint_eq_ran`). -/
theorem exists_left_adjoint_iff {G : A → X} (hG : Monotone G) :
    (∃ F : X → A, GaloisConnection F G) ↔ ∀ x, G (ran G id x) = ran G G x := by
  constructor
  · rintro ⟨F, gc⟩ x
    rw [← left_adjoint_eq_ran gc]
    apply le_antisymm
    · exact le_iInf₂ fun a hx => hG ((gc x a).2 hx)
    · exact iInf₂_le_of_le (F x) (gc.le_u_l x) le_rfl
  · intro h
    refine ⟨ran G id, fun x a => ⟨fun hxa => ?_, fun hxa => iInf₂_le_of_le a hxa le_rfl⟩⟩
    -- `x ≤ G (Ran_G id x)` because `G` preserves the infimum, and each term is `≥ x`.
    have hx : x ≤ G (ran G id x) := by
      rw [h x]
      exact le_iInf₂ fun _ hc => hc
    exact hx.trans (hG hxa)
-- @endregion

-- @region kan_extensions.exists_left_adjoint_of_map_sinf
-- @provenance independent
/-- **The adjoint functor theorem for complete lattices.** If `G : A → X` preserves all
infima, then `G` has a left adjoint. Preserving all infima includes preserving the particular
infimum `Ran_G id x = ⨅ { a | x ≤ G a }`, so this follows from `exists_left_adjoint_iff`;
monotonicity comes from preserving binary infima. -/
theorem exists_left_adjoint_of_map_sInf {G : A → X}
    (hG : ∀ s : Set A, G (sInf s) = ⨅ a ∈ s, G a) : ∃ F : X → A, GaloisConnection F G := by
  have mono : Monotone G := by
    intro a b hab
    have h := hG {a, b}
    rw [sInf_pair, inf_eq_left.2 hab] at h
    rw [h]
    exact iInf₂_le b (by simp)
  refine (exists_left_adjoint_iff mono).2 fun x => ?_
  have hs : ran G id x = sInf { a | x ≤ G a } := by
    simp [ran, sInf_eq_iInf]
  rw [hs, hG]
  simp [ran]
-- @endregion

end Adjoint

/-! ### Mathlib's general Kan extensions -/

section General

open CategoryTheory CategoryTheory.Limits

-- @region kan_extensions.lan_is_left_adjoint
-- @provenance library
/-- **In general, `Lan_L` is left adjoint to restriction along `L`.** For any functor
`L : C ⥤ D` such that every `F : C ⥤ H` has a left Kan extension along `L`, the functor
`L.lan : (C ⥤ H) ⥤ (D ⥤ H)` is a left adjoint; its right adjoint is precomposition with `L`.
This applies Mathlib's `Functor.lanAdjunction` (with `Adjunction.isLeftAdjoint`). -/
theorem lan_isLeftAdjoint {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) [∀ F : C ⥤ H, L.HasLeftKanExtension F] :
    (L.lan : (C ⥤ H) ⥤ (D ⥤ H)).IsLeftAdjoint :=
  (L.lanAdjunction H).isLeftAdjoint
-- @endregion

-- @region kan_extensions.lan_obj_iso_colimit
-- @provenance library
/-- **The pointwise formula, in general.** If `C` is small, `D` is locally small (its
hom-sets live in the same universe) and `H` has all small colimits, then the left Kan extension
of `F : C ⥤ H` along `L : C ⥤ D` exists and its value at `d` is the colimit of `F` over the
comma category `(L ↓ d)` (`CostructuredArrow L d` in Mathlib).
This applies Mathlib's `Functor.leftKanExtensionObjIsoColimit`; the existence of the colimits
is found by instance search from `HasColimits H`. -/
theorem lan_obj_iso_colimit {C D H : Type*} [SmallCategory C] [Category D] [Category H]
    (L : C ⥤ D) (F : C ⥤ H) (d : D) [HasColimits H] :
    Nonempty ((L.leftKanExtension F).obj d ≅ colimit (CostructuredArrow.proj L d ⋙ F)) :=
  ⟨L.leftKanExtensionObjIsoColimit F d⟩
-- @endregion

end General

end Lumenary.KanExtensions
