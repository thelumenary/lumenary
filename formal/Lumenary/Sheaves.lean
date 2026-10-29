/-
The Lumenary — formal mathematics
Sheaves: presheaves on the open sets of a space, the gluing condition, why constant presheaves
fail it, why continuous functions satisfy it, and why a section of a sheaf is determined by its
germs.

What is proved here and what Mathlib provides. Mathlib develops sheaves on topological spaces
(`TopCat.Presheaf`, `TopCat.Sheaf`) and on general sites, stalks and germs, sheafification and its
adjunction, étale spaces, and subobject classifiers for sheaf categories. The *library*
declarations below cite these. To keep the definitions visible, the *independent* part works with
a small self-contained notion of presheaf of types on `Opens X` with the sheaf condition stated as
"compatible local sections glue uniquely", and proves from it: a sheaf has exactly one section
over the empty set (so constant presheaves with two or more values are not sheaves); continuous
maps into any space form a sheaf (continuity is local); and two sections with the same germ at
every point are equal.

Not formalised here: the equivalence between our `IsSheaf` and Mathlib's (it is
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types`, up to repackaging), sheafification of the
constant presheaf as locally constant functions, and sheaf cohomology.
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.EtaleSpace
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Topos.Sheaf

namespace Lumenary.Sheaves

open TopologicalSpace

universe u v w

/-! ### Presheaves and the sheaf condition -/

-- @region sheaves.presheaf
-- @provenance definition
/-- A **presheaf of sets** on `X`: a set of sections `sec U` for every open `U`, and restriction
maps `sec V → sec U` for `U ⊆ V`, such that restricting to `U` itself does nothing and restricting
in two steps is restricting in one. Equivalently, a functor `O(X)ᵒᵖ → Set`
(Mathlib: `TopCat.Presheaf (Type v) X`). -/
structure Presheaf (X : Type u) [TopologicalSpace X] where
  /-- The sections over each open set. -/
  sec : Opens X → Type v
  /-- Restriction from `V` to a smaller open set `U`. -/
  res : ∀ {U V : Opens X}, U ≤ V → sec V → sec U
  /-- Restricting to the same open set is the identity. -/
  res_id : ∀ (U : Opens X) (s : sec U), res (le_refl U) s = s
  /-- Restriction is transitive: `(s|_V)|_U = s|_U`. -/
  res_res : ∀ {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) (s : sec W),
    res hUV (res hVW s) = res (hUV.trans hVW) s
-- @endregion

variable {X : Type u} [TopologicalSpace X]

-- @region sheaves.is_sheaf
-- @provenance definition
/-- The **sheaf condition**: whenever opens `Uᵢ ⊆ V` cover `V` and sections `sᵢ ∈ F(Uᵢ)` agree
on every overlap `Uᵢ ∩ Uⱼ`, there is exactly one section `t ∈ F(V)` restricting to every `sᵢ`.
"Exactly one" packages both axioms: *gluing* (existence) and *locality* (uniqueness). This is the
statement that `F(V) → ∏ F(Uᵢ) ⇉ ∏ F(Uᵢ ∩ Uⱼ)` is an equaliser. -/
def IsSheaf (F : Presheaf.{u, v} X) : Prop :=
  ∀ (V : Opens X) (ι : Type u) (U : ι → Opens X) (hU : ∀ i, U i ≤ V) (_hcov : V ≤ ⨆ i, U i)
    (s : ∀ i, F.sec (U i)),
    (∀ i j, F.res inf_le_left (s i) = F.res inf_le_right (s j)) →
      ∃! t : F.sec V, ∀ i, F.res (hU i) t = s i
-- @endregion

-- @region sheaves.sec_empty
-- @provenance independent
/-- **A sheaf has exactly one section over the empty set.** The empty set is covered by the empty
family; the compatibility condition is vacuous, so "exactly one gluing" means exactly one section
over `∅`. -/
theorem sec_empty (F : Presheaf.{u, v} X) (hF : IsSheaf F) :
    Nonempty (F.sec ⊥) ∧ ∀ s t : F.sec ⊥, s = t := by
  obtain ⟨t, -, huniq⟩ := hF ⊥ PEmpty (fun i => i.elim) (fun i => i.elim) bot_le
    (fun i => i.elim) (fun i => i.elim)
  exact ⟨⟨t⟩, fun s s' => (huniq s (fun i => i.elim)).trans (huniq s' (fun i => i.elim)).symm⟩
-- @endregion

-- @region sheaves.const_presheaf
-- @provenance definition
/-- The **constant presheaf** with value `A`: every open set, including `∅`, gets the set `A`, and
every restriction map is the identity. -/
def constPresheaf (A : Type v) : Presheaf.{u, v} X where
  sec _ := A
  res _ a := a
  res_id _ _ := rfl
  res_res _ _ _ := rfl
-- @endregion

-- @region sheaves.const_not_sheaf
-- @provenance independent
/-- **Constant presheaves are usually not sheaves.** If `A` has two different elements, the
constant presheaf has two sections over `∅`, but a sheaf has only one. (Even after repairing the
value at `∅`, gluing fails on any disconnected open set; the sheafification is the sheaf of
locally constant functions — see the lesson.) -/
theorem const_not_sheaf (A : Type v) (a b : A) (hab : a ≠ b) :
    ¬ IsSheaf (constPresheaf (X := X) A) := by
  intro hF
  exact hab ((sec_empty _ hF).2 a b)
-- @endregion

/-! ### Continuous functions form a sheaf -/

-- @region sheaves.cont_presheaf
-- @provenance definition
/-- The **presheaf of continuous maps** into a space `Y`: over `U`, the continuous maps `U → Y`;
restriction is restriction of functions. -/
def contPresheaf (Y : Type v) [TopologicalSpace Y] : Presheaf.{u, max u v} X where
  sec U := C(U, Y)
  res h f := f.comp ⟨fun x => ⟨x.1, h x.2⟩, by fun_prop⟩
  res_id _ _ := rfl
  res_res _ _ _ := rfl
-- @endregion

-- @region sheaves.cont_is_sheaf
-- @provenance independent
/-- **Continuous functions form a sheaf: continuity is local.** Compatible continuous maps
`sᵢ : Uᵢ → Y` define a single function on `V = ⋃ Uᵢ` (well defined because they agree on
overlaps), which is continuous because it is continuous near every point; and two functions that
agree on every `Uᵢ` agree on `V`. The gluing is Mathlib's `ContinuousMap.liftCover`. -/
theorem cont_isSheaf (Y : Type v) [TopologicalSpace Y] :
    IsSheaf (contPresheaf (X := X) Y) := by
  intro V ι U hU hcov s hcomp
  -- every point of `V` lies in some `Uᵢ`
  have hmem : ∀ x : V, ∃ i, (x : X) ∈ U i := fun x => by
    simpa [Opens.mem_iSup] using hcov x.2
  -- the pieces `Uᵢ`, seen as subsets of `V`, and the local maps on them
  let S : ι → Set V := fun i => {x | (x : X) ∈ U i}
  let φ : ∀ i, C(S i, Y) := fun i => (s i).comp ⟨fun x => ⟨x.1.1, x.2⟩, by fun_prop⟩
  -- compatibility on overlaps
  have hφ : ∀ i j (x : V) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    exact congrArg (fun f : C((U i ⊓ U j : Opens X), Y) => f ⟨x.1, hxi, hxj⟩) (hcomp i j)
  -- each `Sᵢ` is open in `V`, so the pieces form a neighbourhood cover
  have hS : ∀ x : V, ∃ i, S i ∈ nhds x := fun x => by
    obtain ⟨i, hi⟩ := hmem x
    exact ⟨i, ((U i).isOpen.preimage continuous_subtype_val).mem_nhds hi⟩
  refine ⟨ContinuousMap.liftCover S φ hφ hS, ?_, ?_⟩
  · -- the glued map restricts to each `sᵢ`
    intro i
    refine ContinuousMap.ext (X := U i) (Y := Y) fun x => ?_
    exact ContinuousMap.liftCover_coe (S := S) (φ := φ) (hφ := hφ) (hS := hS) (i := i)
      (⟨⟨x.1, hU i x.2⟩, x.2⟩ : S i)
  · -- any other map with the same restrictions is equal to it
    intro t ht
    refine ContinuousMap.ext (X := V) (Y := Y) fun x => ?_
    obtain ⟨i, hi⟩ := hmem x
    have h1 := congrArg (fun f : C(U i, Y) => f ⟨x.1, hi⟩) (ht i)
    have h2 := ContinuousMap.liftCover_coe (S := S) (φ := φ) (hφ := hφ) (hS := hS) (i := i)
      (⟨x, hi⟩ : S i)
    exact h1.trans h2.symm
-- @endregion

/-! ### Germs -/

-- @region sheaves.same_germ
-- @provenance definition
/-- Two sections over `U` have the **same germ at `x`** if they agree on some smaller open
neighbourhood of `x`. The stalk `F_x` is the set of equivalence classes. -/
def SameGerm (F : Presheaf.{u, v} X) {U : Opens X} (x : X) (s t : F.sec U) : Prop :=
  ∃ (W : Opens X) (hWU : W ≤ U), x ∈ W ∧ F.res hWU s = F.res hWU t
-- @endregion

-- @region sheaves.eq_of_same_germ
-- @provenance independent
/-- **A section of a sheaf is determined by its germs.** If `s, t ∈ F(U)` have the same germ at
every point of `U`, choose for each `x` a neighbourhood `W_x` on which they agree. The `W_x` cover
`U`, and `s` and `t` both glue the compatible family `s|_{W_x}`, so by uniqueness `s = t`. -/
theorem eq_of_sameGerm (F : Presheaf.{u, v} X) (hF : IsSheaf F) {U : Opens X} (s t : F.sec U)
    (h : ∀ x ∈ U, SameGerm F x s t) : s = t := by
  -- choose the neighbourhoods
  choose W hWU hxW heq using fun x : U => h x.1 x.2
  -- the family `s|_{W_x}` is compatible
  have hcomp : ∀ i j : U, F.res inf_le_left (F.res (hWU i) s)
      = F.res inf_le_right (F.res (hWU j) s) := by
    intro i j
    rw [F.res_res, F.res_res]
  -- the `W_x` cover `U`
  have hcov : U ≤ ⨆ x : U, W x := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  obtain ⟨g, -, huniq⟩ := hF U U W hWU hcov (fun x => F.res (hWU x) s) hcomp
  exact (huniq s fun _ => rfl).trans (huniq t fun x => (heq x).symm).symm
-- @endregion

/-! ### What Mathlib provides -/

open CategoryTheory Opposite

-- @region sheaves.functions_is_sheaf
-- @provenance library
/-- In Mathlib's language: the presheaf `U ↦ (U → T)` of *all* functions into a type `T` is a
sheaf. This applies `TopCat.Presheaf.toType_isSheaf`. -/
theorem functions_isSheaf (X : TopCat.{u}) (T : Type u) : (X.presheafToType T).IsSheaf :=
  TopCat.Presheaf.toType_isSheaf X T
-- @endregion

-- @region sheaves.section_ext
-- @provenance library
/-- Mathlib's version of `eq_of_sameGerm`: two sections of a sheaf of sets with equal germs at
every point coincide. This applies `TopCat.Presheaf.section_ext`, where the germ is the canonical
map from sections into the stalk, defined as a colimit. -/
theorem section_ext {X : TopCat.{u}} (F : TopCat.Sheaf (Type u) X) (U : Opens X)
    (s t : F.1.obj (op U))
    (h : ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) :
    s = t :=
  TopCat.Presheaf.section_ext F U s t h
-- @endregion

-- @region sheaves.iso_iff_stalks
-- @provenance library
/-- **A morphism of sheaves is an isomorphism if and only if it is an isomorphism on every
stalk.** This applies Mathlib's `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`. -/
theorem iso_iff_stalks {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1) :=
  TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso f
-- @endregion

-- @region sheaves.sheafification_adjunction
-- @provenance library
/-- **Sheafification is left adjoint to the inclusion of sheaves into presheaves.** This applies
Mathlib's `CategoryTheory.sheafificationAdjunction` for the Grothendieck topology of open covers
of `X`. -/
theorem sheafification_adjunction (X : TopCat.{u}) :
    Nonempty (presheafToSheaf (Opens.grothendieckTopology X) (Type u) ⊣
      sheafToPresheaf (Opens.grothendieckTopology X) (Type u)) :=
  ⟨sheafificationAdjunction _ _⟩
-- @endregion

-- @region sheaves.subobject_classifier
-- @provenance library
/-- **Sheaves form a topos (one axiom of it).** The category of sheaves of sets on `X` has a
subobject classifier — the sheaf `Ω` with `Ω(U)` the set of open subsets of `U`. This applies
Mathlib's instance for sheaves on an essentially small site (in `Mathlib.CategoryTheory.Topos`). -/
theorem subobject_classifier (X : TopCat.{u}) :
    HasSubobjectClassifier (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  inferInstance
-- @endregion

-- @region sheaves.etale_covering
-- @provenance library
/-- **Locally constant sheaves are covering spaces.** If every point has a neighbourhood `U` on
which all germ maps `F(U) → F_y` are bijective (as for the sheaf of locally constant functions),
then the projection from the étale space of `F` to `X` is a covering map. This applies Mathlib's
`TopCat.Presheaf.EtaleSpace.isCoveringMap_base`. -/
theorem etale_covering {X : TopCat.{u}} (F : TopCat.Presheaf (Type u) X)
    (hF : ∀ x, ∃ U : Opens X, x ∈ U ∧ ∀ y (hyU : y ∈ U), Function.Bijective (F.germ U y hyU)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := F)) :=
  TopCat.Presheaf.EtaleSpace.isCoveringMap_base hF
-- @endregion

end Lumenary.Sheaves
