/-
The Lumenary — formal mathematics
∞-categories as quasi-categories: inner horn filling, nerves of categories, Kan complexes, and
why the nerve of a non-groupoid is a quasi-category but not a Kan complex.

What is proved here. `quasicategory_iff` unfolds Mathlib's definition of a quasi-category;
`nerve_composite_unique` and `groupoid_outer_horn` show what horn filling means in dimension 2
for nerves; `nerve_fin_two_not_kan` proves from the definitions that the nerve of the
two-element poset `0 < 1` is not a Kan complex. Mathlib already provides simplicial sets
(`SSet`), horns `Λ[n, i]`, quasi-categories (`SSet.Quasicategory`), Kan complexes, the nerve of
a category, the theorem that nerves are quasi-categories (via the strict Segal condition), that
Kan complexes are quasi-categories, and the homotopy category functor, left adjoint to the
nerve. Not yet in Mathlib (as far as we know): the Joyal model structure, Joyal's theorem that a
quasi-category is a Kan complex exactly when its homotopy category is a groupoid, limits and
colimits in quasi-categories, the ∞-categorical Yoneda lemma, and comparisons with other models.
-/
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Groupoid

namespace Lumenary.InfinityCategories

open CategoryTheory SSet Simplicial

/-! ### The definition -/

-- @region infinity_categories.quasicategory_iff
-- @provenance independent
/-- **What a quasi-category is.** A simplicial set `S` is a quasi-category exactly when every
*inner* horn `Λ[n, i] ⟶ S` (with `0 < i < n`) extends along the inclusion `Λ[n, i] ⟶ Δ[n]`.
Mathlib's class `SSet.Quasicategory` states this for `n + 2` (inner horns only exist from
dimension 2); here it is unfolded into the form used in the lesson. -/
theorem quasicategory_iff (S : SSet) :
    S.Quasicategory ↔
      ∀ (n : ℕ) (i : Fin (n + 1)) (σ₀ : (Λ[n, i] : SSet) ⟶ S),
        0 < i → i < Fin.last n → ∃ σ : Δ[n] ⟶ S, σ₀ = Λ[n, i].ι ≫ σ := by
  constructor
  · intro hS n i σ₀ h0 hn
    exact Quasicategory.hornFilling h0 hn σ₀
  · intro h
    exact ⟨fun n i σ₀ h0 hn => h (n + 2) i σ₀ h0 hn⟩
-- @endregion

-- @region infinity_categories.kan_is_quasicategory
-- @provenance library
/-- Every Kan complex (all horns fill, inner and outer) is a quasi-category: ∞-groupoids are
special ∞-categories. This is Mathlib's instance in `Mathlib.AlgebraicTopology.Quasicategory.Basic`. -/
theorem kan_is_quasicategory (S : SSet) [KanComplex S] : S.Quasicategory :=
  inferInstance
-- @endregion

/-! ### Nerves of categories -/

-- @region infinity_categories.nerve_is_quasicategory
-- @provenance library
/-- **The nerve of a category is a quasi-category.** Mathlib proves this
(`CategoryTheory.Nerve.quasicategory`) by showing that nerves satisfy the strict Segal
condition: every simplex is determined by its spine of composable arrows. -/
theorem nerve_is_quasicategory (C : Type) [Category C] : (nerve C).Quasicategory :=
  inferInstance
-- @endregion

-- @region infinity_categories.nerve_triangle_iff
-- @provenance library
/-- In the nerve of a category, a 2-simplex with edges `f : x₀ ⟶ x₁`, `g : x₁ ⟶ x₂` and
`h : x₀ ⟶ x₂` (Mathlib's `Edge.CompStruct`) exists exactly when `f ≫ g = h`: a triangle
*witnesses* a composite. This is Mathlib's `CategoryTheory.nerve.nonempty_compStruct_iff`. -/
theorem nerve_triangle_iff {C : Type} [Category C] {x₀ x₁ x₂ : C}
    (f : x₀ ⟶ x₁) (g : x₁ ⟶ x₂) (h : x₀ ⟶ x₂) :
    Nonempty (Edge.CompStruct (nerve.edgeMk f) (nerve.edgeMk g) (nerve.edgeMk h)) ↔
      f ≫ g = h :=
  nerve.nonempty_compStruct_iff f g h
-- @endregion

-- @region infinity_categories.nerve_composite_unique
-- @provenance independent
/-- **Inner horns in a nerve fill uniquely.** Given composable edges `f` and `g` (a horn
`Λ[2, 1]`), there is exactly one edge `h` that can be the third side of a 2-simplex, namely
`f ≫ g`. In a general quasi-category a filler exists but is unique only up to homotopy; nerves
are exactly the simplicial sets whose inner horns fill uniquely. -/
theorem nerve_composite_unique {C : Type} [Category C] {x₀ x₁ x₂ : C}
    (f : x₀ ⟶ x₁) (g : x₁ ⟶ x₂) :
    ∃! h : x₀ ⟶ x₂,
      Nonempty (Edge.CompStruct (nerve.edgeMk f) (nerve.edgeMk g) (nerve.edgeMk h)) := by
  refine ⟨f ≫ g, (nerve_triangle_iff f g (f ≫ g)).2 rfl, fun h hh => ?_⟩
  exact ((nerve_triangle_iff f g h).1 hh).symm
-- @endregion

-- @region infinity_categories.groupoid_outer_horn
-- @provenance independent
/-- **Outer horns in the nerve of a groupoid fill.** Given `f : x₀ ⟶ x₁` and `h : x₀ ⟶ x₂` (a
horn `Λ[2, 0]`), there is exactly one `g : x₁ ⟶ x₂` making a 2-simplex, namely `f⁻¹ ≫ h`. This
is the dimension-2 shadow of the fact that nerves of groupoids are Kan complexes: filling outer
horns is *inverting* arrows. -/
theorem groupoid_outer_horn {G : Type} [Groupoid G] {x₀ x₁ x₂ : G}
    (f : x₀ ⟶ x₁) (h : x₀ ⟶ x₂) :
    ∃! g : x₁ ⟶ x₂,
      Nonempty (Edge.CompStruct (nerve.edgeMk f) (nerve.edgeMk g) (nerve.edgeMk h)) := by
  refine ⟨Groupoid.inv f ≫ h, (nerve_triangle_iff _ _ _).2 (by simp), fun g hg => ?_⟩
  have hfg : f ≫ g = h := (nerve_triangle_iff f g h).1 hg
  rw [← hfg]
  simp
-- @endregion

-- @region infinity_categories.groupoid_outer_horn_right
-- @provenance independent
/-- The other outer horn, `Λ[2, 2]`: in the nerve of a groupoid, given `g : x₁ ⟶ x₂` and
`h : x₀ ⟶ x₂` there is exactly one `f : x₀ ⟶ x₁` making a 2-simplex, namely `h ≫ g⁻¹`. -/
theorem groupoid_outer_horn_right {G : Type} [Groupoid G] {x₀ x₁ x₂ : G}
    (g : x₁ ⟶ x₂) (h : x₀ ⟶ x₂) :
    ∃! f : x₀ ⟶ x₁,
      Nonempty (Edge.CompStruct (nerve.edgeMk f) (nerve.edgeMk g) (nerve.edgeMk h)) := by
  refine ⟨h ≫ Groupoid.inv g, (nerve_triangle_iff _ _ _).2 (by simp), fun f hf => ?_⟩
  have hfg : f ≫ g = h := (nerve_triangle_iff f g h).1 hf
  rw [← hfg]
  simp
-- @endregion

-- @region infinity_categories.nerve_fin_two_not_kan
-- @provenance independent
/-- **A quasi-category that is not a Kan complex**: the nerve of the poset `0 < 1` (the
"walking arrow" `Fin 2`). The horn `Λ[2, 0]` with edges `0 ⟶ 1` (from vertex 0 to vertex 1) and
`𝟙 0` (from vertex 0 to vertex 2) has no filler: the missing edge would be an arrow `1 ⟶ 0`, i.e.
a proof of `1 ≤ 0`. Proof: glue the two edges into a horn (`horn₂₀.isPushout`), fill it using
the Kan property, read off the vertices of the filling 2-simplex from its faces, and apply its
middle-to-last arrow. -/
theorem nerve_fin_two_not_kan : ¬ KanComplex (nerve (Fin 2)) := by
  intro hK
  -- The two edges of the horn: `0 ⟶ 1` and the identity of `0`.
  let e₀₁ : (nerve (Fin 2)) _⦋1⦌ :=
    ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide))
  let e₀₂ : (nerve (Fin 2)) _⦋1⦌ := ComposableArrows.mk₁ (𝟙 (0 : Fin 2))
  -- They share their source vertex 0, so they glue to a map `Λ[2, 0] ⟶ nerve (Fin 2)`.
  have hsrc : (nerve (Fin 2)).δ 1 e₀₁ = (nerve (Fin 2)).δ 1 e₀₂ :=
    ComposableArrows.ext₀ rfl
  obtain ⟨σ, hσ₁, hσ₂⟩ := horn₂₀.isPushout.exists_desc (SSet.yonedaEquiv.symm e₀₁)
    (SSet.yonedaEquiv.symm e₀₂)
    (by rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, hsrc])
  -- The Kan property fills the horn with a 2-simplex `s`.
  obtain ⟨s, hs⟩ := KanComplex.hornFilling σ
  have hs₂ : stdSimplex.δ 2 ≫ s = SSet.yonedaEquiv.symm e₀₁ := by simp [← hσ₁, hs]
  have hs₁ : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm e₀₂ := by simp [← hσ₂, hs]
  obtain ⟨t, rfl⟩ := SSet.yonedaEquiv.symm.surjective s
  rw [stdSimplex.δ_comp_yonedaEquiv_symm] at hs₂ hs₁
  have ht₂ : (nerve (Fin 2)).δ 2 t = e₀₁ := SSet.yonedaEquiv.symm.injective hs₂
  have ht₁ : (nerve (Fin 2)).δ 1 t = e₀₂ := SSet.yonedaEquiv.symm.injective hs₁
  -- Vertex 1 of `t` is `1` (read off face 2) and vertex 2 of `t` is `0` (read off face 1).
  have v₁ : t.obj 1 = 1 := congrArg (fun x : ComposableArrows (Fin 2) 1 => x.obj 1) ht₂
  have v₂ : t.obj 2 = 0 := congrArg (fun x : ComposableArrows (Fin 2) 1 => x.obj 1) ht₁
  -- The arrow of `t` from vertex 1 to vertex 2 would prove `1 ≤ 0`.
  have hle : t.obj 1 ≤ t.obj 2 := leOfHom (t.map' 1 2)
  rw [v₁, v₂] at hle
  exact absurd hle (by decide)
-- @endregion

/-! ### The homotopy category -/

-- @region infinity_categories.nerve_adjunction
-- @provenance definition
/-- The **homotopy category** functor `hoFunctor : SSet ⥤ Cat` is left adjoint to the nerve.
For a quasi-category `S`, `hoFunctor S` has the vertices as objects and homotopy classes of
edges as morphisms; composition is defined by filling inner 2-horns. This is Mathlib's
`CategoryTheory.nerveAdjunction`. -/
noncomputable def nerveAdjunction : hoFunctor ⊣ nerveFunctor :=
  CategoryTheory.nerveAdjunction
-- @endregion

-- @region infinity_categories.ho_nerve_iso
-- @provenance definition
/-- The homotopy category of the nerve of a category is that category again (naturally): the
nerve loses no information, and categories sit inside ∞-categories as a full subcategory. This
is Mathlib's `CategoryTheory.nerveFunctorCompHoFunctorIso`. -/
noncomputable def hoNerveIso : nerveFunctor.{0, 0} ⋙ hoFunctor ≅ 𝟭 Cat :=
  CategoryTheory.nerveFunctorCompHoFunctorIso
-- @endregion

end Lumenary.InfinityCategories
