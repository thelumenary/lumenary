/-
The Lumenary — formal mathematics
Triangulated categories: Verdier's axioms, long exact Hom sequences, split monomorphisms,
and t-structures.

Mathlib defines pretriangulated categories (`CategoryTheory.Pretriangulated`, axioms TR1–TR3
with the rotation axiom), the octahedral axiom (`CategoryTheory.IsTriangulated`), the
triangulated structures on the homotopy category `K(A)` and the derived category `D(A)`, and
t-structures (`Triangulated.TStructure`, with the canonical one on `D(A)`). Here we derive,
from the axioms alone, the first consequences every learner should be able to prove: the
composite of two consecutive maps in a distinguished triangle vanishes, `Hom(W, -)` is exact
in the middle, every monomorphism and every epimorphism splits (which is why a triangulated
category is almost never abelian), and maps from an object of the heart to a negative shift of
another vanish. Not yet in Mathlib (at this version): the theorem of Beilinson, Bernstein and
Deligne that the heart of a t-structure is abelian, and the identification of `A` with the
heart of the canonical t-structure on `D(A)`.
-/
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory Limits Pretriangulated ZeroObject

namespace Lumenary.TriangulatedCategories

universe v u

section Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

-- @region triangulated_categories.comp_zero_of_distinguished
-- @provenance independent
/-- In a distinguished triangle `X → Y → Z → X[1]` the composite `X → Y → Z` is zero.
Proof from the axioms: the triangle `X = X → 0 → X[1]` is distinguished (TR1), and the square
`(𝟙 X, f)` from it to our triangle commutes, so TR3 gives `c : 0 → Z` with `g ∘ f = c ∘ 0 = 0`.
(Mathlib: `Pretriangulated.comp_distTriang_mor_zero₁₂`.) -/
theorem comp_zero_of_distinguished (T : Triangle C) (hT : T ∈ distTriang C) :
    T.mor₁ ≫ T.mor₂ = 0 := by
  have h₀ : Triangle.mk (𝟙 T.obj₁) (0 : T.obj₁ ⟶ 0) 0 ∈ distTriang C :=
    contractible_distinguished T.obj₁
  obtain ⟨c, hc₁, _⟩ := complete_distinguished_triangle_morphism _ T h₀ hT
    (𝟙 T.obj₁) T.mor₁ (by simp)
  rw [← hc₁]
  exact zero_comp
-- @endregion

-- @region triangulated_categories.hom_exact_middle
-- @provenance independent
/-- `Hom(W, -)` is exact in the middle on a distinguished triangle `X → Y → Z → X[1]`:
a map `φ : W → Y` with `g ∘ φ = 0` factors through `f : X → Y`.
Proof: compare the distinguished triangle `W = W → 0 → W[1]` with ours using `(φ, 0)` on the
last two vertices; TR3 (in its rotated form `complete_distinguished_triangle_morphism₁`)
supplies `ψ : W → X` with `f ∘ ψ = φ ∘ 𝟙 = φ`.
(Mathlib: `Pretriangulated.Triangle.coyoneda_exact₂`.) -/
theorem hom_exact_middle (T : Triangle C) (hT : T ∈ distTriang C) {W : C}
    (φ : W ⟶ T.obj₂) (hφ : φ ≫ T.mor₂ = 0) : ∃ ψ : W ⟶ T.obj₁, ψ ≫ T.mor₁ = φ := by
  have h₀ : Triangle.mk (𝟙 W) (0 : W ⟶ 0) 0 ∈ distTriang C := contractible_distinguished W
  obtain ⟨a, ha₁, _⟩ := complete_distinguished_triangle_morphism₁ _ T h₀ hT φ 0
    (by simp [hφ])
  exact ⟨a, by simpa using ha₁.symm⟩
-- @endregion

-- @region triangulated_categories.connecting_map_eq_zero_of_mono
-- @provenance independent
/-- If `f : X → Y` in a distinguished triangle `X → Y → Z → X[1]` is a monomorphism, the
connecting map `h : Z → X[1]` is zero. Proof: `f[1] ∘ h = 0` (two consecutive maps of the
rotated triangle), and `f[1]` is again a monomorphism because `[1]` is an equivalence. -/
theorem connecting_map_eq_zero_of_mono (T : Triangle C) (hT : T ∈ distTriang C) [Mono T.mor₁] :
    T.mor₃ = 0 := by
  have h : T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ T hT
  rw [← cancel_mono (T.mor₁⟦(1 : ℤ)⟧'), h, zero_comp]
-- @endregion

-- @region triangulated_categories.exists_retraction_of_mono
-- @provenance independent
/-- If `f : X → Y` in a distinguished triangle is a monomorphism, it has a retraction
`r : Y → X` with `r ∘ f = 𝟙`. Proof: the connecting map vanishes
(`connecting_map_eq_zero_of_mono`), so in the rotated-back triangle `Z[-1] → X → Y → Z` the
first map is zero; then `𝟙 X` kills it and, by exactness of `Hom(-, X)` (Mathlib's
`Triangle.yoneda_exact₂`), factors through `f`. -/
theorem exists_retraction_of_mono (T : Triangle C) (hT : T ∈ distTriang C) [Mono T.mor₁] :
    ∃ r : T.obj₂ ⟶ T.obj₁, T.mor₁ ≫ r = 𝟙 T.obj₁ := by
  have h3 : T.mor₃ = 0 := connecting_map_eq_zero_of_mono T hT
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT)
    (𝟙 T.obj₁) (by simp [h3]; exact zero_comp)
  exact ⟨r, hr.symm⟩
-- @endregion

-- @region triangulated_categories.is_split_mono_of_mono
-- @provenance independent
/-- **Every monomorphism in a (pre)triangulated category is split.** Complete `f` to a
distinguished triangle (TR1) and apply `exists_retraction_of_mono`. -/
theorem isSplitMono_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have : Mono (Triangle.mk f g h).mor₁ := by simpa using (inferInstance : Mono f)
  obtain ⟨r, hr⟩ := exists_retraction_of_mono _ hT
  exact IsSplitMono.mk' ⟨r, hr⟩
-- @endregion

-- @region triangulated_categories.is_split_epi_of_epi
-- @provenance independent
/-- **Every epimorphism in a (pre)triangulated category is split.** Complete `f : X → Y` to a
distinguished triangle `X → Y → Z → X[1]`. Since `g ∘ f = 0` and `f` is epi, `g = 0`; so
`𝟙 Y` satisfies `g ∘ 𝟙 = 0` and factors through `f` by `hom_exact_middle`. -/
theorem isSplitEpi_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hg : g = 0 := by
    rw [← cancel_epi f, comp_zero]
    exact comp_zero_of_distinguished _ hT
  obtain ⟨s, hs⟩ := hom_exact_middle _ hT (𝟙 Y) (by simp [hg])
  exact IsSplitEpi.mk' ⟨s, hs⟩
-- @endregion

-- @region triangulated_categories.regular_of_epi_mono
-- @provenance independent
/-- If `f = m ∘ e` with `e` epi and `m` mono (an image factorisation, which every morphism of an
abelian category has), then `f` is *von Neumann regular*: `f ∘ g ∘ f = f` for some `g`.
Proof: `e` has a section `s` and `m` a retraction `r`; take `g = s ∘ r`. This is the heart of
the argument that a triangulated category which is abelian must be semisimple. -/
theorem regular_of_epi_mono {X Y I : C} (f : X ⟶ Y) (e : X ⟶ I) (m : I ⟶ Y) [Epi e] [Mono m]
    (hf : e ≫ m = f) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  obtain ⟨⟨s, hs⟩⟩ := (isSplitEpi_of_epi e).exists_splitEpi
  obtain ⟨⟨r, hr⟩⟩ := (isSplitMono_of_mono m).exists_splitMono
  refine ⟨r ≫ s, ?_⟩
  subst hf
  calc (e ≫ m) ≫ (r ≫ s) ≫ e ≫ m = e ≫ (m ≫ r) ≫ (s ≫ e) ≫ m := by
        simp only [Category.assoc]
    _ = e ≫ m := by rw [hr, hs]; simp
-- @endregion

-- @region triangulated_categories.five_lemma
-- @provenance library
/-- The triangulated five lemma: in a morphism of distinguished triangles, if the first and
third components are isomorphisms, so is the second. This applies Mathlib's
`Pretriangulated.isIso₂_of_isIso₁₃`. -/
theorem five_lemma {T T' : Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ :=
  isIso₂_of_isIso₁₃ φ hT hT' h₁ h₃
-- @endregion

-- @region triangulated_categories.cone_unique_up_to_iso
-- @provenance library
/-- Two distinguished triangles on isomorphic morphisms are isomorphic, compatibly with the
given isomorphism of arrows: the cone is unique up to isomorphism. The isomorphism of third
vertices is *not* unique — the source of the non-functoriality of cones. This applies Mathlib's
`Pretriangulated.exists_iso_of_arrow_iso` (proved with TR3 and the five lemma). -/
theorem cone_unique_up_to_iso (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e : Arrow.mk T₁.mor₁ ≅ Arrow.mk T₂.mor₁) :
    ∃ e' : T₁ ≅ T₂, e'.hom.hom₁ = e.hom.left ∧ e'.hom.hom₂ = e.hom.right :=
  exists_iso_of_arrow_iso T₁ T₂ hT₁ hT₂ e
-- @endregion

-- @region triangulated_categories.heart_hom_neg_shift_eq_zero
-- @provenance independent
/-- For a t-structure `t` and objects `A`, `B` of its heart, every map `A → B[-1]` is zero:
"negative Ext groups vanish in the heart". Proof: `B` is `≥ 0`, so `B[-1]` is `≥ 1` (shift
axiom), while `A` is `≤ 0`; the orthogonality axiom `Hom(D^{≤0}, D^{≥1}) = 0` finishes. -/
theorem heart_hom_neg_shift_eq_zero (t : Triangulated.TStructure C) {A B : C}
    (hA : t.heart A) (hB : t.heart B) (f : A ⟶ B⟦(-1 : ℤ)⟧) : f = 0 := by
  rw [Triangulated.TStructure.mem_heart_iff] at hA hB
  have hB' : t.ge 1 (B⟦(-1 : ℤ)⟧) := t.ge_shift 0 (-1) 1 (by norm_num) B hB.2.ge
  exact t.zero' f hA.1.le hB'
-- @endregion

end Pretriangulated

-- @region triangulated_categories.homotopy_category_triangulated
-- @provenance library
/-- The homotopy category `K(A)` of cochain complexes in an additive category is triangulated:
distinguished triangles are those isomorphic to mapping-cone triangles, and the octahedral
axiom holds. This is Mathlib's instance for `HomotopyCategory C (ComplexShape.up ℤ)`. -/
theorem homotopy_category_triangulated (A : Type u) [Category.{v} A] [Preadditive A]
    [HasZeroObject A] [HasBinaryBiproducts A] :
    IsTriangulated (HomotopyCategory A (ComplexShape.up ℤ)) :=
  inferInstance
-- @endregion

-- @region triangulated_categories.derived_category_triangulated
-- @provenance library
/-- The derived category `D(A)` of an abelian category is triangulated. Mathlib deduces this
from the triangulated structure on `K(A)` by Verdier localisation at the acyclic complexes. -/
theorem derived_category_triangulated (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] : IsTriangulated (DerivedCategory A) :=
  inferInstance
-- @endregion

-- @region triangulated_categories.two_not_regular
-- @provenance independent
/-- Multiplication by `2` on `ℤ` is not von Neumann regular: there is no integer `g` with
`2 · g · 2 = 2`. Combined with `regular_of_epi_mono`, and the fact that `Hom_{D(Ab)}(ℤ, ℤ) = ℤ`,
this shows that `D(Ab)` is not an abelian category. -/
theorem two_not_regular : ¬ ∃ g : ℤ, 2 * g * 2 = 2 := by
  rintro ⟨g, hg⟩
  omega
-- @endregion

end Lumenary.TriangulatedCategories
