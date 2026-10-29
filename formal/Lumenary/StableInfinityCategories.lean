/-
The Lumenary — formal mathematics
Stable ∞-categories: why stability is invisible to ordinary categories, and the triangulated
shadow that a stable ∞-category leaves on its homotopy category.

What is proved here. In any ordinary category with a zero object, the "loop" pullback
`0 ×_X 0` and the "suspension" pushout `0 ⊔_X 0` are both zero (`loop_square_isPullback`,
`suspension_square_isPushout`). Hence if fibre sequences were always cofibre sequences, every
object would be zero (`stable_one_category_trivial`): stability needs the higher homotopies of
an ∞-category. We also prove a small fact about distinguished triangles by rotation.
Mathlib provides pretriangulated and triangulated categories (Verdier's axioms), the homotopy
category of complexes and the derived category as triangulated categories; the library
declarations below point to them. Not in Mathlib (as far as we know): stable ∞-categories,
spectra as an ∞-category, or the theorem that the homotopy category of a stable ∞-category is
triangulated.
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic

namespace Lumenary.StableInfinityCategories

open CategoryTheory Limits ZeroObject

/-! ### Loops and suspensions in an ordinary category are trivial -/

section OneCategory

variable {C : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]

-- @region stable_infinity_categories.loop_square_is_pullback
-- @provenance independent
/-- In an ordinary category with a zero object, the **loop object** `ΩX = 0 ×_X 0` is zero:
the square with three corners `0` and fourth corner `X` is a pullback. Proof: a cone over
`0 ⟶ X ⟵ 0` is an object `W` with two maps `W ⟶ 0`; there is exactly one map `W ⟶ 0`, and it
factors both legs because all maps into a zero object are equal. In a stable ∞-category,
by contrast, `ΩX` is the shift `X[-1]`, and the square commutes only *via a homotopy*, which
is where the information lives. -/
theorem loop_square_isPullback (X : C) :
    IsPullback (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ X) (0 : (0 : C) ⟶ X) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0)
    (by simp)) ?_
  refine PullbackCone.IsLimit.mk _ (fun _ => 0) ?_ ?_ ?_
  · intro s; exact (isZero_zero C).eq_of_tgt _ _
  · intro s; exact (isZero_zero C).eq_of_tgt _ _
  · intro s m _ _; exact (isZero_zero C).eq_of_tgt _ _
-- @endregion

-- @region stable_infinity_categories.suspension_square_is_pushout
-- @provenance independent
/-- Dually, the **suspension** `ΣX = 0 ⊔_X 0` of an object of an ordinary category with a zero
object is zero: the square with corner `X` and three corners `0` is a pushout. (All maps out
of a zero object are equal.) In a stable ∞-category `ΣX` is the shift `X[1]`. -/
theorem suspension_square_isPushout (X : C) :
    IsPushout (0 : X ⟶ (0 : C)) (0 : X ⟶ (0 : C)) (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) := by
  refine IsPushout.of_isColimit (c := PushoutCocone.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0)
    (by simp)) ?_
  refine PushoutCocone.IsColimit.mk _ (fun _ => 0) ?_ ?_ ?_
  · intro s; exact (isZero_zero C).eq_of_src _ _
  · intro s; exact (isZero_zero C).eq_of_src _ _
  · intro s m _ _; exact (isZero_zero C).eq_of_src _ _
-- @endregion

-- @region stable_infinity_categories.is_zero_of_loop_square_is_pushout
-- @provenance independent
/-- If the loop square of `X` (three corners `0`, fourth corner `X`) were also a **pushout**,
then `X` would be zero. Proof: the maps `𝟙 X` and `0 : X ⟶ X` agree after both legs `0 ⟶ X`
(maps out of `0` are all equal), so by the uniqueness half of the pushout property they are
equal; and `𝟙 X = 0` means `X` is a zero object. -/
theorem isZero_of_loop_square_isPushout (X : C)
    (h : IsPushout (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ X) (0 : (0 : C) ⟶ X)) :
    IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact h.hom_ext ((isZero_zero C).eq_of_src _ _) ((isZero_zero C).eq_of_src _ _)
-- @endregion

-- @region stable_infinity_categories.stable_one_category_trivial
-- @provenance independent
/-- **No non-trivial ordinary category is stable.** Suppose that in a category with a zero object
every *fibre sequence* is a *cofibre sequence*: every pullback square
`P ⟶ 0, P ⟶ B, 0 ⟶ Z, B ⟶ Z` is also a pushout square. Then every object is zero. Proof: apply
the hypothesis to the loop square of `X`, which is a pullback (`loop_square_isPullback`), and
conclude with `isZero_of_loop_square_isPushout`. Since limits and colimits in the nerve of an
ordinary category are its ordinary limits and colimits, this is why stable ∞-categories must be
genuinely higher-categorical. -/
theorem stable_one_category_trivial
    (fib_is_cofib : ∀ {P B Z : C} (snd : P ⟶ B) (g : B ⟶ Z),
      IsPullback (0 : P ⟶ 0) snd (0 : 0 ⟶ Z) g → IsPushout (0 : P ⟶ 0) snd (0 : 0 ⟶ Z) g)
    (X : C) : IsZero X :=
  isZero_of_loop_square_isPushout X (fib_is_cofib _ _ (loop_square_isPullback X))
-- @endregion

end OneCategory

/-! ### The triangulated shadow -/

section Triangulated

open Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

-- @region stable_infinity_categories.cone_fill_exists
-- @provenance library
/-- Verdier's axiom TR3, as stated in Mathlib's class `CategoryTheory.Pretriangulated`
(`complete_distinguished_triangle_morphism`): a commutative square between the first two
terms of two distinguished triangles extends to a morphism of triangles. The axiom says
*there exists* a third map `c`; it says nothing about uniqueness, and in general `c` is not
unique. This is the "non-functoriality of cones" that stable ∞-categories repair. -/
theorem cone_fill_exists (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C) (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ T₂.mor₃ :=
  complete_distinguished_triangle_morphism T₁ T₂ h₁ h₂ a b comm
-- @endregion

-- @region stable_infinity_categories.comp_zero_12
-- @provenance library
/-- In a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`, the composite of the first two maps is zero.
(In the stable ∞-category, the composite is not just zero but *null-homotopic via a chosen
homotopy*, which is part of the data of the fibre sequence.) This is Mathlib's
`CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`. -/
theorem comp_zero_12 (T : Triangle C) (hT : T ∈ distTriang C) : T.mor₁ ≫ T.mor₂ = 0 :=
  comp_distTriang_mor_zero₁₂ T hT
-- @endregion

-- @region stable_infinity_categories.comp_zero_23
-- @provenance independent
/-- The composite of the second and third maps of a distinguished triangle is zero too. Proof by
**rotation**: the rotated triangle `Y ⟶ Z ⟶ X[1] ⟶ Y[1]` is distinguished, and its first two
maps are the second and third maps of the original one. (Mathlib also has this as
`comp_distTriang_mor_zero₂₃`.) -/
theorem comp_zero_23 (T : Triangle C) (hT : T ∈ distTriang C) : T.mor₂ ≫ T.mor₃ = 0 :=
  comp_distTriang_mor_zero₁₂ T.rotate (rot_of_distTriang T hT)
-- @endregion

-- @region stable_infinity_categories.coyoneda_exact
-- @provenance library
/-- Maps into a distinguished triangle give exact sequences: if `f : W ⟶ Y` becomes zero in
`Z`, it lifts to `X`. In a stable ∞-category this is the shadow (on `π₀` of mapping spaces) of
the long exact sequence of homotopy groups of a fibre sequence of spectra. This is Mathlib's
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`. -/
theorem coyoneda_exact (T : Triangle C) (hT : T ∈ distTriang C) {W : C} (f : W ⟶ T.obj₂)
    (hf : f ≫ T.mor₂ = 0) : ∃ g : W ⟶ T.obj₁, f = g ≫ T.mor₁ :=
  Triangle.coyoneda_exact₂ T hT f hf
-- @endregion

end Triangulated

-- @region stable_infinity_categories.derived_triangulated
-- @provenance library
/-- The derived category `D(A)` of an abelian category is triangulated (Verdier's axioms,
including the octahedral axiom). In the ∞-categorical picture, `D(A)` is the homotopy category of
the stable derived ∞-category. This is Mathlib's instance in
`Mathlib.Algebra.Homology.DerivedCategory.Basic`. -/
theorem derived_triangulated (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A] :
    IsTriangulated (DerivedCategory A) :=
  inferInstance
-- @endregion

end Lumenary.StableInfinityCategories
