/-
The Lumenary — formal mathematics
Abelian categories: why monomorphisms that are epimorphisms are isomorphisms, why the free
abelian groups do not form an abelian category, the short five lemma for modules, and Mathlib's
abelian categories, five lemma, snake lemma and Freyd–Mitchell embedding theorem.

What is proved here. Independently: in any abelian category a morphism that is both monic and
epic is an isomorphism (from the axiom "every monomorphism is a kernel"); the arithmetic behind
the counterexample — multiplication by `2` on `ℤ` is injective and not surjective, every pair of
homomorphisms `ℤ → G` into a torsion-free group that agree after `2 ·` are equal (so `2 ·` is an
epimorphism among free abelian groups), while into `ℤ/2` they need not be (so it is not an
epimorphism of abelian groups); and the short five lemma for modules, by element chasing.

What Mathlib provides. `CategoryTheory.Abelian`, the abelian structure on `ModuleCat R` and on
categories of sheaves with values in an abelian category, the five lemma
(`Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`), the snake lemma
(`ShortComplex.SnakeInput.snake_lemma`) and the Freyd–Mitchell embedding theorem
(`Abelian.FreydMitchell.functor`), all in general abelian categories. Not formalised here: the
category of free abelian groups itself (we formalise the maps, not the category), and the
exponential sheaf sequence.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Sheaves.Abelian

namespace Lumenary.AbelianCategories

open CategoryTheory Limits

universe v u w w'

/-! ### Mono + epi = iso -/

section MonoEpi

variable {C : Type u} [Category.{v} C] [Abelian C]

-- @region abelian_categories.is_iso_of_mono_of_epi
-- @provenance independent
/-- **In an abelian category, a morphism that is monic and epic is an isomorphism.**

Human proof. Since `f : X ⟶ Y` is monic and the category is abelian, `f` is the kernel of some
`g : Y ⟶ Z` (Mathlib: `normalMonoOfMono`). Then `f ≫ g = 0 = f ≫ 0`, and `f` is epic,
so `g = 0`. The identity `𝟙 Y` satisfies `𝟙 Y ≫ g = 0`, so by the universal property of the
kernel it factors as `h ≫ f` for some `h : Y ⟶ X`. Finally `(f ≫ h) ≫ f = f ≫ (h ≫ f) = f`, and
cancelling the monomorphism `f` gives `f ≫ h = 𝟙 X`. So `h` is a two-sided inverse.
(Mathlib's one-line version is `isIso_of_mono_of_epi`, valid in any balanced category.) -/
theorem isIso_of_mono_of_epi {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f := by
  let nm := normalMonoOfMono f
  -- `f` is a kernel of `nm.g`; since `f` is epic, `nm.g = 0`.
  have hg : nm.g = 0 := by
    rw [← cancel_epi f, nm.w, comp_zero]
  -- factor the identity through the kernel `f`
  let h : Y ⟶ X := KernelFork.IsLimit.lift' nm.isLimit (𝟙 Y) (by rw [hg, comp_zero]) |>.1
  have hf : h ≫ f = 𝟙 Y :=
    KernelFork.IsLimit.lift' nm.isLimit (𝟙 Y) (by rw [hg, comp_zero]) |>.2
  refine ⟨⟨h, ?_, hf⟩⟩
  rw [← cancel_mono f, Category.assoc, hf, Category.comp_id, Category.id_comp]
-- @endregion

end MonoEpi

/-! ### Free abelian groups: additive, not abelian -/

-- @region abelian_categories.two_mul_injective
-- @provenance independent
/-- Multiplication by `2` on `ℤ` is injective (so it is a monomorphism, also among free abelian
groups: its kernel is `0`). -/
theorem two_mul_injective : Function.Injective (fun n : ℤ => 2 * n) := by
  intro a b h
  simpa using h
-- @endregion

-- @region abelian_categories.two_mul_not_surjective
-- @provenance independent
/-- Multiplication by `2` on `ℤ` is not surjective: `1` is not even. So it is not an isomorphism. -/
theorem two_mul_not_surjective : ¬ Function.Surjective (fun n : ℤ => 2 * n) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  simp only at hn
  omega
-- @endregion

-- @region abelian_categories.two_mul_epi_torsion_free
-- @provenance independent
/-- **Multiplication by `2` is an epimorphism among torsion-free abelian groups** (in particular
among free abelian groups): if two homomorphisms `g, h : ℤ → G` into a torsion-free group agree
after `2 ·`, they are equal. Proof: `2 • g 1 = g 2 = h 2 = 2 • h 1`, so `g 1 = h 1` by
torsion-freeness, and a homomorphism out of `ℤ` is determined by its value at `1`. -/
theorem two_mul_epi_torsion_free {G : Type u} [AddCommGroup G] [IsAddTorsionFree G]
    (g h : ℤ →+ G) (hgh : ∀ n : ℤ, g (2 * n) = h (2 * n)) : g = h := by
  have h2 : (2 : ℕ) • g 1 = (2 : ℕ) • h 1 := by
    have := hgh 1
    rw [mul_one] at this
    rw [← map_nsmul, ← map_nsmul]
    simpa using this
  have h1 : g 1 = h 1 :=
    IsAddTorsionFree.eq_of_nsmul_eq_nsmul_of_addCommute two_ne_zero (AddCommute.all _ _) h2
  exact AddMonoidHom.ext_int h1
-- @endregion

-- @region abelian_categories.two_mul_not_epi_ab
-- @provenance independent
/-- **…but not an epimorphism of abelian groups.** The reduction map `ℤ → ℤ/2` and the zero map
differ, yet agree after multiplication by `2`. So in `Ab` the map `2 ·` is monic but not epic —
consistent with `Ab` being abelian — and its cokernel `ℤ/2` is exactly what the category of free
abelian groups is missing. -/
theorem two_mul_not_epi_ab :
    ∃ g h : ℤ →+ ZMod 2, g ≠ h ∧ ∀ n : ℤ, g (2 * n) = h (2 * n) := by
  refine ⟨Int.castAddHom (ZMod 2), 0, ?_, ?_⟩
  · intro hgh
    have := congrArg (fun φ : ℤ →+ ZMod 2 => φ 1) hgh
    simp at this
  · intro n
    simp only [Int.coe_castAddHom, Int.cast_mul, AddMonoidHom.zero_apply]
    have : ((2 : ℤ) : ZMod 2) = 0 := rfl
    rw [this, zero_mul]
-- @endregion

/-! ### The short five lemma, by element chasing -/

section FiveLemma

variable {R : Type u} [Ring R]
variable {A B D A' B' D' : Type w} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup D']
  [Module R A] [Module R B] [Module R D] [Module R A'] [Module R B'] [Module R D']

-- @region abelian_categories.short_five_injective
-- @provenance independent
/-- **Short five lemma, injectivity half.** Given a commutative diagram of modules
```
A  --f-->  B  --g-->  D
|α         |β         |γ
A' --f'--> B' --g'--> D'
```
with the top row exact at `B`, `f'` injective, and `α`, `γ` injective, the middle map `β` is
injective. Element chase: if `β b = 0` then `γ (g b) = g' (β b) = 0`, so `g b = 0`, so `b = f a`;
then `f' (α a) = β (f a) = 0`, so `α a = 0`, so `a = 0` and `b = 0`. -/
theorem short_five_injective (f : A →ₗ[R] B) (g : B →ₗ[R] D) (f' : A' →ₗ[R] B')
    (g' : B' →ₗ[R] D') (α : A →ₗ[R] A') (β : B →ₗ[R] B') (γ : D →ₗ[R] D')
    (hfg : Function.Exact f g) (hf' : Function.Injective f')
    (comm₁ : ∀ a, β (f a) = f' (α a)) (comm₂ : ∀ b, γ (g b) = g' (β b))
    (hα : Function.Injective α) (hγ : Function.Injective γ) : Function.Injective β := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro b hb
  have hgb : g b = 0 := by
    apply hγ
    rw [comm₂, hb, map_zero, map_zero]
  obtain ⟨a, rfl⟩ := (hfg b).mp hgb
  have ha : α a = 0 := by
    apply hf'
    rw [← comm₁, hb, map_zero]
  have : a = 0 := hα (by rw [ha, map_zero])
  rw [this, map_zero]
-- @endregion

-- @region abelian_categories.short_five_surjective
-- @provenance independent
/-- **Short five lemma, surjectivity half.** In the same diagram, if `g` is surjective, the bottom
row is exact at `B'`, and `α`, `γ` are surjective, then `β` is surjective. Element chase: given
`b'`, write `g' b' = γ d` and `d = g b`; then `g' (b' - β b) = 0`, so `b' - β b = f' a'` with
`a' = α a`, and `b' = β (b + f a)`. -/
theorem short_five_surjective (f : A →ₗ[R] B) (g : B →ₗ[R] D) (f' : A' →ₗ[R] B')
    (g' : B' →ₗ[R] D') (α : A →ₗ[R] A') (β : B →ₗ[R] B') (γ : D →ₗ[R] D')
    (hg : Function.Surjective g) (hfg' : Function.Exact f' g')
    (comm₁ : ∀ a, β (f a) = f' (α a)) (comm₂ : ∀ b, γ (g b) = g' (β b))
    (hα : Function.Surjective α) (hγ : Function.Surjective γ) : Function.Surjective β := by
  intro b'
  obtain ⟨d, hd⟩ := hγ (g' b')
  obtain ⟨b, rfl⟩ := hg d
  have hker : g' (b' - β b) = 0 := by
    rw [map_sub, ← comm₂, hd, sub_self]
  obtain ⟨a', ha'⟩ := (hfg' _).mp hker
  obtain ⟨a, rfl⟩ := hα a'
  refine ⟨b + f a, ?_⟩
  rw [map_add, comm₁, ha', add_sub_cancel]
-- @endregion

end FiveLemma

/-! ### The general theory, from Mathlib -/

-- @region abelian_categories.module_cat_abelian
-- @provenance library
/-- **`R`-modules form an abelian category**, for every ring `R` (Mathlib's instance
`ModuleCat.abelian`): kernels and cokernels are the usual ones, and every monomorphism is the
kernel of its cokernel by the first isomorphism theorem. -/
theorem module_cat_abelian (R : Type u) [Ring R] : Nonempty (Abelian (ModuleCat.{v} R)) :=
  ⟨inferInstance⟩
-- @endregion

-- @region abelian_categories.sheaves_abelian
-- @provenance library
/-- **Sheaves with values in an abelian category form an abelian category**, whenever
sheafification exists (Mathlib's `sheafIsAbelian`). Kernels are computed sectionwise; cokernels
are sheafifications of the presheaf cokernels. This covers sheaves of abelian groups on a
topological space. -/
theorem sheaves_abelian {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (D : Type w) [Category.{w'} D] [Abelian D] [HasSheafify J D] :
    Nonempty (Abelian (Sheaf J D)) :=
  ⟨inferInstance⟩
-- @endregion

-- @region abelian_categories.sheaves_on_space_abelian
-- @provenance library
/-- **Sheaves of abelian groups on a topological space `X` form an abelian category**
(Mathlib's instance `TopCat.Sheaf.instAbelian`, a special case of the previous theorem). -/
theorem sheaves_on_space_abelian (X : TopCat.{u}) :
    Nonempty (Abelian (TopCat.Sheaf AddCommGrpCat.{u} X)) :=
  ⟨inferInstance⟩
-- @endregion

section General

variable {C : Type u} [Category.{v} C] [Abelian C]

-- @region abelian_categories.five_lemma
-- @provenance library
/-- **The five lemma** in an arbitrary abelian category (Mathlib's
`Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`). The rows are exact sequences of length five
(`ComposableArrows C 4`), `φ` is a morphism between them (a commutative ladder), and if the
outer maps are epi, iso, iso, mono, then the middle map is an isomorphism. -/
theorem five_lemma {R₁ R₂ : ComposableArrows C 4} (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (φ : R₁ ⟶ R₂) (h₀ : Epi (ComposableArrows.app' φ 0))
    (h₁ : IsIso (ComposableArrows.app' φ 1)) (h₃ : IsIso (ComposableArrows.app' φ 3))
    (h₄ : Mono (ComposableArrows.app' φ 4)) : IsIso (ComposableArrows.app' φ 2) :=
  Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ φ h₀ h₁ h₃ h₄
-- @endregion

-- @region abelian_categories.snake_lemma
-- @provenance library
/-- **The snake lemma** in an arbitrary abelian category (Mathlib's
`ShortComplex.SnakeInput.snake_lemma`). A `SnakeInput` packages the commutative diagram with
exact rows and the kernels and cokernels of the vertical maps; the conclusion is that the
six-term sequence `ker α → ker β → ker γ --δ--> coker α → coker β → coker γ` is exact. -/
theorem snake_lemma (S : ShortComplex.SnakeInput C) : S.composableArrows.Exact :=
  S.snake_lemma
-- @endregion

-- @region abelian_categories.freyd_mitchell
-- @provenance library
/-- **The Freyd–Mitchell embedding theorem** (Mathlib's `Abelian.FreydMitchell.functor`, proved
by Markus Himmel in 2025). Every abelian category `C` admits a full, faithful, exact functor into
the category of modules over some ring. Classically `C` must be small; Mathlib handles a
locally small `C` by letting the ring live in the larger universe `max u v`. -/
theorem freyd_mitchell :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : C ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  ⟨Abelian.FreydMitchell.EmbeddingRing C, inferInstance, Abelian.FreydMitchell.functor C,
    inferInstance, inferInstance, inferInstance, inferInstance⟩
-- @endregion

end General

end Lumenary.AbelianCategories
