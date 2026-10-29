/-
The Lumenary — formal mathematics
Representation theory of finite groups: Maschke's theorem and its failure in characteristic
`p`, Schur's lemma, characters as class functions, the orthogonality relations, character tables
of `S₃` and of the groups of order `8`, and Frobenius reciprocity.

What is proved here. Independently: Schur's lemma (a non-zero map between simple modules is an
isomorphism), from the fact that kernels and images are submodules; the failure of Maschke's
theorem over `𝔽₂` — the shear `(x, y) ↦ (x + y, y)` has order `2`, and its invariant line has no
invariant complement; the orthogonality relations for the character table of `S₃` and for the
common character table of the dihedral group `D₄` and the quaternion group `Q₈`; and the fact
that `D₄` and `Q₈` are nevertheless not isomorphic (they have `6` and `2` elements with
`g² = 1`).

What Mathlib provides. `Representation k G V` (a homomorphism `G →* (V →ₗ[k] V)`), finite-
dimensional representations `FDRep k G`, Maschke's theorem (`MonoidAlgebra.Submodule.exists_isCompl`),
Schur's lemma (`LinearMap.bijective_of_ne_zero`, and `FDRep.finrank_hom_simple_simple` over an
algebraically closed field), characters (`Representation.character`, `Representation.char_conj`),
the orthogonality of irreducible characters (`Representation.char_orthonormal`), and induction as
a left adjoint of restriction (`Rep.indResAdjunction`, Frobenius reciprocity). Not formalised here:
that the number of irreducible representations equals the number of conjugacy classes, that the
squares of their dimensions add up to `|G|`, and the identification of the character tables with
the groups (computed in the experiment).
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.ZMod.Basic

namespace Lumenary.RepresentationTheory

open CategoryTheory

/-! ### Schur's lemma -/

-- @region representation_theory.schur
-- @provenance independent
/-- **Schur's lemma.** A non-zero homomorphism between simple modules is bijective. (For
representations of `G` over `k`, take modules over the group algebra `k[G]`.) Human proof: the
kernel of `f` is a submodule of the simple module `M`, so it is `0` or `M`; it is not `M` because
`f ≠ 0`; so `f` is injective. The image is a submodule of the simple module `N`, so it is `0` or
`N`; it is not `0`; so `f` is surjective. -/
theorem schur {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) (hf : f ≠ 0) :
    Function.Bijective f := by
  constructor
  · rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker f) with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf
  · rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range f) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hf
    · exact LinearMap.range_eq_top.mp h
-- @endregion

-- @region representation_theory.schur_library
-- @provenance library
/-- Schur's lemma in Mathlib: `LinearMap.bijective_of_ne_zero`. -/
theorem schur_library {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (hf : f ≠ 0) :
    Function.Bijective f :=
  LinearMap.bijective_of_ne_zero hf
-- @endregion

-- @region representation_theory.schur_dimension
-- @provenance library
/-- **Schur's lemma over an algebraically closed field**: between irreducible finite-dimensional
representations, `dim Hom(V, W)` is `1` if `V ≅ W` and `0` otherwise; in particular every
endomorphism of an irreducible representation is a scalar. Mathlib:
`FDRep.finrank_hom_simple_simple`. -/
theorem schur_dimension {k G : Type} [Field k] [IsAlgClosed k] [Monoid G] (V W : FDRep k G)
    [Simple V] [Simple W] [Decidable (Nonempty (V ≅ W))] :
    Module.finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 := by
  classical
  convert FDRep.finrank_hom_simple_simple V W
-- @endregion

/-! ### Maschke's theorem, and its failure in characteristic `p` -/

-- @region representation_theory.maschke
-- @provenance library
/-- **Maschke's theorem**: if `G` is finite and `|G|` is non-zero in the field `k`, every
subrepresentation of a representation of `G` (a `k[G]`-submodule) has an invariant complement.
Mathlib: `MonoidAlgebra.Submodule.exists_isCompl`, proved by averaging a projection over `G`, as
in the lesson. -/
theorem maschke {k G V : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
    [AddCommGroup V] [Module (MonoidAlgebra k G) V] (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  MonoidAlgebra.Submodule.exists_isCompl p
-- @endregion

-- @region representation_theory.shear
-- @provenance definition
/-- The shear `(x, y) ↦ (x + y, y)` on `𝔽₂²`. -/
def shear : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
  (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2) + LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)).prod
    (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2))
-- @endregion

-- @region representation_theory.shear_sq
-- @provenance independent
/-- Over `𝔽₂` the shear has order `2`: `(x + y + y, y) = (x, y)`. So `1 ↦ id`, `g ↦ shear` is a
representation of the cyclic group of order `2` on `𝔽₂²`. -/
theorem shear_sq : shear ∘ₗ shear = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp only [shear, LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.id_apply]
  revert x y
  decide
-- @endregion

-- @region representation_theory.maschke_fails
-- @provenance independent
/-- **Maschke fails when the characteristic divides `|G|`.** For the representation of the group
of order `2` by the shear on `𝔽₂²`, the invariant line `L = 𝔽₂ · (1, 0)` has no invariant
complement. Human proof: a complement `Q` contains a vector `b = (c, 1)` (since `L + Q` contains
`(0, 1)`); if `Q` were invariant, it would contain `shear b - b = (1, 0)`, which lies in `L`,
contradicting `L ∩ Q = 0`. -/
theorem maschke_fails :
    ¬ ∃ q : Submodule (ZMod 2) (ZMod 2 × ZMod 2),
      IsCompl (Submodule.span (ZMod 2) {((1 : ZMod 2), (0 : ZMod 2))}) q ∧
        ∀ x ∈ q, shear x ∈ q := by
  rintro ⟨q, hc, hq⟩
  have htop : ((0 : ZMod 2), (1 : ZMod 2)) ∈
      Submodule.span (ZMod 2) {((1 : ZMod 2), (0 : ZMod 2))} ⊔ q := by
    rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hb2 : b.2 = 1 := by
    have := congrArg Prod.snd hab
    simpa using this
  have hdiff : shear b - b ∈ q := q.sub_mem (hq b hb) hb
  have hval : shear b - b = ((1 : ZMod 2), (0 : ZMod 2)) := by
    ext
    · simp [shear, hb2]
    · simp [shear]
  have hmem : ((1 : ZMod 2), (0 : ZMod 2)) ∈
      Submodule.span (ZMod 2) {((1 : ZMod 2), (0 : ZMod 2))} ⊓ q :=
    ⟨Submodule.subset_span rfl, hval ▸ hdiff⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at hmem
  have := congrArg Prod.fst hmem
  simp at this
-- @endregion

/-! ### Characters -/

-- @region representation_theory.char_class_function
-- @provenance library
/-- **Characters are class functions**: `χ(h g h⁻¹) = χ(g)`, because the trace is invariant under
conjugation. Mathlib: `Representation.char_conj`. -/
theorem char_class_function {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) (g h : G) :
    ρ.character (h * g * h⁻¹) = ρ.character g :=
  ρ.char_conj g h
-- @endregion

-- @region representation_theory.char_orthonormal
-- @provenance library
/-- **Orthogonality of irreducible characters**: for irreducible representations `ρ, σ` of a
finite group over an algebraically closed field in which `|G|` is invertible,
`(1/|G|) ∑_g χ_ρ(g) χ_σ(g⁻¹)` is `1` if `σ ≅ ρ` and `0` otherwise. Mathlib:
`Representation.char_orthonormal`, proved from Schur's lemma and averaging, as in the lesson. -/
theorem char_orthonormal {k G V W : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsIrreducible] [σ.IsIrreducible]
    [Decidable (Nonempty (σ.Equiv ρ))] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (σ.Equiv ρ) then 1 else 0 := by
  classical
  convert Representation.char_orthonormal ρ σ
-- @endregion

/-! ### Character tables -/

-- @region representation_theory.s3_table
-- @provenance definition
/-- The character table of `S₃`. Rows: the trivial, sign and 2-dimensional (standard)
characters; columns: the classes of the identity (size `1`), the transpositions (size `3`) and
the 3-cycles (size `2`). -/
def s3Table : Fin 3 → Fin 3 → ℤ := ![![1, 1, 1], ![1, -1, 1], ![2, 0, -1]]
-- @endregion

-- @region representation_theory.s3_orthogonality
-- @provenance independent
/-- **Row orthogonality for `S₃`**: `∑_C |C| χᵢ(C) χⱼ(C) = 6 δᵢⱼ` (the characters are real, so no
complex conjugation is needed), and **column orthogonality**: `∑ᵢ χᵢ(C) χᵢ(C') = δ_{CC'} |G|/|C|`.
Checked by evaluation. -/
theorem s3_orthogonality :
    (∀ i j : Fin 3, ∑ c : Fin 3, ![1, 3, 2] c * s3Table i c * s3Table j c =
      if i = j then 6 else 0) ∧
    (∀ c c' : Fin 3, ∑ i : Fin 3, s3Table i c * s3Table i c' =
      if c = c' then 6 / ![1, 3, 2] c else 0) := by
  decide
-- @endregion

-- @region representation_theory.order8_table
-- @provenance definition
/-- The common character table of `D₄` and `Q₈`. Columns: classes of sizes `1, 1, 2, 2, 2`
(for `D₄`: `1`, `r²`, `{r, r³}`, `{s, sr²}`, `{sr, sr³}`; for `Q₈`: `1`, `-1`, `±i`, `±j`, `±k`).
Rows: four 1-dimensional characters and one of degree `2`. -/
def order8Table : Fin 5 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1], ![1, 1, 1, -1, -1], ![1, 1, -1, 1, -1], ![1, 1, -1, -1, 1],
    ![2, -2, 0, 0, 0]]
-- @endregion

-- @region representation_theory.order8_orthogonality
-- @provenance independent
/-- **Row orthogonality for the order-8 table**: `∑_C |C| χᵢ(C) χⱼ(C) = 8 δᵢⱼ`. With
`1 + 1 + 1 + 1 + 2² = 8 = |G|`. Checked by evaluation. -/
theorem order8_orthogonality :
    (∀ i j : Fin 5, ∑ c : Fin 5, ![1, 1, 2, 2, 2] c * order8Table i c * order8Table j c =
      if i = j then 8 else 0) ∧ ∑ i : Fin 5, order8Table i 0 ^ 2 = 8 := by
  decide
-- @endregion

-- @region representation_theory.d4_not_q8
-- @provenance independent
/-- **…but `D₄` and `Q₈` are not isomorphic.** In `D₄` (Mathlib's `DihedralGroup 4`) six elements
satisfy `g² = 1` (the identity, `r²` and four reflections); in `Q₈` (`QuaternionGroup 2`) only
two do (`±1`). An isomorphism would carry one set bijectively onto the other. So the character
table does not determine the group. -/
theorem d4_not_q8 : IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2) := by
  constructor
  intro e
  have hcard : Fintype.card {g : DihedralGroup 4 // g * g = 1} =
      Fintype.card {h : QuaternionGroup 2 // h * h = 1} :=
    Fintype.card_congr (e.toEquiv.subtypeEquiv fun g => by
      change g * g = 1 ↔ e g * e g = 1
      rw [← map_mul, ← map_one e, e.injective.eq_iff])
  have h1 : Fintype.card {g : DihedralGroup 4 // g * g = 1} = 6 := by decide
  have h2 : Fintype.card {h : QuaternionGroup 2 // h * h = 1} = 2 := by decide
  omega
-- @endregion

/-! ### Induced representations -/

-- @region representation_theory.frobenius_reciprocity
-- @provenance library
/-- **Frobenius reciprocity**: induction along a group homomorphism `φ : G →* H` is left adjoint to
restriction, so `Hom_H(Ind A, B) ≅ Hom_G(A, Res B)` naturally. Mathlib: `Rep.indResAdjunction`. -/
theorem frobenius_reciprocity (k : Type) {G H : Type} [CommRing k] [Group G] [Group H]
    (φ : G →* H) : Nonempty (Rep.indFunctor k φ ⊣ Rep.resFunctor φ) :=
  ⟨Rep.indResAdjunction k φ⟩
-- @endregion

end Lumenary.RepresentationTheory
