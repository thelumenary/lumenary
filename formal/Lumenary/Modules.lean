/-
The Lumenary — formal mathematics
Modules: exact sequences, free and projective modules, the structure theorem over a PID, and
tensor products that are right exact but not exact.

What is proved here. Independently: the short exact sequence `0 → ℤ --2·--> ℤ → ℤ/2 → 0` is
exact; `ℤ/2` is a `ℤ`-module with no basis (it is not free); maps out of a free module lift along
surjections (the heart of "free ⇒ projective"); and tensoring the injective map `2· : ℤ → ℤ` with
`ℤ/2` gives a map that is not injective, so `− ⊗ ℤ/2` is not exact.

What Mathlib provides. Modules, submodules, quotients and exactness (`Function.Exact`); the
instance "free ⇒ projective" (`Module.Projective.of_free`); the lifting property of projective
modules; "a submodule of a finite free module over a PID is free" (`Submodule.basisOfPid`); the
structure theorem for finitely generated modules over a PID (`Module.equiv_free_prod_directSum`)
and its corollary for abelian groups; the tensor–hom adjunction (`TensorProduct.lift.equiv`) and
right exactness of the tensor product (`rTensor_exact`). Not formalised here: the Smith
normal form algorithm itself (Mathlib has `Submodule.smithNormalForm`), uniqueness of invariant
factors, and the Jordan normal form as a corollary.
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Data.ZMod.Basic

namespace Lumenary.Modules

open TensorProduct

universe u v

/-! ### Exact sequences -/

-- @region modules.int_two_exact
-- @provenance independent
/-- **The short exact sequence `0 → ℤ --2·--> ℤ → ℤ/2 → 0` is exact in the middle**: the image
of multiplication by `2` is exactly the kernel of reduction mod `2`. (Exactness at the ends says
that `2·` is injective and reduction is surjective; both are immediate.) The proof is the
arithmetic fact that an integer reduces to `0` in `ℤ/2` exactly when it is even. -/
theorem int_two_exact :
    Function.Exact (fun n : ℤ => 2 * n) (fun n : ℤ => (n : ZMod 2)) := by
  intro n
  constructor
  · intro h
    have h2 : (2 : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).mp h
    obtain ⟨m, hm⟩ := h2
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_mul]
-- @endregion

/-! ### Modules need not have bases -/

-- @region modules.zmod_two_not_free
-- @provenance independent
/-- **`ℤ/2` is a `ℤ`-module with no basis.** Human proof: suppose `b` were a basis. Since
`ℤ/2 ≠ 0` the basis is non-empty; pick a basis vector `b i`. Then `2 • b i = 0` in `ℤ/2`, a
non-trivial linear relation (the coefficient `2 ≠ 0` in `ℤ`), contradicting linear independence.
So modules, unlike vector spaces, can fail to be free: torsion is the obstruction. -/
theorem zmod_two_not_free : ¬ Module.Free ℤ (ZMod 2) := by
  intro hfree
  let b := Module.Free.chooseBasis ℤ (ZMod 2)
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ (ZMod 2)) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have h1 : (1 : ZMod 2) = 0 := by
      rw [← b.sum_repr (1 : ZMod 2)]
      simp
    exact one_ne_zero h1
  obtain ⟨i⟩ := hne
  have h2 : (2 : ℤ) • b i = 0 := by
    have : ∀ x : ZMod 2, (2 : ℤ) • x = 0 := by decide
    exact this _
  -- a basis vector is never killed by a non-zero scalar
  have key : (2 : ℤ) = 0 := by
    have hli := b.linearIndependent
    rw [LinearIndependent] at hli
    have := hli (a₁ := Finsupp.single i 2) (a₂ := 0)
    simp only [Finsupp.linearCombination_single, map_zero] at this
    have h := this h2
    simpa using congrArg (fun f => f i) h
  exact two_ne_zero key
-- @endregion

/-! ### Free modules are projective -/

-- @region modules.free_lifting
-- @provenance independent
/-- **Maps out of a free module lift along surjections.** Let `g : M → N` be surjective and
`f : R^(ι) → N` a homomorphism from the free module on `ι`. For each basis vector `eᵢ`, choose
`mᵢ ∈ M` with `g mᵢ = f eᵢ` (surjectivity); the universal property of the free module gives a
unique `h` with `h eᵢ = mᵢ`, and `g ∘ h = f` because both agree on the basis. This is exactly why
free modules are projective. -/
theorem free_lifting {R : Type*} [Ring R] {ι M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (f : (ι →₀ R) →ₗ[R] N) : ∃ h : (ι →₀ R) →ₗ[R] M, g ∘ₗ h = f := by
  choose m hm using fun i : ι => hg (f (Finsupp.single i 1))
  refine ⟨Finsupp.linearCombination R m, ?_⟩
  ext i
  simp [hm]
-- @endregion

-- @region modules.projective_of_free
-- @provenance library
/-- **Free modules are projective.** This is Mathlib's instance `Module.Projective.of_free`,
whose proof is the lifting argument of `free_lifting`. -/
theorem projective_of_free {R P : Type*} [Ring R] [AddCommGroup P] [Module R P]
    [Module.Free R P] : Module.Projective R P :=
  Module.Projective.of_free
-- @endregion

-- @region modules.projective_lifting
-- @provenance library
/-- **The lifting property of projective modules**: every map from a projective module to the
target of a surjection lifts through it — equivalently, `Hom(P, −)` carries surjections to
surjections. Mathlib: `Module.projective_lifting_property`. -/
theorem projective_lifting {R P M N : Type*} [Ring R] [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R P]
    (g : M →ₗ[R] N) (f : P →ₗ[R] N) (hg : Function.Surjective g) :
    ∃ h : P →ₗ[R] M, g ∘ₗ h = f :=
  Module.projective_lifting_property g f hg
-- @endregion

/-! ### Modules over a principal ideal domain -/

-- @region modules.submodule_free_pid
-- @provenance library
/-- **Over a PID, submodules of finite free modules are free** (of rank at most the rank of the
ambient module). Mathlib: `Submodule.basisOfPid`, which produces a basis of the submodule indexed
by `Fin n`; the proof is the induction on the rank given in the lesson. -/
theorem submodule_free_pid {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (N : Submodule R M) : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R N) :=
  ⟨(Submodule.basisOfPid b N).1, ⟨(Submodule.basisOfPid b N).2⟩⟩
-- @endregion

-- @region modules.structure_theorem
-- @provenance library
/-- **Structure theorem for finitely generated modules over a PID** (elementary divisor form):
`M ≅ Rⁿ ⊕ ⨁ᵢ R/(pᵢ^eᵢ)` with each `pᵢ` irreducible (prime). Mathlib:
`Module.equiv_free_prod_directSum`. Grouping the prime powers gives the invariant factor form
`R/(d₁) ⊕ ⋯ ⊕ R/(dₖ)` with `d₁ ∣ ⋯ ∣ dₖ` used in the lesson. -/
theorem structure_theorem {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible (p i)) (e : ι → ℕ),
      Nonempty (M ≃ₗ[R] (Fin n →₀ R) × DirectSum ι (fun i => R ⧸ R ∙ p i ^ e i)) :=
  Module.equiv_free_prod_directSum R M
-- @endregion

-- @region modules.abelian_groups
-- @provenance library
/-- **Corollary: finitely generated abelian groups.** Taking `R = ℤ`:
`G ≅ ℤⁿ ⊕ ⨁ᵢ ℤ/pᵢ^eᵢ` with the `pᵢ` prime. Mathlib: `AddCommGroup.equiv_free_prod_directSum_zmod`. -/
theorem abelian_groups (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty (G ≃+ (Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i))) :=
  AddCommGroup.equiv_free_prod_directSum_zmod G
-- @endregion

/-! ### Tensor products -/

-- @region modules.tensor_hom
-- @provenance library
/-- **The tensor–hom adjunction** (one variable at a time): bilinear maps `M × N → P`, that is
linear maps `M → Hom(N, P)`, are the same as linear maps `M ⊗ N → P`, naturally. Mathlib:
`TensorProduct.lift.equiv`. -/
noncomputable def tensor_hom (R M N P : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] :
    (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P) :=
  TensorProduct.lift.equiv (RingHom.id R) M N P
-- @endregion

-- @region modules.tensor_right_exact
-- @provenance library
/-- **Tensoring is right exact**: if `M → N → P → 0` is exact then so is
`M ⊗ Q → N ⊗ Q → P ⊗ Q → 0`. Mathlib: `rTensor_exact` (exactness in the middle) and
`LinearMap.rTensor_surjective` (at the right). The lesson derives it from the tensor–hom
adjunction. -/
theorem tensor_right_exact {R M N P : Type*} (Q : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.rTensor Q) (g.rTensor Q) ∧ Function.Surjective (g.rTensor Q) :=
  ⟨rTensor_exact Q hfg hg, LinearMap.rTensor_surjective Q hg⟩
-- @endregion

-- @region modules.tensor_not_left_exact
-- @provenance independent
/-- **…but not exact.** Multiplication by `2` on `ℤ` is injective, yet after tensoring with
`ℤ/2` it becomes the zero map on `ℤ ⊗ ℤ/2 ≅ ℤ/2 ≠ 0`, so it is no longer injective.
Human proof: on a pure tensor, `(2a) ⊗ b = a ⊗ 2b = a ⊗ 0 = 0`; and `1 ⊗ 1 ≠ 0` because
`n ⊗ b ↦ n • b` is a well-defined map `ℤ ⊗ ℤ/2 → ℤ/2` sending it to `1`. -/
theorem tensor_not_left_exact :
    Function.Injective (2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
      ¬ Function.Injective ((2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ).rTensor (ZMod 2)) := by
  constructor
  · intro a b h
    have h' : 2 * a = 2 * b := by simpa [two_smul, two_mul] using h
    omega
  · intro hinj
    -- the element `1 ⊗ 1` is sent to `2 ⊗ 1 = 1 ⊗ 2 = 0`
    have himg : ((2 • LinearMap.id : ℤ →ₗ[ℤ] ℤ).rTensor (ZMod 2)) ((1 : ℤ) ⊗ₜ (1 : ZMod 2)) = 0 := by
      rw [LinearMap.rTensor_tmul]
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [TensorProduct.smul_tmul]
      have : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
      rw [this, TensorProduct.tmul_zero]
    have hzero : (1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2) = 0 :=
      hinj (himg.trans (map_zero _).symm)
    -- but `1 ⊗ 1` maps to `1 ≠ 0` under `ℤ ⊗ ℤ/2 ≅ ℤ/2`
    have := congrArg (TensorProduct.lid ℤ (ZMod 2)) hzero
    rw [TensorProduct.lid_tmul, map_zero, one_smul] at this
    exact one_ne_zero this
-- @endregion

end Lumenary.Modules
