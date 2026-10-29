/-
The Lumenary — formal mathematics
Algebraic topology: chain complexes, cycles and boundaries, chain homotopies, the
Euler–Poincaré formula, the cellular homology of ℝP², and the functorial "no retraction"
argument behind the Brouwer fixed-point theorem.

What is proved here and what Mathlib provides. Mathlib defines simplicial objects, the
alternating face map complex (whose differential squares to zero), singular chain complexes and
singular homology of topological spaces, and — very recently — proves that homotopic maps induce
equal maps on singular homology. The *library* declarations below cite these. The *independent*
declarations prove the algebraic heart of the lesson from first principles, with a small
self-contained notion of chain complex of abelian groups: boundaries are cycles, chain maps
preserve boundaries, chain-homotopic maps agree on homology, the Euler characteristic of a
two-dimensional complex of vector spaces equals the alternating sum of its Betti numbers, the
cellular differentials of ℝP² give torsion with ℤ-coefficients but not with ℤ/2-coefficients,
and no functor can turn a retraction onto `A` into a zero object unless it already kills `A`.

Not formalised here: the computation `Hₙ(Sⁿ) ≅ ℤ` (Mathlib has no Mayer–Vietoris sequence or
excision for singular homology yet), cellular homology of CW complexes, cup products, and the
Lefschetz fixed-point theorem.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Data.ZMod.QuotientGroup

namespace Lumenary.AlgebraicTopology

/-! ### A minimal chain complex of abelian groups -/

-- @region algebraic_topology.chain_cx
-- @provenance definition
/-- A chain complex of abelian groups, graded by `ℕ`: groups `C n` and boundary maps
`d n : C (n + 1) → C n` with `d ∘ d = 0`. (Mathlib's general notion is `ChainComplex V ℕ` for
any preadditive category `V`; this small version keeps every element visible.) -/
structure ChainCx where
  /-- The group of `n`-chains. -/
  C : ℕ → Type
  /-- Each `C n` is an abelian group. -/
  [grp : ∀ n, AddCommGroup (C n)]
  /-- The boundary map from `(n + 1)`-chains to `n`-chains. -/
  d : ∀ n, C (n + 1) →+ C n
  /-- The boundary of a boundary is zero. -/
  d_d : ∀ n (x : C (n + 2)), d n (d (n + 1) x) = 0
-- @endregion

attribute [instance] ChainCx.grp

-- @region algebraic_topology.is_cycle
-- @provenance definition
/-- An `n`-chain is a **cycle** if its boundary vanishes. Every `0`-chain is a cycle. -/
def IsCycle (K : ChainCx) : ∀ n, K.C n → Prop
  | 0, _ => True
  | n + 1, z => K.d n z = 0
-- @endregion

-- @region algebraic_topology.is_boundary
-- @provenance definition
/-- An `n`-chain is a **boundary** if it is `d` of some `(n + 1)`-chain. Homology is
"cycles modulo boundaries". -/
def IsBoundary (K : ChainCx) (n : ℕ) (z : K.C n) : Prop :=
  ∃ y : K.C (n + 1), K.d n y = z
-- @endregion

-- @region algebraic_topology.boundary_is_cycle
-- @provenance independent
/-- Every boundary is a cycle: this is exactly `d ∘ d = 0`, and it is what makes
"cycles modulo boundaries" meaningful. -/
theorem boundary_isCycle (K : ChainCx) (n : ℕ) (z : K.C n) (hz : IsBoundary K n z) :
    IsCycle K n z := by
  obtain ⟨y, rfl⟩ := hz
  cases n with
  | zero => trivial
  | succ n => exact K.d_d n y
-- @endregion

-- @region algebraic_topology.chain_map
-- @provenance definition
/-- A **chain map** `f : K → L` is a family of homomorphisms commuting with the boundary maps.
Continuous maps of spaces induce chain maps on singular chains. -/
structure ChainMap (K L : ChainCx) where
  /-- The component in degree `n`. -/
  f : ∀ n, K.C n →+ L.C n
  /-- `d ∘ f = f ∘ d`. -/
  comm : ∀ n (x : K.C (n + 1)), L.d n (f (n + 1) x) = f n (K.d n x)
-- @endregion

-- @region algebraic_topology.chain_map_boundary
-- @provenance independent
/-- A chain map sends boundaries to boundaries (`f (d y) = d (f y)`), so it induces a
homomorphism on homology. -/
theorem chainMap_boundary {K L : ChainCx} (φ : ChainMap K L) (n : ℕ) (z : K.C n)
    (hz : IsBoundary K n z) : IsBoundary L n (φ.f n z) := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨φ.f (n + 1) y, φ.comm n y⟩
-- @endregion

-- @region algebraic_topology.chain_homotopy
-- @provenance definition
/-- A **chain homotopy** between chain maps `f, g : K → L` is a family `h n : K.C n → L.C (n+1)`
with `f - g = d h + h d` (in degree `0`, simply `f - g = d h`). The prism operator of the lesson
is a chain homotopy between the maps induced by homotopic continuous maps. -/
structure ChainHomotopy {K L : ChainCx} (φ ψ : ChainMap K L) where
  /-- The homotopy operator, raising degree by one. -/
  h : ∀ n, K.C n →+ L.C (n + 1)
  /-- `f - g = d h` in degree `0`. -/
  zero : ∀ x : K.C 0, φ.f 0 x - ψ.f 0 x = L.d 0 (h 0 x)
  /-- `f - g = d h + h d` in degree `n + 1`. -/
  succ : ∀ n (x : K.C (n + 1)),
    φ.f (n + 1) x - ψ.f (n + 1) x = L.d (n + 1) (h (n + 1) x) + h n (K.d n x)
-- @endregion

-- @region algebraic_topology.homotopic_maps_agree_on_homology
-- @provenance independent
/-- **Chain-homotopic maps induce the same map on homology.** If `z` is a cycle then
`f z - g z = d (h z) + h (d z) = d (h z)` is a boundary, so `f z` and `g z` have the same
homology class. This is the algebraic half of the homotopy invariance of homology. -/
theorem homotopic_maps_agree_on_homology {K L : ChainCx} {φ ψ : ChainMap K L}
    (H : ChainHomotopy φ ψ) (n : ℕ) (z : K.C n) (hz : IsCycle K n z) :
    IsBoundary L n (φ.f n z - ψ.f n z) := by
  cases n with
  | zero => exact ⟨H.h 0 z, (H.zero z).symm⟩
  | succ n =>
    refine ⟨H.h (n + 1) z, ?_⟩
    have hdz : K.d n z = 0 := hz
    calc L.d (n + 1) (H.h (n + 1) z)
        = L.d (n + 1) (H.h (n + 1) z) + H.h n (K.d n z) := by rw [hdz, map_zero, add_zero]
      _ = φ.f (n + 1) z - ψ.f (n + 1) z := (H.succ n z).symm
-- @endregion

/-! ### Euler characteristic and Betti numbers -/

open Module in
-- @region algebraic_topology.euler_poincare
-- @provenance independent
/-- **The Euler–Poincaré formula** for a complex `C₂ → C₁ → C₀` of finite-dimensional vector
spaces over a field `K` (for example the cellular chains of a surface with coefficients in `ℚ`
or `ℤ/2`): the alternating sum of the dimensions of the homology groups
`H₀ = C₀ / im d₁`, `H₁ = ker d₁ / im d₂`, `H₂ = ker d₂` equals the alternating sum of the
dimensions of the chain groups — `b₀ - b₁ + b₂ = V - E + F`. The proof is rank–nullity twice. -/
theorem euler_poincare {K : Type*} [Field K] {C₀ C₁ C₂ : Type*}
    [AddCommGroup C₀] [Module K C₀] [FiniteDimensional K C₀]
    [AddCommGroup C₁] [Module K C₁] [FiniteDimensional K C₁]
    [AddCommGroup C₂] [Module K C₂] [FiniteDimensional K C₂]
    (d₁ : C₁ →ₗ[K] C₀) (d₂ : C₂ →ₗ[K] C₁) (hd : d₁ ∘ₗ d₂ = 0) :
    (finrank K (C₀ ⧸ LinearMap.range d₁) : ℤ)
      - finrank K (LinearMap.ker d₁ ⧸ (LinearMap.range d₂).comap (LinearMap.ker d₁).subtype)
      + finrank K (LinearMap.ker d₂)
      = finrank K C₀ - finrank K C₁ + finrank K C₂ := by
  -- `im d₂ ⊆ ker d₁` because `d₁ ∘ d₂ = 0`.
  have hle : LinearMap.range d₂ ≤ LinearMap.ker d₁ := by
    rintro _ ⟨y, rfl⟩
    simpa using LinearMap.congr_fun hd y
  -- dimensions of the quotients
  have h₀ := (LinearMap.range d₁).finrank_quotient_add_finrank
  have h₁ := ((LinearMap.range d₂).comap (LinearMap.ker d₁).subtype).finrank_quotient_add_finrank
  -- inside `ker d₁`, the boundaries are a copy of `im d₂`
  have hB : finrank K ((LinearMap.range d₂).comap (LinearMap.ker d₁).subtype)
      = finrank K (LinearMap.range d₂) :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  -- rank–nullity for `d₁` and `d₂`
  have r₁ := LinearMap.finrank_range_add_finrank_ker d₁
  have r₂ := LinearMap.finrank_range_add_finrank_ker d₂
  omega
-- @endregion

/-! ### Cellular homology of the real projective plane -/

-- @region algebraic_topology.rp2_cellular
-- @provenance independent
/-- The cellular chain complex of `ℝP²` is `ℤ --(×2)--> ℤ --(×0)--> ℤ`. With integer
coefficients the top differential `×2` is injective, so `H₂(ℝP²; ℤ) = 0`; with coefficients in
`ℤ/2` it is the zero map, so `H₂(ℝP²; ℤ/2) ≅ ℤ/2`. Homology depends on the coefficients. -/
theorem rp2_cellular :
    (∀ x : ℤ, 2 * x = 0 → x = 0) ∧ (∀ x : ZMod 2, 2 * x = 0) := by
  refine ⟨fun x hx => by omega, ?_⟩
  decide
-- @endregion

-- @region algebraic_topology.rp2_h1
-- @provenance library
/-- `H₁(ℝP²; ℤ) = ker(×0) / im(×2) = ℤ / 2ℤ ≅ ℤ/2`: a homology group with torsion. This applies
Mathlib's `Int.quotientZMultiplesNatEquivZMod`. -/
theorem rp2_h1 : Nonempty ((ℤ ⧸ AddSubgroup.zmultiples (2 : ℤ)) ≃+ ZMod 2) :=
  ⟨Int.quotientZMultiplesNatEquivZMod 2⟩
-- @endregion

/-! ### Functoriality: the no-retraction argument -/

open CategoryTheory CategoryTheory.Limits in
-- @region algebraic_topology.no_retraction
-- @provenance independent
/-- **The no-retraction principle.** Let `F` be any functor (for instance reduced homology
`H̃ₙ₋₁`). If `i : A → X` has a retraction `r` (`r ∘ i = id`) and `F X` is a zero object, then
`F A` is a zero object too: `id = F r ∘ F i` factors through `F X = 0`. Applied to
`A = Sⁿ⁻¹ ⊂ X = Dⁿ`, where `H̃ₙ₋₁(Dⁿ) = 0` but `H̃ₙ₋₁(Sⁿ⁻¹) ≅ ℤ`, it shows that the sphere is not
a retract of the disc — the heart of the Brouwer fixed-point theorem. -/
theorem no_retraction {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) {A X : C} (i : A ⟶ X) (r : X ⟶ A) (hri : i ≫ r = 𝟙 A)
    (hX : IsZero (F.obj X)) : IsZero (F.obj A) := by
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 (F.obj A) = F.map (i ≫ r) := by rw [hri, F.map_id]
    _ = F.map i ≫ F.map r := F.map_comp i r
    _ = 0 ≫ F.map r := by rw [hX.eq_of_tgt (F.map i) 0]
    _ = 0 := zero_comp
-- @endregion

/-! ### What Mathlib provides -/

open CategoryTheory in
-- @region algebraic_topology.d_squared
-- @provenance library
/-- **`∂ ∘ ∂ = 0`.** For every simplicial object `X` in a preadditive category (for example the
singular simplicial set of a space, made into simplicial abelian groups), the alternating sum
`∂ = Σᵢ (-1)ⁱ dᵢ` of the face maps squares to zero. This applies Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.d_squared`, whose proof cancels the double sum in
pairs using the simplicial identities, exactly as in the lesson. -/
theorem d_squared {V : Type*} [Category V] [Preadditive V] (X : SimplicialObject V) (n : ℕ) :
    _root_.AlgebraicTopology.AlternatingFaceMapComplex.objD X (n + 1) ≫
      _root_.AlgebraicTopology.AlternatingFaceMapComplex.objD X n = 0 :=
  _root_.AlgebraicTopology.AlternatingFaceMapComplex.d_squared X n
-- @endregion

open CategoryTheory CategoryTheory.Limits in
-- @region algebraic_topology.homotopy_invariance
-- @provenance library
/-- **Homotopy invariance of singular homology.** Homotopic continuous maps `f ≃ g : X → Y`
induce the same homomorphism `Hₙ(X; R) → Hₙ(Y; R)` for every `n` and every coefficient object
`R` (e.g. `ℤ` as an abelian group). This applies Mathlib's
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` (Riou–Odermatt), which builds a
chain homotopy between the induced maps of singular chain complexes. -/
theorem homotopy_invariance {V : Type*} [Category V] [Preadditive V] [HasCoproducts V]
    [CategoryWithHomology V] {X Y : TopCat} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (R : V)
    (n : ℕ) :
    HomologicalComplex.homologyMap
        (((_root_.AlgebraicTopology.singularChainComplexFunctor V).obj R).map f) n =
      HomologicalComplex.homologyMap
        (((_root_.AlgebraicTopology.singularChainComplexFunctor V).obj R).map g) n :=
  H.congr_homologyMap_singularChainComplexFunctor R n
-- @endregion

end Lumenary.AlgebraicTopology
