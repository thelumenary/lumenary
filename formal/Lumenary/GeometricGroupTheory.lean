/-
The Lumenary — formal mathematics
Geometric group theory: word metrics, quasi-isometries, growth, and a free subgroup of SL(2, ℤ)
found by playing ping-pong.

What is proved here. (1) Changing the finite generating set changes word lengths by at most a
bounded factor (`wordLength_le_mul_of_generators`): this is why the quasi-isometry class of a
Cayley graph is an invariant of the group. (2) Quasi-isometric embeddings and quasi-isometries
compose (`IsQIEmbedding.comp`, `IsQuasiIsometry.comp`), and `ℤ ↪ ℝ` is a quasi-isometry
(`int_cast_isQuasiIsometry`). (3) Sanov's theorem: the matrices `A = [[1, 2], [0, 1]]` and
`B = [[1, 0], [2, 1]]` generate a free group of rank two in `SL(2, ℤ)` (`sanov_free`); the
ping-pong estimates are proved here and fed into Mathlib's ping-pong lemma for free products.
Mathlib provides the word metric (`Group.Generators.wordLength`), the linear lower bound on the
growth of an infinite finitely generated group, and the ping-pong lemma. Not in Mathlib (as far
as we know): the Švarc–Milnor lemma, hyperbolic groups, Gromov's polynomial growth theorem,
amenability of groups, or the Banach–Tarski paradox.
-/
import Mathlib.GroupTheory.CoprodI
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Geometry.Group.WordMetric
import Mathlib.Geometry.Group.Growth.LinearLowerBound
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.Int
import Mathlib.Algebra.Order.Round

namespace Lumenary.GeometricGroupTheory

/-! ### Word length and the choice of generators -/

section WordLength

variable {G ι κ : Type*} [Group G]

-- @region geometric_group_theory.word_length_mul_le
-- @provenance library
/-- The word length is subadditive: `|gh|_S ≤ |g|_S + |h|_S`. Concatenating a shortest word for
`g` with one for `h` spells `gh`. This is Mathlib's `Group.Generators.wordLength_mul_le`; it makes
`d_S(g, h) = |g⁻¹h|_S` a metric, the **word metric**. -/
theorem word_length_mul_le (P : Group.Generators G ι) (g h : G) :
    P.wordLength (g * h) ≤ P.wordLength g + P.wordLength h :=
  P.wordLength_mul_le g h
-- @endregion

-- @region geometric_group_theory.word_length_le_mul_of_generators
-- @provenance independent
/-- **Changing generators distorts word length by a bounded factor.** If every generator of the
family `P` has `Q`-word length at most `L`, then `|g|_Q ≤ L · |g|_P` for every `g`. Proof: write
`g` as a shortest `P`-word `s₁^{±1} ⋯ s_n^{±1}`; replace each letter by a `Q`-word of length at
most `L` (inverting a word does not change its length) and use subadditivity. Applied in both
directions, the identity map is a bi-Lipschitz map between the two word metrics, so the Cayley
graphs for two finite generating sets are quasi-isometric. -/
theorem wordLength_le_mul_of_generators (P : Group.Generators G ι) (Q : Group.Generators G κ)
    (L : ℕ) (hL : ∀ i, Q.wordLength (P.val i) ≤ L) (g : G) :
    Q.wordLength g ≤ L * P.wordLength g := by
  -- First: every `P`-word of length `n` has `Q`-length at most `L * n`.
  have key : ∀ l : List (ι × Bool), Q.wordLength (P.wordProd l) ≤ L * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      obtain ⟨i, b⟩ := a
      have hletter : Q.wordLength (cond b (P.val i) (P.val i)⁻¹) ≤ L := by
        cases b <;> simp [hL i]
      calc Q.wordLength (P.wordProd ((i, b) :: l))
          = Q.wordLength (cond b (P.val i) (P.val i)⁻¹ * P.wordProd l) := by
            rw [P.wordProd_cons]
        _ ≤ Q.wordLength (cond b (P.val i) (P.val i)⁻¹) + Q.wordLength (P.wordProd l) :=
            Q.wordLength_mul_le _ _
        _ ≤ L + L * l.length := Nat.add_le_add hletter ih
        _ = L * ((i, b) :: l).length := by simp [Nat.mul_succ, Nat.add_comm]
  -- Then apply it to a shortest `P`-word for `g`.
  obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
  rw [hl.eq]
  exact key l
-- @endregion

end WordLength

/-! ### Quasi-isometries -/

section QuasiIsometry

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

-- @region geometric_group_theory.is_qi_embedding
-- @provenance definition
/-- `f : X → Y` is an `(L, C)`-**quasi-isometric embedding** (with `L ≥ 1`, `C ≥ 0`) if it
distorts distances by at most a factor `L`, up to an additive error `C`:
`d(x, x')/L − C ≤ d(f x, f x') ≤ L · d(x, x') + C`. Such a map may be discontinuous and may
collapse bounded sets: it only sees the space "from far away". -/
def IsQIEmbedding (f : X → Y) (L C : ℝ) : Prop :=
  1 ≤ L ∧ 0 ≤ C ∧ ∀ x x', dist x x' / L - C ≤ dist (f x) (f x') ∧
    dist (f x) (f x') ≤ L * dist x x' + C
-- @endregion

-- @region geometric_group_theory.is_quasi_isometry
-- @provenance definition
/-- A **quasi-isometry** is a quasi-isometric embedding that is **coarsely surjective**: every
point of `Y` lies within `C` of the image. Two spaces are quasi-isometric if there is a
quasi-isometry between them; for example `ℤ` and `ℝ`, or a group and its Cayley graph. -/
def IsQuasiIsometry (f : X → Y) (L C : ℝ) : Prop :=
  IsQIEmbedding f L C ∧ ∀ y, ∃ x, dist (f x) y ≤ C
-- @endregion

-- @region geometric_group_theory.isometry_is_qi_embedding
-- @provenance independent
/-- Every isometric embedding is a `(1, 0)`-quasi-isometric embedding: with `L = 1` and `C = 0`
both inequalities become the equation `d(f x, f x') = d(x, x')`. -/
theorem isometry_isQIEmbedding {f : X → Y} (hf : Isometry f) : IsQIEmbedding f 1 0 := by
  refine ⟨le_rfl, le_rfl, fun x x' => ?_⟩
  rw [hf.dist_eq]
  constructor <;> simp
-- @endregion

-- @region geometric_group_theory.is_qi_embedding_comp
-- @provenance independent
/-- Quasi-isometric embeddings compose: if `f` is an `(L, C)`- and `g` an `(L', C')`-quasi-isometric
embedding, then `g ∘ f` is an `(L'L, L'C + C')`-quasi-isometric embedding. Upper bound:
`d(gfx, gfx') ≤ L'(L d + C) + C'`. Lower bound: `d(gfx, gfx') ≥ (d/L − C)/L' − C'`, and
`C/L' ≤ L'C` because `L' ≥ 1`. -/
theorem IsQIEmbedding.comp {f : X → Y} {g : Y → Z} {L C L' C' : ℝ}
    (hf : IsQIEmbedding f L C) (hg : IsQIEmbedding g L' C') :
    IsQIEmbedding (g ∘ f) (L' * L) (L' * C + C') := by
  obtain ⟨hL, hC, hfd⟩ := hf
  obtain ⟨hL', hC', hgd⟩ := hg
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos hL'
  refine ⟨one_le_mul_of_one_le_of_one_le hL' hL, by positivity, fun x x' => ⟨?_, ?_⟩⟩
  · obtain ⟨hf1, -⟩ := hfd x x'
    obtain ⟨hg1, -⟩ := hgd (f x) (f x')
    have hdiv : (dist x x' / L - C) / L' ≤ dist (f x) (f x') / L' :=
      div_le_div_of_nonneg_right hf1 hL'pos.le
    have hCL : C / L' ≤ L' * C := by
      rw [div_le_iff₀ hL'pos]
      nlinarith [mul_le_mul_of_nonneg_left hL' hC]
    have hsplit : (dist x x' / L - C) / L' = dist x x' / (L' * L) - C / L' := by
      field_simp
    simp only [Function.comp]
    linarith
  · obtain ⟨-, hf2⟩ := hfd x x'
    obtain ⟨-, hg2⟩ := hgd (f x) (f x')
    simp only [Function.comp]
    nlinarith [mul_le_mul_of_nonneg_left hf2 hL'pos.le]
-- @endregion

-- @region geometric_group_theory.is_quasi_isometry_comp
-- @provenance independent
/-- Quasi-isometries compose, so "being quasi-isometric" is transitive. A point `z` is within `C'`
of some `g y`, and `y` is within `C` of some `f x`; then `g (f x)` is within `L'C + C' + C'` of
`z`. We use the common constant `L'C + 2C'`. -/
theorem IsQuasiIsometry.comp {f : X → Y} {g : Y → Z} {L C L' C' : ℝ}
    (hf : IsQuasiIsometry f L C) (hg : IsQuasiIsometry g L' C') :
    IsQuasiIsometry (g ∘ f) (L' * L) (L' * C + 2 * C') := by
  obtain ⟨hfe, hfs⟩ := hf
  obtain ⟨hge, hgs⟩ := hg
  obtain ⟨-, -, hcd⟩ := IsQIEmbedding.comp hfe hge
  obtain ⟨hL, hC, -⟩ := hfe
  obtain ⟨hL', hC', hgd⟩ := hge
  refine ⟨⟨one_le_mul_of_one_le_of_one_le hL' hL, by positivity, fun x x' => ?_⟩, fun z => ?_⟩
  · obtain ⟨h1, h2⟩ := hcd x x'
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨y, hy⟩ := hgs z
    obtain ⟨x, hx⟩ := hfs y
    refine ⟨x, ?_⟩
    obtain ⟨-, hg2⟩ := hgd (f x) y
    calc dist ((g ∘ f) x) z ≤ dist (g (f x)) (g y) + dist (g y) z := dist_triangle _ _ _
      _ ≤ (L' * dist (f x) y + C') + C' := by gcongr
      _ ≤ L' * C + 2 * C' := by nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ L')]
-- @endregion

-- @region geometric_group_theory.int_cast_is_quasi_isometry
-- @provenance independent
/-- The inclusion `ℤ ↪ ℝ` is a `(1, 1/2)`-quasi-isometry: it preserves distances exactly, and every
real number lies within `1/2` of an integer (round it). So the discrete group `ℤ` and the line `ℝ`
look the same from far away — the prototype of "a group is quasi-isometric to the space it acts
on" (the Švarc–Milnor lemma). -/
theorem int_cast_isQuasiIsometry : IsQuasiIsometry (fun n : ℤ => (n : ℝ)) 1 (1 / 2) := by
  refine ⟨⟨le_rfl, by norm_num, fun m n => ?_⟩, fun y => ⟨round y, ?_⟩⟩
  · rw [Int.dist_cast_real]
    constructor <;> linarith [dist_nonneg (x := m) (y := n)]
  · rw [Real.dist_eq, abs_sub_comm]
    exact abs_sub_round y
-- @endregion

end QuasiIsometry

/-! ### Growth -/

open scoped Pointwise

-- @region geometric_group_theory.growth_at_least_linear
-- @provenance library
/-- **Growth is at least linear.** If a finite set `X ∋ 1` generates an infinite group, then the
`n`-fold product set `Xⁿ` (the ball of radius `n` in the word metric, for symmetric `X`) has at
least `n + 1` elements. This is Mathlib's `Finset.add_one_le_card_pow`. Gromov's theorem
characterises the other extreme: polynomial growth happens exactly for virtually nilpotent groups. -/
theorem growth_at_least_linear {G : Type*} [Group G] [DecidableEq G] {X : Finset G}
    (hX₁ : (1 : G) ∈ X) (hXinf : (Subgroup.closure (X : Set G) : Set G).Infinite) (n : ℕ) :
    n + 1 ≤ (X ^ n).card :=
  Finset.add_one_le_card_pow hX₁ hXinf n
-- @endregion

/-! ### Ping-pong and a free subgroup of SL(2, ℤ) -/

section Sanov

open Matrix Cardinal
open scoped MatrixGroups Pointwise Function

-- @region geometric_group_theory.upper_hom
-- @provenance definition
/-- The homomorphism `ℤ → SL(2, ℤ)`, `n ↦ [[1, 2n], [0, 1]]` (written multiplicatively, as
Mathlib's free products require). Its value at `1` is Sanov's matrix `A`, and its value at `n`
is `Aⁿ`. -/
def upperHom : Multiplicative ℤ →* SL(2, ℤ) where
  toFun n := ⟨!![1, 2 * n.toAdd; 0, 1], by simp [det_fin_two_of]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' m n := by
    apply Subtype.ext
    change !![1, 2 * (m * n).toAdd; 0, 1] = !![1, 2 * m.toAdd; 0, 1] * !![1, 2 * n.toAdd; 0, 1]
    rw [Matrix.mul_fin_two]
    simp [toAdd_mul]
    ring
-- @endregion

-- @region geometric_group_theory.lower_hom
-- @provenance definition
/-- The homomorphism `ℤ → SL(2, ℤ)`, `n ↦ [[1, 0], [2n, 1]]`; its value at `1` is Sanov's matrix
`B`. -/
def lowerHom : Multiplicative ℤ →* SL(2, ℤ) where
  toFun n := ⟨!![1, 0; 2 * n.toAdd, 1], by simp [det_fin_two_of]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' m n := by
    apply Subtype.ext
    change !![1, 0; 2 * (m * n).toAdd, 1] = !![1, 0; 2 * m.toAdd, 1] * !![1, 0; 2 * n.toAdd, 1]
    rw [Matrix.mul_fin_two]
    simp [toAdd_mul]
    ring
-- @endregion

-- @region geometric_group_theory.sanov_a
-- @provenance definition
/-- Sanov's matrix `A = [[1, 2], [0, 1]]`. -/
def sanovA : SL(2, ℤ) := upperHom (Multiplicative.ofAdd 1)
-- @endregion

-- @region geometric_group_theory.sanov_b
-- @provenance definition
/-- Sanov's matrix `B = [[1, 0], [2, 1]]`. -/
def sanovB : SL(2, ℤ) := lowerHom (Multiplicative.ofAdd 1)
-- @endregion

-- @region geometric_group_theory.upper_ping
-- @provenance independent
/-- **Ping.** A non-zero power `Aⁿ = [[1, 2n], [0, 1]]` sends a vector with `|x| < |y|` to one with
`|x'| > |y'|`. Indeed `(x', y') = (x + 2ny, y)` and `|x + 2ny| ≥ 2|n||y| − |x| ≥ 2|y| − |x| > |y|`. -/
theorem upper_ping (n : ℤ) (hn : n ≠ 0) (v : Fin 2 → ℤ) (hv : |v 0| < |v 1|) :
    |(upperHom (Multiplicative.ofAdd n) • v) 1| < |(upperHom (Multiplicative.ofAdd n) • v) 0| := by
  have h0 : (upperHom (Multiplicative.ofAdd n) • v) 0 = v 0 + 2 * n * v 1 := by
    change (!![1, 2 * n; 0, 1] *ᵥ v) 0 = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (upperHom (Multiplicative.ofAdd n) • v) 1 = v 1 := by
    change (!![1, 2 * n; 0, 1] *ᵥ v) 1 = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  have hn1 : 1 ≤ |n| := Int.one_le_abs hn
  have hbig : 2 * |v 1| ≤ |2 * n * v 1| := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (v 1)]
  have htri : |2 * n * v 1| ≤ |v 0 + 2 * n * v 1| + |v 0| := by
    have := abs_sub (v 0 + 2 * n * v 1) (v 0)
    simpa using this
  linarith
-- @endregion

-- @region geometric_group_theory.lower_pong
-- @provenance independent
/-- **Pong.** Symmetrically, a non-zero power `Bⁿ = [[1, 0], [2n, 1]]` sends a vector with
`|x| > |y|` to one with `|x'| < |y'|`: `(x', y') = (x, y + 2nx)`. -/
theorem lower_pong (n : ℤ) (hn : n ≠ 0) (v : Fin 2 → ℤ) (hv : |v 1| < |v 0|) :
    |(lowerHom (Multiplicative.ofAdd n) • v) 0| < |(lowerHom (Multiplicative.ofAdd n) • v) 1| := by
  have h0 : (lowerHom (Multiplicative.ofAdd n) • v) 0 = v 0 := by
    change (!![1, 0; 2 * n, 1] *ᵥ v) 0 = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (lowerHom (Multiplicative.ofAdd n) • v) 1 = v 1 + 2 * n * v 0 := by
    change (!![1, 0; 2 * n, 1] *ᵥ v) 1 = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [h0, h1]
  have hn1 : 1 ≤ |n| := Int.one_le_abs hn
  have hbig : 2 * |v 0| ≤ |2 * n * v 0| := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (v 0)]
  have htri : |2 * n * v 0| ≤ |v 1 + 2 * n * v 0| + |v 1| := by
    have := abs_sub (v 1 + 2 * n * v 0) (v 1)
    simpa using this
  linarith
-- @endregion

-- @region geometric_group_theory.sanov_free
-- @provenance independent
/-- **Sanov's theorem (1947).** The matrices `A = [[1, 2], [0, 1]]` and `B = [[1, 0], [2, 1]]`
generate a free group of rank two inside `SL(2, ℤ)`: the homomorphism from the free group on two
letters sending the letters to `A` and `B` is injective, so no non-trivial reduced word in
`A^{±1}, B^{±1}` equals the identity. Proof by **ping-pong** on `ℤ²`: let `X₀ = {|x| > |y|}` and
`X₁ = {|x| < |y|}`; non-zero powers of `A` send `X₁` into `X₀` (`upper_ping`) and non-zero powers
of `B` send `X₀` into `X₁` (`lower_pong`). Mathlib's ping-pong lemma for free products
(`Monoid.CoprodI.lift_injective_of_ping_pong`) turns these two estimates into injectivity, via
`F₂ ≅ ℤ * ℤ` (`freeGroupEquivCoprodI`). -/
theorem sanov_free : Function.Injective (FreeGroup.lift ![sanovA, sanovB]) := by
  classical
  -- The ping-pong table: `X 0 = {|x| > |y|}` and `X 1 = {|x| < |y|}`.
  let X : Fin 2 → Set (Fin 2 → ℤ) := ![{v | |v 1| < |v 0|}, {v | |v 0| < |v 1|}]
  let H : Fin 2 → Type := fun _ => FreeGroup Unit
  let f : ∀ i, H i →* SL(2, ℤ) := fun i => FreeGroup.lift fun _ => ![sanovA, sanovB] i
  -- A free group is the free product of copies of `ℤ = FreeGroup Unit`.
  have hlift : FreeGroup.lift ![sanovA, sanovB] =
      (Monoid.CoprodI.lift f).comp (@freeGroupEquivCoprodI (Fin 2)).toMonoidHom := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [f, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      freeGroupEquivCoprodI_apply]
    rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, Monoid.CoprodI.lift_of,
      FreeGroup.lift_apply_of]
  rw [hlift, MonoidHom.coe_comp]
  refine Function.Injective.comp ?_ (MulEquiv.injective _)
  refine Monoid.CoprodI.lift_injective_of_ping_pong f ?_ X ?_ ?_ ?_
  · -- one factor has at least three elements
    right
    refine ⟨0, ?_⟩
    simp only [H]
    rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
    exact natCast_le_aleph0
  · intro i
    fin_cases i
    · exact ⟨![1, 0], by simp [X]⟩
    · exact ⟨![0, 1], by simp [X]⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Set.disjoint_left.2 fun v h1 h2 => by simp [X] at h1 h2; linarith
    · exact Set.disjoint_left.2 fun v h1 h2 => by simp [X] at h1 h2; linarith
    · exact absurd rfl hij
  · intro i j hij
    refine FreeGroup.freeGroupUnitEquivInt.forall_congr_left.mpr ?_
    intro n hne1
    have hn : n ≠ 0 := by
      rintro rfl
      apply hne1
      simp [FreeGroup.freeGroupUnitEquivInt]
    change FreeGroup.lift (fun _ => ![sanovA, sanovB] i) (FreeGroup.of () ^ n) • X j ⊆ X i
    rw [map_zpow, FreeGroup.lift_apply_of]
    rw [Set.smul_set_subset_iff]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · intro v hv
      have hpow : sanovA ^ n = upperHom (Multiplicative.ofAdd n) := by
        rw [sanovA, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
      change |v 0| < |v 1| at hv
      change |(sanovA ^ n • v) 1| < |(sanovA ^ n • v) 0|
      rw [hpow]
      exact upper_ping n hn v hv
    · intro v hv
      have hpow : sanovB ^ n = lowerHom (Multiplicative.ofAdd n) := by
        rw [sanovB, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
      change |v 1| < |v 0| at hv
      change |(sanovB ^ n • v) 0| < |(sanovB ^ n • v) 1|
      rw [hpow]
      exact lower_pong n hn v hv
    · exact absurd rfl hij
-- @endregion

end Sanov

end Lumenary.GeometricGroupTheory
