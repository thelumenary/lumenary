/-
The Lumenary — formal mathematics
ZFC: the axioms of set theory, used inside Lean.

Lean is *not* founded on ZFC: its logic is a dependent type theory. Mathlib nevertheless builds a
model of ZFC inside Lean. A `ZFSet` is a well-founded tree of "pre-sets" up to extensional
equivalence, and Mathlib proves that each ZFC axiom holds for it (`ZFSet.ext`, `ZFSet.mem_pair`,
`ZFSet.mem_sUnion`, `ZFSet.mem_powerset`, `ZFSet.mem_sep`, `ZFSet.mem_range`, `ZFSet.omega_succ`,
`ZFSet.regularity`, `ZFSet.choice_isFunc`). The first group of declarations below simply restates
these facts in the form a set theorist writes the axioms (`@provenance library`).

The second group proves, *from* those axioms, the first theorems of the lesson
(`@provenance independent`): Russell's argument that there is no set of all sets (Separation),
the characteristic property of Kuratowski pairs (Extensionality and Pairing), that no set is a
member of itself and there are no 2-cycles `x ∈ y ∈ x` (Foundation), and that the von Neumann
natural numbers `0 = ∅`, `n + 1 = n ∪ {n}` are distinct members of `ω`, ordered by `∈`, with
`n = {0, 1, …, n - 1}`.

Not formalised here: ZFC as a first-order *theory* (formulas, formal proofs, arbitrary models),
the independence of the axioms, and anything about the consistency of ZFC.
-/
import Mathlib.SetTheory.ZFC.Class

namespace Lumenary.Zfc

universe u

/-! ### The axioms, as facts about Mathlib's model `ZFSet` -/

-- @region zfc.extensionality
-- @provenance library
/-- **Extensionality.** Two sets with the same elements are equal.
This applies Mathlib's `ZFSet.ext`. -/
theorem extensionality (x y : ZFSet.{u}) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  ZFSet.ext h
-- @endregion

-- @region zfc.pairing
-- @provenance library
/-- **Pairing.** For any `a` and `b` there is a set `{a, b}` whose elements are exactly `a` and
`b`. This applies Mathlib's `ZFSet.mem_pair`. -/
theorem pairing (a b : ZFSet.{u}) : ∃ p : ZFSet.{u}, ∀ z, z ∈ p ↔ z = a ∨ z = b :=
  ⟨{a, b}, fun _ => ZFSet.mem_pair⟩
-- @endregion

-- @region zfc.union
-- @provenance library
/-- **Union.** For every set `x` there is a set `⋃ x` whose elements are the elements of the
elements of `x`. This applies Mathlib's `ZFSet.mem_sUnion`. -/
theorem union (x : ZFSet.{u}) : ∃ v : ZFSet.{u}, ∀ z, z ∈ v ↔ ∃ y ∈ x, z ∈ y :=
  ⟨ZFSet.sUnion x, fun _ => ZFSet.mem_sUnion⟩
-- @endregion

-- @region zfc.power_set
-- @provenance library
/-- **Power set.** For every set `x` there is a set `𝒫 x` whose elements are exactly the subsets
of `x`. This applies Mathlib's `ZFSet.mem_powerset`. -/
theorem power_set (x : ZFSet.{u}) : ∃ p : ZFSet.{u}, ∀ z, z ∈ p ↔ z ⊆ x :=
  ⟨ZFSet.powerset x, fun _ => ZFSet.mem_powerset⟩
-- @endregion

-- @region zfc.separation
-- @provenance library
/-- **Separation.** For every set `x` and every property `φ` there is a set
`{z ∈ x | φ z}`. In first-order ZFC this is a *schema*, one axiom for each formula `φ`; in Lean
it is a single statement quantifying over all predicates. This applies `ZFSet.mem_sep`. -/
theorem separation (φ : ZFSet.{u} → Prop) (x : ZFSet.{u}) :
    ∃ s : ZFSet.{u}, ∀ z, z ∈ s ↔ z ∈ x ∧ φ z :=
  ⟨ZFSet.sep φ x, fun _ => ZFSet.mem_sep⟩
-- @endregion

-- @region zfc.replacement
-- @provenance library
/-- **Replacement.** The image of a set under any operation `F` is a set:
`{F w | w ∈ x}`. Like Separation, this is a schema in first-order ZFC. This applies Mathlib's
`ZFSet.range` and `ZFSet.mem_range` (a set indexed by the elements of `x` is a set). -/
theorem replacement (F : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) :
    ∃ r : ZFSet.{u}, ∀ z, z ∈ r ↔ ∃ w ∈ x, F w = z := by
  refine ⟨ZFSet.range (fun w : x => F w), fun z => ?_⟩
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨w, hw⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
-- @endregion

-- @region zfc.infinity
-- @provenance library
/-- **Infinity.** There is a set containing `∅` and closed under `y ↦ y ∪ {y}`; Mathlib's `ω`
(`ZFSet.omega`) is one. This applies `ZFSet.omega_zero` and `ZFSet.omega_succ`. -/
theorem infinity :
    ∅ ∈ ZFSet.omega.{u} ∧ ∀ y ∈ ZFSet.omega.{u}, insert y y ∈ ZFSet.omega.{u} :=
  ⟨ZFSet.omega_zero, fun _ hy => ZFSet.omega_succ hy⟩
-- @endregion

-- @region zfc.foundation
-- @provenance library
/-- **Foundation (Regularity).** Every non-empty set `x` has an element `y` that shares no
element with `x`: an `∈`-minimal element. This applies Mathlib's `ZFSet.regularity`. -/
theorem foundation (x : ZFSet.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
  ZFSet.regularity x h
-- @endregion

-- @region zfc.choice
-- @provenance library
/-- **Choice**, in its set-theoretic form: if `x` is a set of non-empty sets, there is a
function — itself a set of ordered pairs — from `x` to `⋃ x`. Mathlib's `ZFSet.choice x`
(built from Lean's own choice principle) is one, and it picks `f(y) ∈ y` (`ZFSet.choice_cmem`).
This applies `ZFSet.choice_isFunc`. -/
theorem choice (x : ZFSet.{u}) (h : ∅ ∉ x) : ∃ f : ZFSet.{u}, ZFSet.IsFunc x (ZFSet.sUnion x) f :=
  ⟨ZFSet.choice x, ZFSet.choice_isFunc x h⟩
-- @endregion

/-! ### First theorems of ZF, proved from the axioms -/

-- @region zfc.no_universal_set
-- @provenance independent
/-- **There is no set of all sets.** If `U` contained every set, Separation would give
`R = {x ∈ U | x ∉ x}`, and then `R ∈ R ↔ R ∉ R`: Russell's paradox. Only Separation is used
(Foundation would give a different, shorter proof). -/
theorem no_universal_set : ¬ ∃ U : ZFSet.{u}, ∀ x, x ∈ U := by
  rintro ⟨U, hU⟩
  -- Separation: the members of `U` that are not members of themselves.
  obtain ⟨R, hR⟩ := separation (fun x => x ∉ x) U
  have key : R ∈ R ↔ R ∉ R :=
    (hR R).trans ⟨fun h => h.2, fun h => ⟨hU R, h⟩⟩
  -- A statement equivalent to its own negation is contradictory (no excluded middle needed).
  have hnot : R ∉ R := fun h => key.mp h h
  exact hnot (key.mpr hnot)
-- @endregion

-- @region zfc.kpair
-- @provenance definition
/-- The **Kuratowski ordered pair** `(a, b) = {{a}, {a, b}}`. It is the same set as Mathlib's
`ZFSet.pair a b`. -/
def kpair (a b : ZFSet.{u}) : ZFSet.{u} :=
  {{a}, {a, b}}
-- @endregion

-- @region zfc.kpair_inj
-- @provenance independent
/-- **The characteristic property of ordered pairs**, proved as in the lesson.
If `{{a}, {a, b}} = {{c}, {c, d}}` then:
1. `{a}` is `{c}` or `{c, d}`; either way `c ∈ {a}`, so `a = c`.
2. If `b = a`, the left side is `{{a}}`, so `{c, d} = {a}` and `d = a = b`.
3. If `b ≠ a`, then `{a, b}` is not a singleton, so `{a, b} = {c, d} = {a, d}` and `b = d`. -/
theorem kpair_inj {a b c d : ZFSet.{u}} (h : kpair a b = kpair c d) : a = c ∧ b = d := by
  -- Membership in the two pairs, by Extensionality and Pairing.
  have mem : ∀ z : ZFSet.{u}, (z = {a} ∨ z = {a, b}) ↔ (z = {c} ∨ z = {c, d}) := by
    intro z
    rw [← ZFSet.mem_pair, ← ZFSet.mem_pair]
    exact Iff.of_eq (congrArg (z ∈ ·) h)
  -- Step 1: `a = c`.
  have hac : a = c := by
    rcases (mem {a}).mp (Or.inl rfl) with h1 | h1
    · exact ZFSet.singleton_inj.mp h1
    · have hc : c ∈ ({a} : ZFSet.{u}) := by rw [h1]; exact ZFSet.mem_pair.mpr (Or.inl rfl)
      exact (ZFSet.mem_singleton.mp hc).symm
  refine ⟨hac, ?_⟩
  rw [← hac] at mem
  -- Step 2: `b = d`, splitting on whether `b = a`.
  by_cases hba : b = a
  · -- Then `{c, d} = {a, d}` is `{a}` or `{a, b} = {a}`; either way `d ∈ {a, b}`.
    rcases (mem {a, d}).mpr (Or.inr rfl) with h2 | h2
    · have hd : d ∈ ({a} : ZFSet.{u}) := by rw [← h2]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
      rw [hba, ZFSet.mem_singleton.mp hd]
    · have hd : d ∈ ({a, b} : ZFSet.{u}) := by rw [← h2]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
      rcases ZFSet.mem_pair.mp hd with h3 | h3
      · rw [hba, h3]
      · exact h3.symm
  · -- `{a, b}` is `{a}` (impossible, as `b ≠ a`) or `{a, d}`.
    rcases (mem {a, b}).mp (Or.inr rfl) with h2 | h2
    · have hb : b ∈ ({a} : ZFSet.{u}) := by rw [← h2]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
      exact absurd (ZFSet.mem_singleton.mp hb) hba
    · have hb : b ∈ ({a, d} : ZFSet.{u}) := by rw [← h2]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
      rcases ZFSet.mem_pair.mp hb with h3 | h3
      · exact absurd h3 hba
      · exact h3
-- @endregion

-- @region zfc.kpair_eq_iff
-- @provenance independent
/-- Kuratowski pairs are equal **exactly** when their components are: the converse direction of
`kpair_inj` is immediate. -/
theorem kpair_eq_iff {a b c d : ZFSet.{u}} : kpair a b = kpair c d ↔ a = c ∧ b = d := by
  constructor
  · exact kpair_inj
  · rintro ⟨rfl, rfl⟩
    rfl
-- @endregion

-- @region zfc.pair_inj_library
-- @provenance library
/-- The same fact for Mathlib's `ZFSet.pair` (which is `{{a}, {a, b}}` too), by `ZFSet.pair_inj`. -/
theorem pair_inj_library {a b c d : ZFSet.{u}} : ZFSet.pair a b = ZFSet.pair c d ↔ a = c ∧ b = d :=
  ZFSet.pair_inj
-- @endregion

-- @region zfc.not_mem_self
-- @provenance independent
/-- **No set is a member of itself.** If `x ∈ x`, apply Foundation to `{x}`: its only element
`x` must be disjoint from `{x}`, but `x ∈ {x} ∩ x`. (Mathlib: `ZFSet.mem_irrefl`.) -/
theorem not_mem_self (x : ZFSet.{u}) : x ∉ x := by
  intro hx
  have hne : ({x} : ZFSet.{u}) ≠ ∅ := fun h =>
    ZFSet.notMem_empty x (h ▸ ZFSet.mem_singleton.mpr rfl)
  obtain ⟨y, hy, hdisj⟩ := foundation {x} hne
  rw [ZFSet.mem_singleton.mp hy] at hdisj
  have hin : x ∈ ({x} : ZFSet.{u}) ∩ x := ZFSet.mem_inter.mpr ⟨ZFSet.mem_singleton.mpr rfl, hx⟩
  rw [hdisj] at hin
  exact ZFSet.notMem_empty x hin
-- @endregion

-- @region zfc.no_two_cycle
-- @provenance independent
/-- **There are no 2-cycles `x ∈ y ∈ x`.** Apply Foundation to `{x, y}`. If its `∈`-minimal
element is `x`, then `y ∈ {x, y} ∩ x`; if it is `y`, then `x ∈ {x, y} ∩ y`. Either way the
intersection is not empty. -/
theorem no_two_cycle (x y : ZFSet.{u}) : ¬ (x ∈ y ∧ y ∈ x) := by
  rintro ⟨hxy, hyx⟩
  have hx : x ∈ ({x, y} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
  have hy : y ∈ ({x, y} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inr rfl)
  have hne : ({x, y} : ZFSet.{u}) ≠ ∅ := fun h => ZFSet.notMem_empty x (h ▸ hx)
  obtain ⟨z, hz, hdisj⟩ := foundation {x, y} hne
  rcases ZFSet.mem_pair.mp hz with rfl | rfl
  · have hin : y ∈ ({z, y} : ZFSet.{u}) ∩ z := ZFSet.mem_inter.mpr ⟨hy, hyx⟩
    rw [hdisj] at hin
    exact ZFSet.notMem_empty y hin
  · have hin : x ∈ ({x, z} : ZFSet.{u}) ∩ z := ZFSet.mem_inter.mpr ⟨hx, hxy⟩
    rw [hdisj] at hin
    exact ZFSet.notMem_empty x hin
-- @endregion

/-! ### The von Neumann natural numbers -/

-- @region zfc.succ
-- @provenance definition
/-- The von Neumann **successor** `x ∪ {x}`, written `insert x x` in Mathlib. -/
def succ (x : ZFSet.{u}) : ZFSet.{u} :=
  insert x x
-- @endregion

-- @region zfc.mem_succ
-- @provenance library
/-- `y ∈ x ∪ {x}` exactly when `y = x` or `y ∈ x`. This applies `ZFSet.mem_insert_iff`. -/
theorem mem_succ {x y : ZFSet.{u}} : y ∈ succ x ↔ y = x ∨ y ∈ x :=
  ZFSet.mem_insert_iff
-- @endregion

-- @region zfc.succ_injective
-- @provenance independent
/-- **The successor operation is injective.** If `x ∪ {x} = y ∪ {y}`, then `x ∈ y ∪ {y}`, so
`x = y` or `x ∈ y`; symmetrically `y = x` or `y ∈ x`. If `x ≠ y` we would have `x ∈ y ∈ x`,
which Foundation forbids (`no_two_cycle`). -/
theorem succ_injective : Function.Injective succ := by
  intro x y h
  have hx : x ∈ succ y := by rw [← h]; exact mem_succ.mpr (Or.inl rfl)
  have hy : y ∈ succ x := by rw [h]; exact mem_succ.mpr (Or.inl rfl)
  rcases mem_succ.mp hx with hxy | hxy
  · exact hxy
  · rcases mem_succ.mp hy with hyx | hyx
    · exact hyx.symm
    · exact absurd ⟨hxy, hyx⟩ (no_two_cycle x y)
-- @endregion

-- @region zfc.of_nat
-- @provenance definition
/-- The **von Neumann natural numbers**: `0 = ∅` and `n + 1 = n ∪ {n}`. So
`1 = {∅}`, `2 = {∅, {∅}}`, `3 = {∅, {∅}, {∅, {∅}}}`, … -/
def ofNat : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => succ (ofNat n)
-- @endregion

-- @region zfc.of_nat_mem_omega
-- @provenance independent
/-- Every von Neumann natural number lies in `ω`: by induction, using the two halves of the
Axiom of Infinity (`infinity`). -/
theorem ofNat_mem_omega (n : ℕ) : ofNat n ∈ ZFSet.omega := by
  induction n with
  | zero => exact infinity.1
  | succ n ih => exact infinity.2 _ ih
-- @endregion

-- @region zfc.mem_of_nat
-- @provenance independent
/-- **`n = {0, 1, …, n - 1}`**: the elements of the set `ofNat n` are exactly the sets `ofNat m`
with `m < n`. By induction on `n`, since `n + 1 = n ∪ {n}`. -/
theorem mem_ofNat {n : ℕ} {y : ZFSet.{u}} : y ∈ ofNat n ↔ ∃ m < n, y = ofNat m := by
  induction n with
  | zero =>
    constructor
    · intro h; exact absurd h (ZFSet.notMem_empty y)
    · rintro ⟨m, hm, -⟩; exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    show y ∈ succ (ofNat n) ↔ _
    rw [mem_succ, ih]
    constructor
    · rintro (h | ⟨m, hm, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨m, Nat.lt_succ_of_lt hm, h⟩
    · rintro ⟨m, hm, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
      · exact Or.inr ⟨m, hlt, h⟩
      · exact Or.inl (heq ▸ h)
-- @endregion

-- @region zfc.of_nat_mem_iff
-- @provenance independent
/-- **The order of the natural numbers is membership:** `m ∈ n` (as sets) if and only if
`m < n`. The forward direction uses `mem_ofNat` and the injectivity below is a consequence. -/
theorem ofNat_mem_iff {m n : ℕ} : ofNat m ∈ ofNat n ↔ m < n := by
  constructor
  · intro h
    obtain ⟨k, hk, hmk⟩ := mem_ofNat.mp h
    -- `ofNat m = ofNat k` with `k < n`; if `m ≠ k` one of them is a member of the other.
    rcases Nat.lt_trichotomy m k with hlt | rfl | hgt
    · have hmem : ofNat m ∈ ofNat k := mem_ofNat.mpr ⟨m, hlt, rfl⟩
      rw [hmk] at hmem
      exact absurd hmem (not_mem_self _)
    · exact hk
    · have hmem : ofNat k ∈ ofNat m := mem_ofNat.mpr ⟨k, hgt, rfl⟩
      rw [← hmk] at hmem
      exact absurd hmem (not_mem_self _)
  · intro h
    exact mem_ofNat.mpr ⟨m, h, rfl⟩
-- @endregion

-- @region zfc.of_nat_injective
-- @provenance independent
/-- **Different numbers are different sets.** If `m < n` then `ofNat m ∈ ofNat n`; were the two
sets equal, we would have a set that is a member of itself. -/
theorem ofNat_injective : Function.Injective ofNat := by
  intro m n h
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have hmem := ofNat_mem_iff.mpr hlt
    rw [h] at hmem
    exact absurd hmem (not_mem_self _)
  · exact heq
  · have hmem := ofNat_mem_iff.mpr hgt
    rw [h] at hmem
    exact absurd hmem (not_mem_self _)
-- @endregion

-- @region zfc.mem_prod
-- @provenance library
/-- **Cartesian products are sets.** `x × y`, the set of pairs `(a, b)` with `a ∈ x`, `b ∈ y`, is
carved by Separation out of `𝒫(𝒫(x ∪ y))`, since `{{a}, {a, b}} ⊆ 𝒫(x ∪ y)`. This applies
Mathlib's `ZFSet.mem_prod`. -/
theorem mem_prod {x y z : ZFSet.{u}} : z ∈ ZFSet.prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = ZFSet.pair a b :=
  ZFSet.mem_prod
-- @endregion

end Lumenary.Zfc
