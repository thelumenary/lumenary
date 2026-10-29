/-
The Lumenary — formal mathematics
Large cardinals: inaccessible and measurable cardinals, the universe `V_κ`, and κ-complete
ultrafilters.

What is formalised. Mathlib defines inaccessible cardinals (`Cardinal.IsInaccessible`), the von
Neumann hierarchy `ZFSet.vonNeumann` (`V_ α`) inside its model `ZFSet` of ZFC, and the rank of a
set. Proved here: if `κ` is inaccessible then every member of `V_κ` has fewer than `κ` elements,
and `V_κ` is closed under pairing, union, power set and images of fewer than `κ` sets (the closure
property behind Replacement), and contains `ω`. These are the set-theoretic facts behind the
theorem "`V_κ ⊨ ZFC`"; the theorem itself is not formalised, because Mathlib has no satisfaction
relation for formulas of set theory inside `ZFSet`. For measurable cardinals, defined here via
κ-complete non-principal ultrafilters (Mathlib has no definition), we prove that every set in
such an ultrafilter has at least `κ` elements, that a countably complete ultrafilter on `ℕ` is
principal, and — the main result — that **every measurable cardinal is inaccessible**: it is a
regular strong limit. Not formalised: ultrapowers, elementary embeddings `j : V → M`, Scott's
theorem that a measurable cardinal implies `V ≠ L`, and anything about consistency strength,
which would need a formalisation of provability in ZFC. Finally, Mathlib proves that Lean's own
universe hierarchy contains inaccessible cardinals — Lean's foundations are stronger than ZFC.
-/
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Filter.CountableInter

namespace Lumenary.LargeCardinals

open Cardinal Set

universe u

/-! ### Inaccessible cardinals and the universe `V_κ` -/

-- @region large_cardinals.inaccessible_iff
-- @provenance library
/-- Mathlib's definition of a (strongly) inaccessible cardinal agrees with the lesson's: `κ` is
uncountable, regular, and a strong limit (`2^λ < κ` for all `λ < κ`). This is Mathlib's
`Cardinal.isInaccessible_def`. -/
theorem inaccessible_iff {κ : Cardinal.{u}} :
    IsInaccessible κ ↔ ℵ₀ < κ ∧ Cardinal.IsRegular κ ∧ IsStrongLimit κ :=
  isInaccessible_def
-- @endregion

-- @region large_cardinals.card_von_neumann
-- @provenance library
/-- If `κ` is inaccessible then `|V_κ| = κ`. Mathlib computes `|V_α| = ℶ'_α` (`card_vonNeumann`,
with the "pre-beth" function `preBeth`) and proves `preBeth κ = κ` for inaccessible `κ`
(`IsInaccessible.preBeth_ord`), by the induction in the lesson: strong limit at successor steps,
regularity at limit steps. -/
theorem card_vonNeumann {κ : Cardinal.{u}} (hκ : IsInaccessible κ) :
    (ZFSet.vonNeumann κ.ord).card = κ := by
  rw [ZFSet.card_vonNeumann, hκ.preBeth_ord]
-- @endregion

-- @region large_cardinals.card_lt_of_mem
-- @provenance independent
/-- Every member of `V_κ`, for `κ` inaccessible, has fewer than `κ` elements: a set `x` of rank
`α < κ` is a subset of `V_α`, and `|V_α| = ℶ'_α < ℶ'_κ = κ`. -/
theorem card_lt_of_mem {κ : Cardinal.{u}} (hκ : IsInaccessible κ) {x : ZFSet.{u}}
    (hx : x ∈ ZFSet.vonNeumann κ.ord) : x.card < κ := by
  have hr : x.rank < κ.ord := ZFSet.mem_vonNeumann.1 hx
  calc x.card ≤ (ZFSet.vonNeumann x.rank).card := ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)
    _ = preBeth x.rank := ZFSet.card_vonNeumann _
    _ < preBeth κ.ord := preBeth_strictMono hr
    _ = κ := hκ.preBeth_ord
-- @endregion

-- @region large_cardinals.pair_mem
-- @provenance independent
/-- **Pairing** holds in `V_κ` for every infinite `κ`: `rank {x, y} = max (rank x + 1) (rank y + 1)`,
and the successor of an ordinal below the limit ordinal `κ` is still below it. -/
theorem pair_mem {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {x y : ZFSet.{u}}
    (hx : x ∈ ZFSet.vonNeumann κ.ord) (hy : y ∈ ZFSet.vonNeumann κ.ord) :
    ({x, y} : ZFSet) ∈ ZFSet.vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann] at *
  rw [ZFSet.rank_pair]
  have hlim := isSuccLimit_ord hκ
  exact max_lt (hlim.succ_lt hx) (hlim.succ_lt hy)
-- @endregion

-- @region large_cardinals.sunion_mem
-- @provenance independent
/-- **Union** holds in `V_κ`: `rank (⋃₀ x) ≤ rank x`. -/
theorem sUnion_mem {κ : Cardinal.{u}} {x : ZFSet.{u}} (hx : x ∈ ZFSet.vonNeumann κ.ord) :
    ZFSet.sUnion x ∈ ZFSet.vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann] at *
  exact (ZFSet.rank_sUnion_le x).trans_lt hx
-- @endregion

-- @region large_cardinals.powerset_mem
-- @provenance independent
/-- **Power set** holds in `V_κ` for every infinite `κ`: `rank (𝒫 x) = rank x + 1 < κ`. (That
`𝒫 x` is the *true* power set, so that `V_κ` and `V` agree about it, is transitivity of `V_κ`
together with `V_{α+1} = 𝒫 V_α`.) -/
theorem powerset_mem {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {x : ZFSet.{u}}
    (hx : x ∈ ZFSet.vonNeumann κ.ord) : ZFSet.powerset x ∈ ZFSet.vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann] at *
  rw [ZFSet.rank_powerset]
  exact (isSuccLimit_ord hκ).succ_lt hx
-- @endregion

-- @region large_cardinals.range_mem
-- @provenance independent
/-- **Replacement** for `V_κ`, `κ` regular: if fewer than `κ` sets `f i` all lie in `V_κ`, so does
the set `{f i : i ∈ ι}`. Its rank is `sup (rank (f i) + 1)`, and a supremum of fewer than
`cf κ = κ` ordinals below `κ` stays below `κ`. This is exactly where regularity is needed: for
`κ = ℵ_ω`, which is singular, the ranks `ω_n` of the sets `ω_n ∈ V_{ω_ω}` are cofinal in `ω_ω`. -/
theorem range_mem {κ : Cardinal.{u}} (hκ : Cardinal.IsRegular κ) {ι : Type u} (hι : #ι < κ)
    (f : ι → ZFSet.{u}) (hf : ∀ i, f i ∈ ZFSet.vonNeumann κ.ord) :
    ZFSet.range f ∈ ZFSet.vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann, ZFSet.rank_range]
  simp_rw [Order.succ_eq_add_one]
  apply Ordinal.iSup_add_one_lt_of_lt_cof
  · rwa [hκ.cof_ord]
  · exact fun i => ZFSet.mem_vonNeumann.1 (hf i)
-- @endregion

-- @region large_cardinals.omega_mem
-- @provenance independent
/-- **Infinity** holds in `V_κ` for uncountable `κ`: the von Neumann ordinal `ω` has rank `ω`,
which is below `κ` (viewed as an ordinal) because `κ > ℵ₀`. -/
theorem omega_mem {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) :
    (Ordinal.omega0.{u}).toZFSet ∈ ZFSet.vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet, Cardinal.lt_ord, Ordinal.card_omega0]
  exact hκ
-- @endregion

-- @region large_cardinals.univ_inaccessible
-- @provenance library
/-- Lean's universes are inaccessible: the cardinality of `Type u`, as a cardinal of the next
universe, is inaccessible (Mathlib's `Cardinal.IsInaccessible.univ`). So Lean's type theory
proves the existence of inaccessible cardinals, which ZFC cannot (if it is consistent) — Lean's
foundations are strictly stronger than ZFC. -/
theorem univ_inaccessible : IsInaccessible Cardinal.univ.{u, u + 1} :=
  IsInaccessible.univ
-- @endregion

/-! ### Measurable cardinals -/

-- @region large_cardinals.is_complete
-- @provenance definition
/-- An ultrafilter `U` on `α` is **κ-complete** if the intersection of any family of fewer than
`κ` members of `U` is again in `U`. Every ultrafilter is `ℵ₀`-complete (finite intersections). -/
def IsComplete (κ : Cardinal.{u}) {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ S : Set (Set α), #S < κ → (∀ s ∈ S, s ∈ U) → ⋂₀ S ∈ U
-- @endregion

-- @region large_cardinals.is_nonprincipal
-- @provenance definition
/-- An ultrafilter is **non-principal** if it contains no singleton (equivalently, it is not the
ultrafilter `{s : a ∈ s}` of all sets containing a fixed point `a`). -/
def IsNonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ a : α, ({a} : Set α) ∉ U
-- @endregion

-- @region large_cardinals.is_measurable
-- @provenance definition
/-- `κ` is **measurable** if it is uncountable and there is a κ-complete non-principal
ultrafilter on (the well-ordered set of ordinals below) `κ`. Without "uncountable", `ℵ₀` would
qualify, since every non-principal ultrafilter on `ℕ` is `ℵ₀`-complete. -/
def IsMeasurable (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ ∃ U : Ultrafilter κ.ord.ToType, IsComplete κ U ∧ IsNonprincipal U
-- @endregion

-- @region large_cardinals.le_card_of_mem
-- @provenance independent
/-- In a κ-complete non-principal ultrafilter every set has at least `κ` elements. If `s ∈ U`
had fewer, the fewer than `κ` sets `{a}ᶜ` (`a ∈ s`) would all be in `U`, so their intersection,
and its intersection with `s`, would be in `U` — but that set is empty. -/
theorem le_card_of_mem {κ : Cardinal.{u}} {α : Type u} {U : Ultrafilter α} (hc : IsComplete κ U)
    (hn : IsNonprincipal U) {s : Set α} (hs : s ∈ U) : κ ≤ #s := by
  by_contra! hlt
  let S : Set (Set α) := (fun a => ({a}ᶜ : Set α)) '' s
  have hI : ⋂₀ S ∈ U := by
    refine hc S (mk_image_le.trans_lt hlt) ?_
    rintro _ ⟨a, -, rfl⟩
    exact Ultrafilter.compl_mem_iff_notMem.2 (hn a)
  have hempty : s ∩ ⋂₀ S = ∅ := by
    ext b
    simp only [S, mem_inter_iff, mem_sInter, mem_image, forall_exists_index, and_imp,
      mem_empty_iff_false, iff_false, not_and]
    intro hb h
    exact h _ b hb rfl rfl
  have h := Filter.inter_mem hs hI
  rw [hempty] at h
  exact Ultrafilter.empty_notMem h
-- @endregion

-- @region large_cardinals.principal_of_card_lt
-- @provenance independent
/-- A κ-complete ultrafilter on a set with fewer than `κ` elements is principal. In particular
the ultrafilter witnessing measurability must live on a set of size at least `κ`. -/
theorem principal_of_card_lt {κ : Cardinal.{u}} {α : Type u} {U : Ultrafilter α}
    (hc : IsComplete κ U) (hα : #α < κ) : ∃ a : α, ({a} : Set α) ∈ U := by
  by_contra! h
  have := le_card_of_mem hc h (Filter.univ_mem : (univ : Set α) ∈ U)
  rw [mk_univ] at this
  exact this.not_gt hα
-- @endregion

-- @region large_cardinals.nat_countably_complete_principal
-- @provenance independent
/-- `ℵ₀` is not measurable in any reasonable sense: a countably complete ultrafilter on `ℕ`
(Mathlib's `CountableInterFilter`) is principal, because the countably many sets `{n}ᶜ` would
otherwise all be in it, and their intersection is empty. -/
theorem nat_countably_complete_principal (U : Ultrafilter ℕ) [CountableInterFilter (U : Filter ℕ)] :
    ∃ n : ℕ, ({n} : Set ℕ) ∈ U := by
  by_contra! h
  have hI : (⋂ n : ℕ, ({n}ᶜ : Set ℕ)) ∈ (U : Filter ℕ) :=
    countable_iInter_mem.2 fun n => Ultrafilter.compl_mem_iff_notMem.2 (h n)
  have hempty : (⋂ n : ℕ, ({n}ᶜ : Set ℕ)) = ∅ := by
    ext m
    simp only [mem_iInter, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_forall, not_not]
    exact ⟨m, rfl⟩
  rw [hempty] at hI
  exact Ultrafilter.empty_notMem hI
-- @endregion

-- @region large_cardinals.two_power_lt
-- @provenance independent
/-- **A measurable cardinal is a strong limit.** If `μ < κ` but `κ ≤ 2^μ`, embed `κ` into the
subsets of a set `I` of size `μ`, `a ↦ g a`. For each `i ∈ I` the ultrafilter contains either
`{a : i ∈ g a}` or its complement; intersecting these fewer than `κ` choices gives a set in `U`
on which `g` is constant — at most one point, contradicting `le_card_of_mem`. -/
theorem two_power_lt {κ : Cardinal.{u}} (hκ : IsMeasurable κ) {μ : Cardinal.{u}} (hμ : μ < κ) :
    2 ^ μ < κ := by
  classical
  obtain ⟨hω, U, hc, hn⟩ := hκ
  by_contra! hle
  -- An embedding of the ordinals below `κ` into the subsets of `I`, where `|I| = μ`.
  set I := μ.out
  have hI : #I = μ := mk_out μ
  have hle' : #κ.ord.ToType ≤ #(Set I) := by
    rw [mk_toType, card_ord, mk_set, hI]
    exact hle
  obtain ⟨g⟩ := (le_def _ _).1 hle'
  -- For each `i`, the member of `U` deciding whether `i ∈ g a`.
  let Y : I → Set κ.ord.ToType := fun i =>
    if {a | i ∈ g a} ∈ U then {a | i ∈ g a} else {a | i ∈ g a}ᶜ
  have hY : ∀ i, Y i ∈ U := by
    intro i
    by_cases h : {a | i ∈ g a} ∈ U
    · rw [show Y i = {a | i ∈ g a} from ite_eq_left h]; exact h
    · rw [show Y i = {a | i ∈ g a}ᶜ from ite_eq_right h]
      exact Ultrafilter.compl_mem_iff_notMem.2 h
  have hInter : ⋂₀ range Y ∈ U :=
    hc (range Y) (mk_range_le.trans_lt (hI ▸ hμ)) (by rintro _ ⟨i, rfl⟩; exact hY i)
  -- On that intersection, `g` takes a single value, so it has at most one point.
  have hsub : (⋂₀ range Y).Subsingleton := by
    intro a ha b hb
    apply g.injective
    ext i
    have ha' := mem_sInter.1 ha (Y i) ⟨i, rfl⟩
    have hb' := mem_sInter.1 hb (Y i) ⟨i, rfl⟩
    by_cases h : {a | i ∈ g a} ∈ U
    · rw [show Y i = {a | i ∈ g a} from ite_eq_left h] at ha' hb'
      exact iff_of_true ha' hb'
    · rw [show Y i = {a | i ∈ g a}ᶜ from ite_eq_right h] at ha' hb'
      exact iff_of_false ha' hb'
  have h1 : #(⋂₀ range Y) ≤ 1 := mk_le_one_iff_set_subsingleton.2 hsub
  have h2 := le_card_of_mem hc hn hInter
  exact absurd (h2.trans h1) (not_le.2 (one_lt_aleph0.trans hω))
-- @endregion

-- @region large_cardinals.is_regular
-- @provenance independent
/-- **A measurable cardinal is regular.** If `cf κ < κ`, the ordinals below `κ` are covered by
fewer than `κ` initial segments `Iic s`, each with fewer than `κ` elements. None of them is in
`U` (`le_card_of_mem`), so all their complements are, and by κ-completeness so is the
intersection of the complements — which is empty. -/
theorem is_regular {κ : Cardinal.{u}} (hκ : IsMeasurable κ) : Cardinal.IsRegular κ := by
  obtain ⟨hω, U, hc, hn⟩ := hκ
  refine ⟨hω.le, ?_⟩
  by_contra! hlt
  obtain ⟨S, hS, hcard⟩ := Order.exists_cof_eq κ.ord.ToType
  rw [Ordinal.cof_toType] at hcard
  -- Initial segments of `κ` are small.
  have hsmall : ∀ s : κ.ord.ToType, #(Iic s) < κ := by
    intro s
    have hIio : #(Iio s) < κ := by
      have := mk_Iio_lt s (by rw [mk_toType, card_ord, Ordinal.type_toType])
      rwa [mk_toType, card_ord] at this
    rw [← Iio_insert]
    exact mk_insert_le.trans_lt (add_lt_of_lt hω.le hIio (one_lt_aleph0.trans hω))
  let F : Set (Set κ.ord.ToType) := (fun s => (Iic s)ᶜ) '' S
  have hI : ⋂₀ F ∈ U := by
    refine hc F (mk_image_le.trans_lt (hcard ▸ hlt)) ?_
    rintro _ ⟨s, -, rfl⟩
    exact Ultrafilter.compl_mem_iff_notMem.2 fun h => (le_card_of_mem hc hn h).not_gt (hsmall s)
  have hempty : ⋂₀ F = ∅ := by
    ext a
    simp only [F, mem_sInter, mem_image, forall_exists_index, and_imp, mem_empty_iff_false,
      iff_false, not_forall]
    obtain ⟨s, hs, has⟩ := hS a
    exact ⟨_, s, hs, rfl, fun h => h has⟩
  rw [hempty] at hI
  exact Ultrafilter.empty_notMem hI
-- @endregion

-- @region large_cardinals.measurable_inaccessible
-- @provenance independent
/-- **Every measurable cardinal is (strongly) inaccessible** (Ulam, 1930): it is uncountable by
definition, regular by `is_regular` and a strong limit by `two_power_lt`. -/
theorem measurable_inaccessible {κ : Cardinal.{u}} (hκ : IsMeasurable κ) : IsInaccessible κ :=
  inaccessible_iff.2 ⟨hκ.1, is_regular hκ, ⟨(aleph0_pos.trans hκ.1).ne', fun _ hμ => two_power_lt hκ hμ⟩⟩
-- @endregion

end Lumenary.LargeCardinals
