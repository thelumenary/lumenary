/-
The Lumenary — formal mathematics
Axiomatic set theory: the cumulative hierarchy `V_α`, rank and foundation, cofinality and König's
theorem `cf(2^κ) > κ`, and the generalised continuum hypothesis.

Mathlib models ZFC sets as the type `ZFSet` (built from well-founded trees of types), with the
von Neumann hierarchy `ZFSet.vonNeumann` and the rank function `ZFSet.rank`; it also has
cofinality and König's theorem for cardinals. Below, the structural facts about `V_α` apply
Mathlib, and three results are proved here from more basic facts: that membership has no cycles
(via rank), König's inequality `κ < cf(2^κ)` from `κ < κ^cf(κ)` — the same calculation as in the
lesson — and its corollary `2^ℵ₀ ≠ ℵ_ω`. Gödel's constructible universe `L` and the reflection
principle are **not** formalised (Mathlib has neither): they need a formalised satisfaction
relation for set-theoretic formulas inside `ZFSet`.
-/
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
import Mathlib.SetTheory.Cardinal.Aleph

universe u

namespace Lumenary.AxiomaticSetTheory

open Cardinal Ordinal

/-! ### The cumulative hierarchy -/

-- @region axiomatic_set_theory.von_neumann_succ
-- @provenance library
/-- The successor step of the cumulative hierarchy: `V_{α+1} = 𝒫(V_α)`.
This applies Mathlib's `ZFSet.vonNeumann_add_one`. -/
theorem vonNeumann_succ (α : Ordinal) :
    ZFSet.vonNeumann (α + 1) = ZFSet.powerset (ZFSet.vonNeumann α) :=
  ZFSet.vonNeumann_add_one α
-- @endregion

-- @region axiomatic_set_theory.von_neumann_limit
-- @provenance library
/-- The limit step: for a limit ordinal `λ` (or `0`), `V_λ = ⋃_{α<λ} V_α`.
This applies Mathlib's `ZFSet.vonNeumann_of_isSuccPrelimit`. -/
theorem vonNeumann_limit {l : Ordinal} (h : Order.IsSuccPrelimit l) :
    ZFSet.vonNeumann l = ZFSet.iUnion fun α : Set.Iio l => ZFSet.vonNeumann α :=
  ZFSet.vonNeumann_of_isSuccPrelimit h
-- @endregion

-- @region axiomatic_set_theory.mem_von_neumann_succ_rank
-- @provenance independent
/-- **Every set appears in the hierarchy**, at the stage after its rank: `x ∈ V_{rank(x)+1}`.
Here `rank` is defined by ∈-recursion, `rank x = sup {rank y + 1 | y ∈ x}`, which is possible
because membership is well founded (the axiom of foundation); Mathlib shows `x ∈ V_α` iff
`rank x < α` (`ZFSet.mem_vonNeumann`). -/
theorem mem_vonNeumann_succ_rank (x : ZFSet) :
    x ∈ ZFSet.vonNeumann (Order.succ (ZFSet.rank x)) :=
  ZFSet.mem_vonNeumann.mpr (Order.lt_succ (ZFSet.rank x))
-- @endregion

-- @region axiomatic_set_theory.exists_mem_von_neumann
-- @provenance library
/-- `V = ⋃_α V_α`: every set lies in some `V_α`. This applies `ZFSet.exists_mem_vonNeumann`. -/
theorem exists_mem_vonNeumann (x : ZFSet) : ∃ α, x ∈ ZFSet.vonNeumann α :=
  ZFSet.exists_mem_vonNeumann x
-- @endregion

-- @region axiomatic_set_theory.not_mem_self
-- @provenance independent
/-- No set is a member of itself. Proof via rank: `y ∈ x` implies `rank y < rank x`, so `x ∈ x`
would give `rank x < rank x`. (Mathlib proves the same as `ZFSet.mem_irrefl`.) -/
theorem not_mem_self (x : ZFSet) : x ∉ x := fun h =>
  lt_irrefl _ (ZFSet.rank_lt_of_mem h)
-- @endregion

-- @region axiomatic_set_theory.no_mem_two_cycle
-- @provenance independent
/-- There are no membership 2-cycles `x ∈ y ∈ x`: their ranks would satisfy
`rank x < rank y < rank x`. The same argument excludes cycles of every length. -/
theorem no_mem_two_cycle (x y : ZFSet) : ¬ (x ∈ y ∧ y ∈ x) := fun ⟨hxy, hyx⟩ =>
  lt_irrefl _ ((ZFSet.rank_lt_of_mem hxy).trans (ZFSet.rank_lt_of_mem hyx))
-- @endregion

-- @region axiomatic_set_theory.card_von_neumann
-- @provenance library
/-- The size of the hierarchy: `|V_α| = ℶ'_α` (Mathlib's `preBeth`: `0, 1, 2, 4, 16, …` for
finite `α`, and `ℶ_α` from `ω` on, since `V_{α+1} = 𝒫(V_α)` has `2^|V_α|` elements). This applies
`ZFSet.card_vonNeumann`. -/
theorem card_vonNeumann (α : Ordinal) : (ZFSet.vonNeumann α).card = preBeth α :=
  ZFSet.card_vonNeumann α
-- @endregion

/-! ### Cofinality and König's theorem -/

-- @region axiomatic_set_theory.koenig_power_cof
-- @provenance library
/-- **König's theorem**, in the form `κ < κ^cf(κ)` for infinite `κ`: an infinite cardinal is
smaller than the number of `cf(κ)`-sequences from it. (It follows from `∑ᵢ κᵢ < ∏ᵢ λᵢ` when
`κᵢ < λᵢ`, Mathlib's `Cardinal.sum_lt_prod`.) This applies `Cardinal.lt_power_cof_ord`; here
`c.ord.cof` is the cofinality of the initial ordinal of `c`. -/
theorem koenig_power_cof {κ : Cardinal} (hκ : ℵ₀ ≤ κ) : κ < κ ^ κ.ord.cof :=
  lt_power_cof_ord hκ
-- @endregion

-- @region axiomatic_set_theory.koenig_cof_two_power
-- @provenance independent
/-- **König's corollary: `cf(2^κ) > κ`** for every infinite cardinal `κ`. Proof as in the lesson:
put `λ = 2^κ` and suppose `cf(λ) ≤ κ`. Then
`λ < λ^cf(λ) ≤ λ^κ = 2^(κ·κ) = 2^κ = λ`, a contradiction. -/
theorem koenig_cof_two_power {κ : Cardinal} (hκ : ℵ₀ ≤ κ) :
    κ < ((2 : Cardinal) ^ κ).ord.cof := by
  by_contra h
  push Not at h
  have hl : ℵ₀ ≤ (2 : Cardinal) ^ κ := hκ.trans (cantor κ).le
  have hne : (2 : Cardinal) ^ κ ≠ 0 := power_ne_zero κ two_ne_zero
  have hle : ((2 : Cardinal) ^ κ) ^ ((2 : Cardinal) ^ κ).ord.cof ≤ (2 : Cardinal) ^ κ :=
    calc ((2 : Cardinal) ^ κ) ^ ((2 : Cardinal) ^ κ).ord.cof
        ≤ ((2 : Cardinal) ^ κ) ^ κ := power_le_power_left hne h
      _ = (2 : Cardinal) ^ (κ * κ) := power_mul.symm
      _ = (2 : Cardinal) ^ κ := by rw [mul_eq_self hκ]
  exact absurd (koenig_power_cof hl) (not_lt.mpr hle)
-- @endregion

-- @region axiomatic_set_theory.koenig_cof_two_power_library
-- @provenance library
/-- The same corollary from Mathlib, for any base `b > 1`: `κ < cf(b^κ)`.
This applies `Cardinal.lt_cof_ord_power`. -/
theorem koenig_cof_two_power_library {κ : Cardinal} (hκ : ℵ₀ ≤ κ) :
    κ < ((2 : Cardinal) ^ κ).ord.cof :=
  lt_cof_ord_power hκ one_lt_two
-- @endregion

-- @region axiomatic_set_theory.two_power_aleph0_ne_aleph_omega
-- @provenance independent
/-- **The continuum is not `ℵ_ω`.** The cardinal `ℵ_ω = sup {ℵₙ | n < ω}` has cofinality `ℵ₀`,
while König gives `cf(2^ℵ₀) > ℵ₀`. Here `ℵ_ω` is `ℵ_ ω` and its initial ordinal is `ω_ ω`, whose
cofinality equals that of `ω` (Mathlib's `Ordinal.cof_omega`). -/
theorem two_power_aleph0_ne_aleph_omega : (2 : Cardinal) ^ ℵ₀ ≠ ℵ_ ω := by
  intro h
  have hk := koenig_cof_two_power (le_refl ℵ₀)
  rw [h, ord_aleph, cof_omega isSuccLimit_omega0, cof_omega0] at hk
  exact lt_irrefl _ hk
-- @endregion

/-! ### The generalised continuum hypothesis -/

-- @region axiomatic_set_theory.gch
-- @provenance definition
/-- The **generalised continuum hypothesis**: `2^κ = κ⁺` for every infinite cardinal `κ`, where
`κ⁺ = Order.succ κ` is the next cardinal. Gödel showed that it holds in `L`, so it is consistent
with ZFC (if ZF is); Cohen showed that its negation is consistent too. -/
def GCH : Prop :=
  ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → 2 ^ κ = Order.succ κ
-- @endregion

-- @region axiomatic_set_theory.gch_continuum
-- @provenance independent
/-- GCH implies CH: `2^ℵ₀ = ℵ₁`, since the successor cardinal of `ℵ₀` is `ℵ₁`
(`Cardinal.succ_aleph0`). -/
theorem gch_continuum (h : GCH.{u}) : (2 : Cardinal.{u}) ^ ℵ₀ = ℵ₁ := by
  rw [h ℵ₀ le_rfl, succ_aleph0]
-- @endregion

end Lumenary.AxiomaticSetTheory
