/-
The Lumenary — formal mathematics
Extremal and additive combinatorics: Turán's theorem, Ramsey numbers, sumsets, three-term
progressions, Roth's theorem and Szemerédi's regularity lemma.

Proved here (`@provenance independent`): the Erdős–Szekeres recursion
`R(s, t) ≤ R(s − 1, t) + R(s, t − 1)` and its consequences `R(s, t) ≤ C(s + t − 2, s − 1)` and
`R(k + 1, k + 1) ≤ 4ᵏ`, for graphs on an arbitrary vertex type; the sumset bound
`|A + B| ≥ |A| + |B| − 1` for finite sets of integers; and an explicit 3AP-free set showing
`r₃(14) ≥ 8`.

From Mathlib (`@provenance library`): Turán's theorem in its structural form (the extremal
graphs are exactly the Turán graphs); the Cauchy–Davenport theorem in `ℤ/pℤ` and in linearly
ordered groups; Roth's theorem `r₃(N) = o(N)` (Mathlib proves it via the corners theorem and the
triangle removal lemma, not by Fourier analysis); and Szemerédi's regularity lemma (Dillies and
Mehta).

Not formalised (and not in Mathlib at this version): Erdős's probabilistic lower bound for
Ramsey numbers, Szemerédi's theorem on long progressions, the Green–Tao theorem, sum–product
estimates, and the polynomial-method theorems (Dvir, Ellenberg–Gijswijt).
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Group.Finset

namespace Lumenary.AdditiveExtremalCombinatorics

open Finset Pointwise

/-! ### Turán's theorem -/

-- @region additive_extremal_combinatorics.turan_structure
-- @provenance library
/-- **Turán's theorem**, structural form: for `r ≥ 1`, a graph on `n` vertices is
*Turán-maximal* (it has no `K_{r+1}` and as many edges as possible among such graphs) if and
only if it is isomorphic to the Turán graph `T(n, r)`, the complete `r`-partite graph with parts
as equal as possible. This applies Mathlib's `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`
(proved there by Zykov symmetrisation). -/
theorem turan_structure {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g SimpleGraph.turanGraph (Fintype.card V) r) :=
  SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr
-- @endregion

/-! ### Ramsey numbers -/

-- @region additive_extremal_combinatorics.ramsey_prop
-- @provenance definition
/-- `RamseyProp α s t m` says: in **every** graph `G` on the vertex type `α`, **every** set `W` of
at least `m` vertices contains `s` vertices that are pairwise adjacent (an `s`-clique of `G`) or
`t` vertices that are pairwise non-adjacent (a `t`-clique of the complement `Gᶜ`). Colouring
the edges of `G` red and the non-edges blue, this is "`m ≥ R(s, t)`" for colourings of the
complete graph on `W`. Quantifying over all `W` inside one type avoids induced subgraphs. -/
def RamseyProp (α : Type*) (s t m : ℕ) : Prop :=
  ∀ (G : SimpleGraph α) (W : Finset α), m ≤ W.card →
    ∃ S ⊆ W, G.IsNClique s S ∨ Gᶜ.IsNClique t S
-- @endregion

-- @region additive_extremal_combinatorics.ramsey_one_left
-- @provenance independent
/-- `R(1, t) ≤ 1`: any single vertex is a `1`-clique. -/
theorem ramsey_one_left {α : Type*} (t : ℕ) : RamseyProp α 1 t 1 := by
  intro G W hW
  obtain ⟨v, hv⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨{v}, Finset.singleton_subset_iff.mpr hv, Or.inl (SimpleGraph.isNClique_one.mpr ⟨v, rfl⟩)⟩
-- @endregion

-- @region additive_extremal_combinatorics.ramsey_one_right
-- @provenance independent
/-- `R(s, 1) ≤ 1`: any single vertex is a `1`-clique of the complement. -/
theorem ramsey_one_right {α : Type*} (s : ℕ) : RamseyProp α s 1 1 := by
  intro G W hW
  obtain ⟨v, hv⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨{v}, Finset.singleton_subset_iff.mpr hv, Or.inr (SimpleGraph.isNClique_one.mpr ⟨v, rfl⟩)⟩
-- @endregion

-- @region additive_extremal_combinatorics.ramsey_step
-- @provenance independent
/-- **The Erdős–Szekeres recursion** `R(s + 1, t + 1) ≤ R(s, t + 1) + R(s + 1, t)`.
Proof, as in the lesson: pick a vertex `v ∈ W` and split the other `|W| − 1 ≥ a + b − 1` vertices
into neighbours `N` and non-neighbours `M`. By pigeonhole `|N| ≥ a` or `|M| ≥ b`. In `N` we find
an `s`-clique (add `v` to get an `(s + 1)`-clique) or an independent `(t + 1)`-set; in `M` an
`(s + 1)`-clique or an independent `t`-set (add `v`). -/
theorem ramsey_step {α : Type*} [DecidableEq α] {s t a b : ℕ}
    (hA : RamseyProp α s (t + 1) a) (hB : RamseyProp α (s + 1) t b) (hab : 0 < a + b) :
    RamseyProp α (s + 1) (t + 1) (a + b) := by
  classical
  intro G W hW
  obtain ⟨v, hv⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
  -- neighbours and non-neighbours of `v` in `W`
  set N := (W.erase v).filter (G.Adj v) with hN
  set M := (W.erase v).filter (fun w => ¬ G.Adj v w) with hM
  have hcard : N.card + M.card = W.card - 1 := by
    rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
  have hNW : N ⊆ W := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hMW : M ⊆ W := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  by_cases hNa : a ≤ N.card
  · obtain ⟨S, hSN, hS | hS⟩ := hA G N hNa
    · -- an `s`-clique of neighbours, plus `v`
      refine ⟨insert v S, Finset.insert_subset hv (hSN.trans hNW), Or.inl ?_⟩
      exact hS.insert fun w hw => (Finset.mem_filter.mp (hSN hw)).2
    · exact ⟨S, hSN.trans hNW, Or.inr hS⟩
  · -- pigeonhole: otherwise `M` is large
    have hMb : b ≤ M.card := by omega
    obtain ⟨S, hSM, hS | hS⟩ := hB G M hMb
    · exact ⟨S, hSM.trans hMW, Or.inl hS⟩
    · -- an independent `t`-set of non-neighbours, plus `v`
      refine ⟨insert v S, Finset.insert_subset hv (hSM.trans hMW), Or.inr ?_⟩
      refine hS.insert fun w hw => ?_
      have hw' := Finset.mem_filter.mp (hSM hw)
      rw [SimpleGraph.compl_adj]
      exact ⟨fun h => (Finset.ne_of_mem_erase hw'.1) h.symm, hw'.2⟩
-- @endregion

-- @region additive_extremal_combinatorics.ramsey_binomial
-- @provenance independent
/-- **The Erdős–Szekeres bound** (1935): `R(s + 1, t + 1) ≤ C(s + t, s)`, i.e.
`R(s, t) ≤ C(s + t − 2, s − 1)`. Induction on `s` and `t`, with the base cases `R(1, t) = R(s, 1)
= 1` and Pascal's rule `C(s + t + 2, s + 1) = C(s + t + 1, s) + C(s + t + 1, s + 1)` matching
the recursion `ramsey_step`. -/
theorem ramsey_binomial {α : Type*} [DecidableEq α] :
    ∀ s t : ℕ, RamseyProp α (s + 1) (t + 1) ((s + t).choose s) := by
  intro s
  induction s with
  | zero => intro t; simpa using ramsey_one_left (α := α) (t + 1)
  | succ s ihs =>
    intro t
    induction t with
    | zero => simpa using ramsey_one_right (α := α) (s + 1 + 1)
    | succ t iht =>
      have hc : (s + 1 + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show s + 1 + (t + 1) = (s + t + 1) + 1 by omega, Nat.choose_succ_succ,
          show s + (t + 1) = s + t + 1 by omega, show s + 1 + t = s + t + 1 by omega]
      rw [hc]
      exact ramsey_step (ihs (t + 1)) iht
        (by have := Nat.choose_pos (show s ≤ s + (t + 1) by omega); omega)
-- @endregion

-- @region additive_extremal_combinatorics.ramsey_diag
-- @provenance independent
/-- The diagonal case: `R(k + 1, k + 1) ≤ C(2k, k) ≤ 4ᵏ`. Every graph on `4ᵏ` vertices contains
`k + 1` vertices that are pairwise adjacent or pairwise non-adjacent. (Erdős's random colourings
show that the base `4` cannot be replaced by anything below `√2`.) -/
theorem ramsey_diag {α : Type*} [DecidableEq α] (k : ℕ) :
    RamseyProp α (k + 1) (k + 1) (4 ^ k) := by
  intro G W hW
  apply ramsey_binomial k k G W
  calc (k + k).choose k ≤ 2 ^ (k + k) := Nat.choose_le_two_pow _ _
    _ = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
    _ ≤ W.card := hW
-- @endregion

/-! ### Sumsets -/

-- @region additive_extremal_combinatorics.sumset_lower
-- @provenance independent
/-- **The simplest inverse-theorem bound**: for non-empty finite `A, B ⊆ ℤ`,
`|A + B| ≥ |A| + |B| − 1` (equality when `A` and `B` are progressions with the same difference).
Proof by induction on `A`, adding its largest element `a` last: `a + max B` is larger than every
sum in `A' + B`, where `A' = A \ {a}`, so `|A + B| ≥ |A' + B| + 1`. -/
theorem sumset_lower (B : Finset ℤ) (hB : B.Nonempty) :
    ∀ A : Finset ℤ, A.Nonempty → A.card + B.card - 1 ≤ (A + B).card := by
  intro A
  induction A using Finset.induction_on_max with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | insert a s hlt ih =>
    intro _
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp [Finset.card_singleton_add]
    · set m := B.max' hB
      -- the new sum `a + max B` exceeds every old sum
      have hnot : a + m ∉ s + B := by
        intro h
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp h
        have h1 := hlt x hx
        have h2 := Finset.le_max' B y hy
        omega
      have hsub : insert (a + m) (s + B) ⊆ insert a s + B :=
        Finset.insert_subset (Finset.add_mem_add (Finset.mem_insert_self _ _) (Finset.max'_mem _ _))
          (Finset.add_subset_add (Finset.subset_insert _ _) (subset_refl B))
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      rw [Finset.card_insert_of_notMem has]
      have := ih hs
      omega
-- @endregion

-- @region additive_extremal_combinatorics.cauchy_davenport_ordered
-- @provenance library
/-- Mathlib's version of `sumset_lower`, for any linearly ordered cancellative additive
semigroup. This applies `cauchy_davenport_add_of_linearOrder_isCancelAdd`. -/
theorem cauchy_davenport_ordered {α : Type*} [LinearOrder α] [Add α] [IsCancelAdd α]
    [AddLeftMono α] [AddRightMono α] {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card :=
  cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB
-- @endregion

-- @region additive_extremal_combinatorics.cauchy_davenport_zmod
-- @provenance library
/-- **The Cauchy–Davenport theorem** (Cauchy 1813, Davenport 1935): for non-empty `A, B ⊆ ℤ/pℤ`
with `p` prime, `|A + B| ≥ min(p, |A| + |B| − 1)`. In `ℤ/pℤ` sums can wrap around, so the
ordering argument fails; Mathlib proves it by DeVos's induction for arbitrary groups. This
applies `ZMod.cauchy_davenport`. -/
theorem cauchy_davenport_zmod {p : ℕ} (hp : p.Prime) {A B : Finset (ZMod p)} (hA : A.Nonempty)
    (hB : B.Nonempty) : min p (A.card + B.card - 1) ≤ (A + B).card :=
  ZMod.cauchy_davenport hp hA hB
-- @endregion

/-! ### Three-term progressions -/

-- @region additive_extremal_combinatorics.stanley_three_ap_free
-- @provenance independent
/-- The numbers below `14` whose base-3 digits are all `0` or `1`,
`{0, 1, 3, 4, 9, 10, 12, 13}`, contain no three-term arithmetic progression `a, b, c` with
`a + c = 2b` and `a ≠ b`. (Doubling a number with digits `0, 1` creates no carries in base 3, so
`a + c = 2b` forces equal digits.) Checked here by the kernel (`decide`) using Mathlib's
`ThreeAPFree`. -/
theorem stanley_three_ap_free :
    ThreeAPFree ((({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ)) : Set ℕ) := by
  decide
-- @endregion

-- @region additive_extremal_combinatorics.roth_number_14
-- @provenance independent
/-- Hence `r₃(14) ≥ 8`: `{0, …, 13}` contains a 3AP-free set of size 8. (In fact `r₃(14) = 8`.)
Uses Mathlib's `ThreeAPFree.le_rothNumberNat`. -/
theorem roth_number_14 : 8 ≤ rothNumberNat 14 :=
  ThreeAPFree.le_rothNumberNat _ stanley_three_ap_free (by decide) (by decide)
-- @endregion

-- @region additive_extremal_combinatorics.roth_theorem
-- @provenance library
/-- **Roth's theorem** (1953): `r₃(N) = o(N)` — for every `δ > 0`, every subset of `{0, …, N − 1}`
with at least `δN` elements contains a non-trivial three-term progression once `N` is large.
Mathlib proves it (Dillies and Mehta) through the triangle removal lemma and the
corners theorem — a different route from Roth's Fourier-analytic proof sketched in the
lesson. This applies `rothNumberNat_isLittleO_id`. -/
theorem roth_theorem :
    (fun N => (rothNumberNat N : ℝ)) =o[Filter.atTop] (fun N => (N : ℝ)) :=
  rothNumberNat_isLittleO_id
-- @endregion

-- @region additive_extremal_combinatorics.szemeredi_regularity_lemma
-- @provenance library
/-- **Szemerédi's regularity lemma** (1975–78), effective form: for every `ε > 0` and `l`, every
graph on at least `l` vertices has an `ε`-uniform equipartition into at least `l` and at most
`bound ε l` parts, where the bound depends only on `ε` and `l`, not on the graph. (The bound is
a tower of exponentials, and Gowers showed towers are necessary.) This applies Mathlib's
`szemeredi_regularity`, formalised by Dillies and Mehta. -/
theorem szemeredi_regularity_lemma {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] {ε : ℝ} {l : ℕ} (hε : 0 < ε) (hl : l ≤ Fintype.card α) :
    ∃ P : Finpartition (Finset.univ : Finset α), P.IsEquipartition ∧ l ≤ P.parts.card ∧
      P.parts.card ≤ SzemerediRegularity.bound ε l ∧ P.IsUniform G ε :=
  szemeredi_regularity G hε hl
-- @endregion

end Lumenary.AdditiveExtremalCombinatorics
