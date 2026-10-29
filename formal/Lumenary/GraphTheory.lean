/-
The Lumenary — formal mathematics
Graph theory: the handshake lemma, Hall's marriage theorem, the edge bounds behind the
non-planarity of K₅ and K₃,₃, Mantel's and Turán's theorems, and the Ramsey number R(3, 3) = 6.

Proved here (`@provenance independent`): the easy direction of Hall's theorem; the arithmetic
consequences of Euler's formula (`E ≤ 3V − 6`, and `E ≤ 2V − 4` without triangles) and the fact
that K₅ and K₃,₃ violate them; the 2-colouring of K₅ by a pentagon and a pentagram with no
monochromatic triangle; and the theorem that every 2-colouring of the edges of K₆ has one — the
two halves of R(3, 3) = 6, following the pigeonhole proof of the lesson.

From Mathlib (`@provenance library`): the handshake lemma
`SimpleGraph.sum_degrees_eq_twice_card_edges`, Hall's theorem
`Finset.all_card_le_biUnion_card_iff_exists_injective`, and Turán's theorem
`SimpleGraph.CliqueFree.card_edgeFinset_le` with `SimpleGraph.turanNumber_two`.

Not formalised: Mathlib does not yet have plane embeddings of graphs, so Euler's formula itself,
Kuratowski's theorem and the four colour theorem are not stated here (the four colour theorem
has been formalised in Coq by Gonthier and Werner).
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.Hall.Basic

namespace Lumenary.GraphTheory

open Finset

/-! ### Degrees -/

-- @region graph_theory.handshake
-- @provenance library
/-- **The handshake lemma**: the degrees of a finite graph add up to twice the number of edges.
This applies Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem handshake {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  G.sum_degrees_eq_twice_card_edges
-- @endregion

/-! ### Hall's marriage theorem -/

-- @region graph_theory.hall_necessary
-- @provenance independent
/-- **Hall's condition is necessary.** If every `i` can be matched to its own `f i ∈ t i`, with
different `i` getting different elements, then any `k` indices have at least `k` neighbours
between them: the images `f i` of the indices in `s` are `#s` distinct neighbours. -/
theorem hall_necessary {ι α : Type*} [DecidableEq α] (t : ι → Finset α) (f : ι → α)
    (hf : Function.Injective f) (hft : ∀ i, f i ∈ t i) (s : Finset ι) :
    #s ≤ #(s.biUnion t) := by
  have hsub : s.image f ⊆ s.biUnion t := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    exact mem_biUnion.2 ⟨i, hi, hft i⟩
  calc #s = #(s.image f) := (card_image_of_injective s hf).symm
    _ ≤ #(s.biUnion t) := card_le_card hsub
-- @endregion

-- @region graph_theory.hall
-- @provenance library
/-- **Hall's marriage theorem** (P. Hall, 1935): a family of finite sets `t i` has a system of
distinct representatives if and only if every `k` of the sets together contain at least `k`
elements. Mathlib proves it for an arbitrary (even infinite) index type, which needs a
compactness argument on top of the finite case. This applies
`Finset.all_card_le_biUnion_card_iff_exists_injective`. -/
theorem hall {ι α : Type*} [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔ ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t
-- @endregion

/-! ### Planarity: the counting step -/

-- @region graph_theory.planar_edge_bound
-- @provenance independent
/-- **The edge bound for plane graphs.** If a connected plane graph has `V` vertices, `E` edges
and `F` faces, Euler's formula gives `V − E + F = 2`. If every face is bounded by at least three
edges, counting edge–face incidences gives `3F ≤ 2E`. Together: `E ≤ 3V − 6`. -/
theorem planar_edge_bound (V E F : ℤ) (euler : V - E + F = 2) (faces : 3 * F ≤ 2 * E) :
    E ≤ 3 * V - 6 := by
  omega
-- @endregion

-- @region graph_theory.planar_edge_bound_bipartite
-- @provenance independent
/-- Without triangles (for instance in a bipartite graph) every face has at least four edges,
so `4F ≤ 2E`, and Euler's formula gives `E ≤ 2V − 4`. -/
theorem planar_edge_bound_bipartite (V E F : ℤ) (euler : V - E + F = 2)
    (faces : 4 * F ≤ 2 * E) : E ≤ 2 * V - 4 := by
  omega
-- @endregion

-- @region graph_theory.k5_k33_too_many_edges
-- @provenance independent
/-- K₅ (5 vertices, 10 edges) violates `E ≤ 3V − 6`, and K₃,₃ (6 vertices, 9 edges, no
triangles) violates `E ≤ 2V − 4`. Combined with the two bounds above, this is the proof that
neither graph is planar — given Euler's formula, which is not formalised here. -/
theorem k5_k33_too_many_edges : ¬ ((10 : ℤ) ≤ 3 * 5 - 6) ∧ ¬ ((9 : ℤ) ≤ 2 * 6 - 4) := by
  omega
-- @endregion

/-! ### Extremal graph theory -/

-- @region graph_theory.mantel
-- @provenance library
/-- **Mantel's theorem** (1907): a triangle-free graph on `n` vertices has at most `⌊n² / 4⌋`
edges. This is the case `r = 2` of Turán's theorem, applying Mathlib's
`SimpleGraph.CliqueFree.card_edgeFinset_le` and `SimpleGraph.turanNumber_two`. -/
theorem mantel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) : #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  have := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) h
  rwa [SimpleGraph.turanNumber_two] at this
-- @endregion

-- @region graph_theory.turan
-- @provenance library
/-- **Turán's theorem** (1941), in the convenient form `|E| ≤ (1 − 1/r) n² / 2` for graphs with no
clique of size `r + 1`, written without division. This combines Mathlib's
`SimpleGraph.CliqueFree.card_edgeFinset_le` and `SimpleGraph.mul_turanNumber_le`. -/
theorem turan {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.CliqueFree (r + 1)) :
    2 * r * #G.edgeFinset ≤ (r - 1) * Fintype.card V ^ 2 :=
  calc 2 * r * #G.edgeFinset ≤ 2 * r * SimpleGraph.turanNumber (Fintype.card V) r :=
        Nat.mul_le_mul_left _ (SimpleGraph.CliqueFree.card_edgeFinset_le h)
    _ ≤ (r - 1) * Fintype.card V ^ 2 := SimpleGraph.mul_turanNumber_le
-- @endregion

/-! ### Ramsey: R(3, 3) = 6 -/

-- @region graph_theory.pentagon
-- @provenance definition
/-- A red–blue colouring of the edges of K₅: an edge is red (`true`) if it is a side of the
pentagon 0–1–2–3–4–0, and blue (`false`) if it is a diagonal (the pentagram). -/
def pentagon (e : Sym2 (Fin 5)) : Bool :=
  decide (e ∈ [s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)])
-- @endregion

-- @region graph_theory.pentagon_no_mono_triangle
-- @provenance independent
/-- **R(3, 3) > 5.** The pentagon colouring of K₅ has no monochromatic triangle: the red graph
(a 5-cycle) and the blue graph (another 5-cycle) contain no triangles. Checked by `decide` over
all `5³` triples. -/
theorem pentagon_no_mono_triangle :
    ∀ a b d : Fin 5, a ≠ b → b ≠ d → a ≠ d →
      ¬ (pentagon s(a, b) = pentagon s(b, d) ∧ pentagon s(b, d) = pentagon s(a, d)) := by
  decide
-- @endregion

-- @region graph_theory.bool_eq_of_ne
-- @provenance independent
/-- With only two colours, two edges that both avoid a colour have the same colour. -/
theorem bool_eq_of_ne_of_ne {a b col : Bool} (ha : a ≠ col) (hb : b ≠ col) : a = b := by
  cases a <;> cases b <;> cases col <;> simp_all
-- @endregion

-- @region graph_theory.three_of_five
-- @provenance independent
/-- **The pigeonhole step.** Among five edges coloured with two colours, three share a colour:
if at most two were red, at least three would be blue. -/
theorem three_of_five (f : Fin 5 → Bool) :
    ∃ col : Bool, ∃ x y z : Fin 5, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      f x = col ∧ f y = col ∧ f z = col := by
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin 5)))
    (fun k => f k = true)
  rw [card_univ, Fintype.card_fin] at hsplit
  by_cases h3 : 2 < #(univ.filter fun k : Fin 5 => f k = true)
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := two_lt_card_iff.1 h3
    simp only [mem_filter, mem_univ, true_and] at hx hy hz
    exact ⟨true, x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
  · have h3' : 2 < #(univ.filter fun k : Fin 5 => ¬ f k = true) := by omega
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := two_lt_card_iff.1 h3'
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_true] at hx hy hz
    exact ⟨false, x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
-- @endregion

-- @region graph_theory.ramsey_three_three
-- @provenance independent
/-- **R(3, 3) ≤ 6: every red–blue colouring of the edges of K₆ has a monochromatic triangle.**
The proof of the lesson: vertex `0` has five edges, so three of them, to `x, y, z`, share a
colour `col` (`three_of_five`). If any edge among `x, y, z` also has colour `col`, it forms a
triangle with `0`; otherwise all three edges among `x, y, z` have the other colour. -/
theorem ramsey_three_three (c : Sym2 (Fin 6) → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ b ≠ d ∧ a ≠ d ∧ c s(a, b) = c s(b, d) ∧ c s(b, d) = c s(a, d) := by
  -- Step 1: three edges at vertex 0 with the same colour. Vertex `k.succ` is the `k`-th neighbour.
  obtain ⟨col, x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ := three_of_five fun k => c s(0, k.succ)
  have h0x : (0 : Fin 6) ≠ x.succ := (Fin.succ_ne_zero x).symm
  have h0y : (0 : Fin 6) ≠ y.succ := (Fin.succ_ne_zero y).symm
  have h0z : (0 : Fin 6) ≠ z.succ := (Fin.succ_ne_zero z).symm
  have hxy' : x.succ ≠ y.succ := fun h => hxy (Fin.succ_inj.1 h)
  have hxz' : x.succ ≠ z.succ := fun h => hxz (Fin.succ_inj.1 h)
  have hyz' : y.succ ≠ z.succ := fun h => hyz (Fin.succ_inj.1 h)
  -- Step 2: an edge among `x, y, z` of colour `col` closes a triangle with `0`.
  by_cases e1 : c s(x.succ, y.succ) = col
  · exact ⟨0, x.succ, y.succ, h0x, hxy', h0y, hx.trans e1.symm, e1.trans hy.symm⟩
  by_cases e2 : c s(x.succ, z.succ) = col
  · exact ⟨0, x.succ, z.succ, h0x, hxz', h0z, hx.trans e2.symm, e2.trans hz.symm⟩
  by_cases e3 : c s(y.succ, z.succ) = col
  · exact ⟨0, y.succ, z.succ, h0y, hyz', h0z, hy.trans e3.symm, e3.trans hz.symm⟩
  -- Step 3: otherwise `x, y, z` form a triangle of the other colour.
  exact ⟨x.succ, y.succ, z.succ, hxy', hyz', hxz', bool_eq_of_ne_of_ne e1 e3,
    bool_eq_of_ne_of_ne e3 e2⟩
-- @endregion

end Lumenary.GraphTheory
