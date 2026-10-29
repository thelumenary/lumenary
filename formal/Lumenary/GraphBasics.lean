/-
The Lumenary — formal mathematics
Graphs: degrees and the handshake lemma, Euler trails and circuits (with the Königsberg bridges),
trees, and graph isomorphism.

Two models of a graph appear here. For the handshake lemma and Euler's theorem we use a
*multigraph* given as a list of edges, because the Königsberg bridges include parallel edges
(two bridges joining the same pair of land masses). For trees and isomorphism we use Mathlib's
`SimpleGraph`, so that learners meet the real library.

Proved here (`@provenance independent`): the handshake lemma for multigraphs, by induction on the
list of edges; that the number of odd-degree vertices is even; the edge-end count along a walk;
the necessity half of Euler's theorem — a multigraph with an Euler circuit has every degree even,
and in an Euler trail every odd-degree vertex is an end of the trail; that the Königsberg
multigraph has no Euler trail; that every finite tree with at least two vertices has at least two
leaves; and that the path and the star on four vertices — two trees with the same number of
vertices and edges — are not isomorphic.

From Mathlib (`@provenance library`): the handshake lemma for simple graphs
(`SimpleGraph.sum_degrees_eq_twice_card_edges`), the degree condition for Eulerian trails
(`SimpleGraph.Walk.IsEulerian.even_degree_iff`), the edge count of a tree
(`SimpleGraph.IsTree.card_edgeFinset`), unique paths in trees
(`SimpleGraph.isTree_iff_existsUnique_path`) and the invariance of degrees under isomorphism
(`SimpleGraph.Iso.degree_eq`).

Not formalised: the sufficiency half of Euler's theorem (a connected graph whose degrees are all
even has an Euler circuit), which Mathlib does not yet contain; the lesson proves it by hand.
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace Lumenary.GraphBasics

open Finset

/-! ### Multigraphs, degrees and the handshake lemma -/

-- @region graph_basics.multigraph
-- @provenance definition
/-- A finite **multigraph** on the vertices `0, 1, …, n − 1`, given as a list of edges. An edge
is an unordered pair `s(a, b)` (Mathlib's `Sym2`), and the same pair may occur several times:
parallel edges, like the two bridges joining the island of Kneiphof to each river bank. -/
abbrev Multigraph (n : ℕ) := List (Sym2 (Fin n))
-- @endregion

-- @region graph_basics.ends
-- @provenance definition
/-- How many ends of the edge `e` lie at the vertex `v`: `0`, `1` or `2` (a loop `s(v, v)`
has both of its ends at `v`). -/
def ends {n : ℕ} (v : Fin n) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun a b => (if a = v then 1 else 0) + (if b = v then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩
-- @endregion

-- @region graph_basics.degree
-- @provenance definition
/-- The **degree** of `v` in `G`: the number of edge-ends at `v`. -/
def degree {n : ℕ} (G : Multigraph n) (v : Fin n) : ℕ := (G.map (ends v)).sum
-- @endregion

-- @region graph_basics.handshake
-- @provenance independent
/-- **The handshake lemma:** the degrees add up to twice the number of edges. Induction on the
list of edges: an edge `s(a, b)` contributes one end at `a` and one at `b`, so adding it raises
the total degree by exactly `2`. -/
theorem handshake {n : ℕ} (G : Multigraph n) : ∑ v, degree G v = 2 * G.length := by
  induction G with
  | nil => simp [degree]
  | cons e G ih =>
    have he : ∑ v, ends v e = 2 := by
      induction e using Sym2.ind with
      | h a b => simp [ends, sum_add_distrib]
    simp only [degree, List.map_cons, List.sum_cons, sum_add_distrib, List.length_cons] at ih ⊢
    rw [he, ih]
    omega
-- @endregion

-- @region graph_basics.even_card_odd_degree
-- @provenance independent
/-- **The number of odd-degree vertices is even.** Split the degree sum into the odd-degree and
the even-degree vertices. The total is even (handshake lemma) and the even-degree part is even,
so the odd-degree part is even; but a sum of odd numbers is even only when there is an even
number of them. -/
theorem even_card_odd_degree {n : ℕ} (G : Multigraph n) :
    Even #{v | Odd (degree G v)} := by
  set O := ({v | Odd (degree G v)} : Finset (Fin n))
  -- each odd degree is `2q + 1`, each even degree is `2q`
  have hodd : ∑ v ∈ O, degree G v = 2 * ∑ v ∈ O, degree G v / 2 + #O := by
    rw [mul_sum, card_eq_sum_ones, ← sum_add_distrib]
    refine sum_congr rfl fun v hv => ?_
    have h1 := Nat.odd_iff.1 (mem_filter.1 hv).2
    have h2 := Nat.div_add_mod (degree G v) 2
    omega
  have heven : ∑ v ∈ univ.filter (fun v => ¬ Odd (degree G v)), degree G v =
      2 * ∑ v ∈ univ.filter (fun v => ¬ Odd (degree G v)), degree G v / 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun v hv => ?_
    have h1 := Nat.not_odd_iff.1 (mem_filter.1 hv).2
    have h2 := Nat.div_add_mod (degree G v) 2
    omega
  have htotal := handshake G
  rw [← sum_filter_add_sum_filter_not univ (fun v => Odd (degree G v)), hodd, heven] at htotal
  rw [Nat.even_iff]
  omega
-- @endregion

/-! ### Walks, Euler trails and Euler circuits -/

-- @region graph_basics.walk_edges
-- @provenance definition
/-- The edges crossed by a walk that visits the vertices `w₀, w₁, …, wₘ` in this order:
`s(w₀, w₁), s(w₁, w₂), …, s(wₘ₋₁, wₘ)`. -/
def walkEdges {n : ℕ} : List (Fin n) → Multigraph n
  | a :: b :: rest => s(a, b) :: walkEdges (b :: rest)
  | _ => []
-- @endregion

-- @region graph_basics.is_euler_trail
-- @provenance definition
/-- `w` is an **Euler trail** of `G`: a walk whose edges are exactly the edges of `G`, each
crossed once (the two lists are rearrangements of each other). -/
def IsEulerTrail {n : ℕ} (G : Multigraph n) (w : List (Fin n)) : Prop :=
  w ≠ [] ∧ (walkEdges w).Perm G
-- @endregion

-- @region graph_basics.is_euler_circuit
-- @provenance definition
/-- An **Euler circuit** is an Euler trail that ends where it started. -/
def IsEulerCircuit {n : ℕ} (G : Multigraph n) (w : List (Fin n)) : Prop :=
  IsEulerTrail G w ∧ w.head? = w.getLast?
-- @endregion

-- @region graph_basics.degree_walk_edges
-- @provenance independent
/-- **Counting edge-ends along a walk.** Each time a walk passes *through* a vertex it uses two
edge-ends there, one arriving and one leaving; only the start and the finish are left with a
single end. Precisely: for the walk `a, …` whose last vertex is `rest.getLastD a`, the degree of
`v` in the walk's edges, plus `1` if the walk starts at `v`, plus `1` if it finishes at `v`, is
twice the number of visits to `v`. Induction on the walk. -/
theorem degree_walkEdges {n : ℕ} (a : Fin n) (rest : List (Fin n)) (v : Fin n) :
    degree (walkEdges (a :: rest)) v + (if a = v then 1 else 0) +
      (if rest.getLastD a = v then 1 else 0) = 2 * (a :: rest).count v := by
  induction rest generalizing a with
  | nil =>
    simp only [walkEdges, degree, List.map_nil, List.sum_nil, List.getLastD_nil,
      List.count_singleton, beq_iff_eq]
    by_cases hav : a = v <;> simp [hav]
  | cons b rest ih =>
    have h := ih b
    have hab : ends v s(a, b) = (if a = v then 1 else 0) + (if b = v then 1 else 0) := rfl
    simp only [walkEdges, degree, List.map_cons, List.sum_cons, List.getLastD_cons,
      List.count_cons, beq_iff_eq, hab] at h ⊢
    by_cases hav : a = v <;> by_cases hbv : b = v <;> simp [hav, hbv] at h ⊢ <;> omega
-- @endregion

-- @region graph_basics.degree_perm
-- @provenance independent
/-- Rearranging the list of edges does not change any degree. -/
theorem degree_perm {n : ℕ} {G H : Multigraph n} (h : G.Perm H) (v : Fin n) :
    degree G v = degree H v :=
  (h.map (ends v)).sum_eq
-- @endregion

-- @region graph_basics.euler_circuit_even
-- @provenance independent
/-- **Euler's theorem, necessity (circuits).** If a multigraph has an Euler circuit, every
vertex has even degree: the circuit's start and finish coincide, so every visit to a vertex
uses an even number of edge-ends there. -/
theorem euler_circuit_even {n : ℕ} {G : Multigraph n} {w : List (Fin n)}
    (h : IsEulerCircuit G w) (v : Fin n) : Even (degree G v) := by
  obtain ⟨⟨hne, hperm⟩, hends⟩ := h
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  -- the walk finishes where it starts
  have hlast : rest.getLastD a = a := by
    simp only [List.head?_cons, List.getLast?_cons, Option.some.injEq] at hends
    rw [List.getLastD_eq_getLast?]
    exact hends.symm
  have key := degree_walkEdges a rest v
  rw [hlast, degree_perm hperm v] at key
  rw [Nat.even_iff]
  by_cases hav : a = v <;> simp [hav] at key <;> omega
-- @endregion

-- @region graph_basics.euler_trail_odd
-- @provenance independent
/-- **Euler's theorem, necessity (trails).** In an Euler trail, every vertex of odd degree is
the start or the finish of the trail. So a multigraph with more than two odd-degree vertices
has no Euler trail. -/
theorem euler_trail_odd {n : ℕ} {G : Multigraph n} {w : List (Fin n)}
    (h : IsEulerTrail G w) (v : Fin n) (hv : Odd (degree G v)) :
    w.head? = some v ∨ w.getLast? = some v := by
  obtain ⟨hne, hperm⟩ := h
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have key := degree_walkEdges a rest v
  rw [degree_perm hperm v] at key
  rw [List.head?_cons, List.getLast?_cons, ← List.getLastD_eq_getLast?]
  rw [Nat.odd_iff] at hv
  by_contra hcon
  simp only [not_or, Option.some.injEq] at hcon
  simp only [hcon.1, hcon.2, ite_false] at key
  omega
-- @endregion

-- @region graph_basics.konigsberg
-- @provenance definition
/-- **The bridges of Königsberg** (1736). Land masses: `0` = the island of Kneiphof,
`1` = the north bank, `2` = the south bank, `3` = the eastern island. Seven bridges: two from
Kneiphof to each bank, one from Kneiphof to the eastern island, and one from each bank to the
eastern island. -/
def konigsberg : Multigraph 4 :=
  [s(0, 1), s(0, 1), s(0, 2), s(0, 2), s(0, 3), s(1, 3), s(2, 3)]
-- @endregion

-- @region graph_basics.konigsberg_degrees
-- @provenance independent
/-- The degrees of the four land masses are `5, 3, 3, 3` — all odd. Lean counts the bridge
ends. -/
theorem konigsberg_degrees :
    degree konigsberg 0 = 5 ∧ degree konigsberg 1 = 3 ∧ degree konigsberg 2 = 3 ∧
      degree konigsberg 3 = 3 := by
  decide
-- @endregion

-- @region graph_basics.konigsberg_no_euler_trail
-- @provenance independent
/-- **There is no walk crossing every bridge of Königsberg exactly once.** All four land masses
have odd degree, so by `euler_trail_odd` each of the four would have to be the start or the
finish of the walk — but a walk has only one start and one finish. -/
theorem konigsberg_no_euler_trail : ¬ ∃ w, IsEulerTrail konigsberg w := by
  rintro ⟨w, hw⟩
  obtain ⟨d0, d1, d2, d3⟩ := konigsberg_degrees
  have h0 := euler_trail_odd hw 0 (by rw [d0]; decide)
  have h1 := euler_trail_odd hw 1 (by rw [d1]; decide)
  have h2 := euler_trail_odd hw 2 (by rw [d2]; decide)
  have h3 := euler_trail_odd hw 3 (by rw [d3]; decide)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> simp_all
-- @endregion

/-! ### The same facts in Mathlib's `SimpleGraph` -/

-- @region graph_basics.handshake_library
-- @provenance library
/-- The handshake lemma for Mathlib's simple graphs. This applies
`SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem handshake_library {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  G.sum_degrees_eq_twice_card_edges
-- @endregion

-- @region graph_basics.eulerian_even_degree_iff
-- @provenance library
/-- Euler's degree condition in Mathlib: if `p` is an Eulerian trail from `u` to `v` (it uses
every edge exactly once), then `w` has even degree exactly when it is not an end of an open
trail. This applies `SimpleGraph.Walk.IsEulerian.even_degree_iff`. -/
theorem eulerian_even_degree_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v : V} {p : G.Walk u v} (hp : p.IsEulerian) (w : V) :
    Even (G.degree w) ↔ (u ≠ v → w ≠ u ∧ w ≠ v) :=
  hp.even_degree_iff
-- @endregion

/-! ### Trees -/

-- @region graph_basics.tree_card_edges
-- @provenance library
/-- **A tree with `n` vertices has `n − 1` edges** (stated as `|E| + 1 = |V|`). This applies
Mathlib's `SimpleGraph.IsTree.card_edgeFinset`, whose proof pairs each vertex other than a
chosen root with the first edge of its unique path to the root. -/
theorem tree_card_edges {V : Type*} [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : G.IsTree) : #G.edgeFinset + 1 = Fintype.card V :=
  hG.card_edgeFinset
-- @endregion

-- @region graph_basics.tree_unique_path
-- @provenance library
/-- **Trees are exactly the graphs with a unique path between any two vertices** (and at
least one vertex). This applies Mathlib's `SimpleGraph.isTree_iff_existsUnique_path`. -/
theorem tree_unique_path {V : Type*} {G : SimpleGraph V} :
    G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath :=
  SimpleGraph.isTree_iff_existsUnique_path
-- @endregion

-- @region graph_basics.tree_two_leaves
-- @provenance independent
/-- **Every finite tree with at least two vertices has at least two leaves** (vertices of
degree `1`). Degree counting: the degrees add up to `2|E| = 2(n − 1)`; every degree is at least
`1` because the tree is connected; if at most one vertex had degree `1`, the others would have
degree at least `2` and the sum would be at least `2n − 1`. -/
theorem tree_two_leaves {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsTree) :
    2 ≤ #{v | G.degree v = 1} := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hedges := hG.card_edgeFinset
  have hpos : ∀ v, 1 ≤ G.degree v := fun v => hG.connected.preconnected.degree_pos_of_nontrivial v
  -- the leaves contribute their number to the degree sum …
  have hleaves : ∑ v ∈ univ.filter (fun v => G.degree v = 1), G.degree v =
      #(univ.filter fun v => G.degree v = 1) := by
    rw [card_eq_sum_ones]
    exact sum_congr rfl fun v hv => (mem_filter.1 hv).2
  -- … and every other vertex has degree at least 2
  have hrest : 2 * #(univ.filter fun v => ¬ G.degree v = 1) ≤
      ∑ v ∈ univ.filter (fun v => ¬ G.degree v = 1), G.degree v := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun v hv => ?_
    have := hpos v
    have := (mem_filter.1 hv).2
    omega
  have hsplit := sum_filter_add_sum_filter_not univ (fun v => G.degree v = 1) (fun v => G.degree v)
  have hcard := card_filter_add_card_filter_not (s := univ) (fun v => G.degree v = 1)
  rw [card_univ] at hcard
  omega
-- @endregion

/-! ### Isomorphism -/

-- @region graph_basics.iso_degree
-- @provenance library
/-- **An isomorphism preserves degrees:** if `f : G ≃g H` then `v` and `f v` have the same
degree. This applies Mathlib's `SimpleGraph.Iso.degree_eq`. -/
theorem iso_degree {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : G ≃g H) (v : V) : H.degree (f v) = G.degree v :=
  f.degree_eq v
-- @endregion

-- @region graph_basics.path_not_iso_star
-- @provenance independent
/-- **Same counts, different graphs.** The path `0 — 1 — 2 — 3` and the star with centre `0`
both have four vertices and three edges, and both are trees. They are not isomorphic: the star's
centre has degree `3`, an isomorphism would send it to a vertex of degree `3` in the path, and
every vertex of the path has degree at most `2`. -/
theorem path_not_iso_star :
    IsEmpty (SimpleGraph.pathGraph 4 ≃g SimpleGraph.starGraph (0 : Fin 4)) := by
  constructor
  intro f
  have hstar : (SimpleGraph.starGraph (0 : Fin 4)).degree 0 = 3 := by decide
  have hpath : ∀ v, (SimpleGraph.pathGraph 4).degree v ≤ 2 := by decide
  have h := iso_degree f (f.symm 0)
  rw [f.apply_symm_apply, hstar] at h
  have := hpath (f.symm 0)
  omega
-- @endregion

end Lumenary.GraphBasics
