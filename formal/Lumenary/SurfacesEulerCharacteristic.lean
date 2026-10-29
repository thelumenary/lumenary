/-
The Lumenary — formal mathematics
Surfaces, polyhedra and the Euler characteristic.

Euler's formula itself — `V - E + F = 2` for a connected graph drawn in the plane — needs the
notion of the faces of a plane drawing, which Mathlib does not yet have. What we formalise is
everything that follows from it by counting, proved here from scratch
(`@provenance independent`): there are exactly five Platonic solids; a ball made of
pentagons and hexagons with three at each vertex has exactly twelve pentagons; a simple plane
graph has `E ≤ 3V - 6`, so `K₅` and `K₃,₃` are not planar; Descartes's total angle defect is
`2π χ`; and the Euler characteristic of a connected sum is `χ₁ + χ₂ - 2`. Mathlib supplies the
graph-theoretic base case of the proof of Euler's formula (`@provenance library`): a finite
tree has one fewer edge than vertices.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases

namespace Lumenary.SurfacesEulerCharacteristic

/-! ### Cell counts and the Euler characteristic -/

-- @region surfaces_euler_characteristic.cells
-- @provenance definition
/-- The numbers of vertices, edges and faces of a surface divided into polygons. -/
structure Cells where
  /-- number of vertices -/
  V : ℕ
  /-- number of edges -/
  E : ℕ
  /-- number of faces -/
  F : ℕ
-- @endregion

-- @region surfaces_euler_characteristic.euler
-- @provenance definition
/-- The Euler characteristic `χ = V - E + F`, an integer (it can be negative). -/
def euler (c : Cells) : ℤ := (c.V : ℤ) - c.E + c.F
-- @endregion

-- @region surfaces_euler_characteristic.euler_examples
-- @provenance independent
/-- The tetrahedron, cube and icosahedron have `χ = 2`; the picture-frame torus
(`V = 16, E = 32, F = 16`) has `χ = 0`. -/
theorem euler_examples :
    euler ⟨4, 6, 4⟩ = 2 ∧ euler ⟨8, 12, 6⟩ = 2 ∧ euler ⟨12, 30, 20⟩ = 2 ∧
      euler ⟨16, 32, 16⟩ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
-- @endregion

/-! ### Consequences of Euler's formula -/

-- @region surfaces_euler_characteristic.platonic_solids
-- @provenance independent
/-- **There are exactly five Platonic solids.** Suppose a polyhedron with `V - E + F = 2` has
every face a `p`-gon and `q` faces at every vertex, with `p, q ≥ 3`. Counting edge–face and
edge–vertex incidences gives `p F = 2E` and `q V = 2E`. Multiplying Euler's formula by `p q`
gives `E (2p + 2q - pq) = 2pq > 0`, so `(p - 2)(q - 2) < 4`; hence `p, q ≤ 5`, and checking
the remaining cases leaves exactly the tetrahedron, octahedron, cube, icosahedron and
dodecahedron, with their numbers of vertices, edges and faces. -/
theorem platonic_solids (p q V E F : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) (hF : p * F = 2 * E)
    (hV : q * V = 2 * E) (hEuler : V + F = E + 2) :
    (p = 3 ∧ q = 3 ∧ V = 4 ∧ E = 6 ∧ F = 4) ∨
    (p = 3 ∧ q = 4 ∧ V = 6 ∧ E = 12 ∧ F = 8) ∨
    (p = 4 ∧ q = 3 ∧ V = 8 ∧ E = 12 ∧ F = 6) ∨
    (p = 3 ∧ q = 5 ∧ V = 12 ∧ E = 30 ∧ F = 20) ∨
    (p = 5 ∧ q = 3 ∧ V = 20 ∧ E = 30 ∧ F = 12) := by
  -- Euler's formula times `p q`: `2E (p + q) = E p q + 2 p q`.
  have key : 2 * E * (p + q) = E * (p * q) + 2 * (p * q) :=
    calc 2 * E * (p + q) = p * (q * V) + q * (p * F) := by rw [hV, hF]; ring
      _ = p * q * (V + F) := by ring
      _ = p * q * (E + 2) := by rw [hEuler]
      _ = E * (p * q) + 2 * (p * q) := by ring
  -- So `(p - 2)(q - 2) < 4`, which bounds `p` and `q`.
  have hp5 : p ≤ 5 := by
    by_contra hcon
    push Not at hcon
    have : 2 * (p + q) ≤ p * q := by nlinarith
    nlinarith [key, this]
  have hq5 : q ≤ 5 := by
    by_contra hcon
    push Not at hcon
    have : 2 * (p + q) ≤ p * q := by nlinarith
    nlinarith [key, this]
  interval_cases p <;> interval_cases q <;> omega
-- @endregion

-- @region surfaces_euler_characteristic.twelve_pentagons
-- @provenance independent
/-- **The football theorem.** A polyhedron whose faces are `P` pentagons and `H` hexagons,
with exactly three faces at each vertex, has exactly `12` pentagons — however many hexagons it
has (football: `H = 20`; the C₆₀ molecule; geodesic domes; many virus shells). From
`5P + 6H = 2E`, `3V = 2E` and `V - E + (P + H) = 2`: multiply Euler's formula by `6`. -/
theorem twelve_pentagons (P H V E : ℕ) (hfaces : 5 * P + 6 * H = 2 * E) (hvert : 3 * V = 2 * E)
    (hEuler : V + (P + H) = E + 2) : P = 12 := by
  omega
-- @endregion

-- @region surfaces_euler_characteristic.edge_bound
-- @provenance independent
/-- **A simple plane graph has at most `3V - 6` edges.** In a drawing with `V - E + F = 2`
where every face is bounded by at least `3` edges, counting edge–face incidences gives
`3F ≤ 2E`; substituting into Euler's formula gives `E + 6 ≤ 3V`. -/
theorem edge_bound (V E F : ℕ) (hEuler : V + F = E + 2) (hfaces : 3 * F ≤ 2 * E) :
    E + 6 ≤ 3 * V := by
  omega
-- @endregion

-- @region surfaces_euler_characteristic.k5_not_planar
-- @provenance independent
/-- **`K₅` is not planar.** It has `V = 5` and `E = 10`, but `edge_bound` would need
`10 + 6 ≤ 15`. So no number of faces `F` is compatible with Euler's formula and `3F ≤ 2E`. -/
theorem k5_not_planar : ¬ ∃ F : ℕ, 5 + F = 10 + 2 ∧ 3 * F ≤ 2 * 10 := by
  rintro ⟨F, h1, h2⟩
  have := edge_bound 5 10 F h1 h2
  omega
-- @endregion

-- @region surfaces_euler_characteristic.k33_not_planar
-- @provenance independent
/-- **`K₃,₃` is not planar** (the three-utilities puzzle). It has `V = 6`, `E = 9`, and no
triangles (it is bipartite), so every face would have at least `4` edges: `4F ≤ 2E = 18`.
Euler's formula forces `F = 5`, and `20 > 18`. -/
theorem k33_not_planar : ¬ ∃ F : ℕ, 6 + F = 9 + 2 ∧ 4 * F ≤ 2 * 9 := by
  rintro ⟨F, h1, h2⟩
  omega
-- @endregion

-- @region surfaces_euler_characteristic.descartes_defect
-- @provenance independent
/-- **Descartes's theorem on angle defects** (the discrete Gauss–Bonnet theorem). On a
polyhedron with `V` vertices, `E` edges and faces with `n₁, …, n_F` sides, the angles of an
`n`-gon add up to `(n - 2) π`, and `∑ nᵢ = 2E`. The *total angle defect* — `2π` per vertex
minus all the face angles — is then `2π (V - E + F)`; for a sphere-like polyhedron, `4π`. -/
theorem descartes_defect {F : ℕ} (V E : ℕ) (sides : Fin F → ℕ)
    (hsides : ∑ i, sides i = 2 * E) :
    2 * Real.pi * V - ∑ i, ((sides i : ℝ) - 2) * Real.pi =
      2 * Real.pi * ((V : ℝ) - E + F) := by
  have hsum : ∑ i, ((sides i : ℝ) - 2) * Real.pi = (2 * E - 2 * F) * Real.pi := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    have h : ∑ i, (sides i : ℝ) = 2 * E := by exact_mod_cast hsides
    rw [h]
    simp
    ring
  rw [hsum]
  ring
-- @endregion

/-! ### Building surfaces -/

-- @region surfaces_euler_characteristic.connected_sum
-- @provenance definition
/-- The cell counts of a **connected sum**: remove an `n`-gon face from each surface and glue
the two boundary polygons together. The `n` vertices and `n` edges of the two boundaries are
identified in pairs, and two faces disappear. -/
def connectedSum (c₁ c₂ : Cells) (n : ℕ) : Cells :=
  ⟨c₁.V + c₂.V - n, c₁.E + c₂.E - n, c₁.F + c₂.F - 2⟩
-- @endregion

-- @region surfaces_euler_characteristic.euler_connected_sum
-- @provenance independent
/-- **`χ(M # N) = χ(M) + χ(N) - 2`.** The `n` lost vertices and `n` lost edges cancel and only
the two lost faces count. (Geometrically each surface must have an `n`-gon face to remove; the
hypotheses here only ensure that the natural-number subtractions in `connectedSum` do not
truncate.) Consequently the connected sum of `g` tori has `χ = 2 - 2g`, and of `k` projective
planes `χ = 2 - k`. -/
theorem euler_connected_sum (c₁ c₂ : Cells) (n : ℕ) (hV : n ≤ c₁.V) (hE : n ≤ c₁.E)
    (hF₁ : 1 ≤ c₁.F) (hF₂ : 1 ≤ c₂.F) :
    euler (connectedSum c₁ c₂ n) = euler c₁ + euler c₂ - 2 := by
  unfold euler connectedSum
  simp only
  omega
-- @endregion

-- @region surfaces_euler_characteristic.subdivision_invariant
-- @provenance independent
/-- **Refining a subdivision does not change `χ`.** The three elementary refinements — put a
new vertex in the middle of an edge (`V + 1`, `E + 1`), cut a face by a diagonal (`E + 1`,
`F + 1`), or put a new vertex inside a face joined to one corner (`V + 1`, `E + 1`) — each
leave `V - E + F` unchanged. (That any two subdivisions have a common refinement is the hard
part of the invariance theorem, and is not formalised here.) -/
theorem subdivision_invariant (c : Cells) :
    euler ⟨c.V + 1, c.E + 1, c.F⟩ = euler c ∧ euler ⟨c.V, c.E + 1, c.F + 1⟩ = euler c := by
  unfold euler
  constructor <;> push_cast <;> ring
-- @endregion

/-! ### Mathlib: trees, the base case of Euler's formula -/

-- @region surfaces_euler_characteristic.tree_edges
-- @provenance library
/-- **A finite tree has `E = V - 1`.** Drawn in the plane, a tree has one face, so it satisfies
`V - E + F = 2`: this is the base case of the proof of Euler's formula by deleting edges of
cycles. This is Mathlib's `SimpleGraph.IsTree.card_edgeFinset`. -/
theorem tree_edges {W : Type*} [Fintype W] (G : SimpleGraph W) [Fintype G.edgeSet]
    (hG : G.IsTree) : G.edgeFinset.card + 1 = Fintype.card W :=
  hG.card_edgeFinset
-- @endregion

-- @region surfaces_euler_characteristic.connected_edges
-- @provenance library
/-- **A connected graph has `V ≤ E + 1`**, i.e. `E - V + 2 ≥ 1`: a plane drawing of a connected
graph has at least one face, as Euler's formula predicts. Mathlib proves it by choosing a
spanning tree: `SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`. -/
theorem connected_edges {W : Type*} (G : SimpleGraph W) (hG : G.Connected) :
    Nat.card W ≤ Nat.card G.edgeSet + 1 :=
  hG.card_vert_le_card_edgeSet_add_one
-- @endregion

end Lumenary.SurfacesEulerCharacteristic
