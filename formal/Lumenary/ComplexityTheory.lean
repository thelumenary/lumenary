/-
The Lumenary — formal mathematics
Computational complexity: Boolean satisfiability, certificates, brute-force search, and
polynomial-time reductions between graph problems.

Proved here (`@provenance independent`): CNF formulas with their evaluation (the polynomial-time
*verifier* for SAT); the brute-force algorithm that tries all `2 ^ n` assignments, with a proof
that it is correct and that the search space has exactly `2 ^ n` elements; unsatisfiability of the
pigeonhole formula PHP(3, 2) by running that algorithm; and the correctness of the reductions
INDEPENDENT-SET ↔ VERTEX-COVER (complement the set) and CLIQUE ↔ INDEPENDENT-SET (complement the
graph), including the bookkeeping of sizes `k ↦ n - k`.

From Mathlib (`@provenance library`): `SimpleGraph.isVertexCover_compl`,
`SimpleGraph.isIndepSet_compl`, and `SimpleGraph.IsClique.card_le_of_colorable`.

Not formalised: running times. Lean functions carry no cost model here, so statements such as
"`CNF.eval` runs in linear time" or "SAT is NP-complete" are explained in the lesson but not
proved in this file. (Mathlib has a Turing-machine notion of polynomial-time computability,
`Turing.TM2ComputableInPolyTime`; the Cook–Levin theorem has been formalised in Coq and in
Isabelle, but not in Mathlib.)
-/
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Lumenary.ComplexityTheory

/-! ### Boolean formulas in conjunctive normal form -/

-- @region complexity_theory.literal
-- @provenance definition
/-- A literal over the variables `x₀, …, x_{n-1}`: a variable together with a sign
(`pos = true` for `xᵢ`, `pos = false` for `¬xᵢ`). -/
structure Literal (n : ℕ) where
  var : Fin n
  pos : Bool
  deriving DecidableEq
-- @endregion

-- @region complexity_theory.clause
-- @provenance definition
/-- A clause is a disjunction of literals, stored as a list. -/
abbrev Clause (n : ℕ) := List (Literal n)
-- @endregion

-- @region complexity_theory.cnf
-- @provenance definition
/-- A CNF formula is a conjunction of clauses, stored as a list. -/
abbrev CNF (n : ℕ) := List (Clause n)
-- @endregion

-- @region complexity_theory.assignment
-- @provenance definition
/-- A truth assignment gives every variable a value. -/
abbrev Assignment (n : ℕ) := Fin n → Bool
-- @endregion

-- @region complexity_theory.literal_eval
-- @provenance definition
/-- The value of a literal under an assignment. -/
def Literal.eval {n : ℕ} (a : Assignment n) (l : Literal n) : Bool :=
  if l.pos then a l.var else !a l.var
-- @endregion

-- @region complexity_theory.clause_eval
-- @provenance definition
/-- A clause is true when at least one of its literals is true. -/
def Clause.eval {n : ℕ} (a : Assignment n) (c : Clause n) : Bool :=
  c.any (Literal.eval a)
-- @endregion

-- @region complexity_theory.cnf_eval
-- @provenance definition
/-- **The verifier for SAT.** A formula is true when every clause is true. Checking a proposed
assignment (a *certificate*) is a single pass over the formula: linear time in its length. -/
def CNF.eval {n : ℕ} (a : Assignment n) (φ : CNF n) : Bool :=
  φ.all (Clause.eval a)
-- @endregion

-- @region complexity_theory.satisfiable
-- @provenance definition
/-- A formula is satisfiable if some assignment makes it true — "some certificate passes the
verifier". This is the shape of every problem in NP. -/
def Satisfiable {n : ℕ} (φ : CNF n) : Prop :=
  ∃ a : Assignment n, φ.eval a = true
-- @endregion

/-! ### Brute force: correct, and exponential -/

-- @region complexity_theory.all_assignments
-- @provenance definition
/-- The list of all assignments to `n` variables, built by choosing the value of `x₀` and
recursing on the rest. -/
def allAssignments : (n : ℕ) → List (Assignment n)
  | 0 => [Fin.elim0]
  | n + 1 => (allAssignments n).flatMap fun a => [Fin.cons false a, Fin.cons true a]
-- @endregion

-- @region complexity_theory.length_all_assignments
-- @provenance independent
/-- **The search space doubles with every variable**: there are exactly `2 ^ n` assignments. -/
theorem length_allAssignments (n : ℕ) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allAssignments, List.length_flatMap, List.length_cons, List.length_nil]
    rw [List.map_const', List.sum_replicate, ih, smul_eq_mul, pow_succ, Nat.mul_comm]
-- @endregion

-- @region complexity_theory.mem_all_assignments
-- @provenance independent
/-- Every assignment occurs in `allAssignments n`. Induction on `n`: an assignment to `n + 1`
variables is its value at `x₀` consed onto an assignment to the remaining `n`
(`Fin.cons_self_tail`). -/
theorem mem_allAssignments : ∀ (n : ℕ) (a : Assignment n), a ∈ allAssignments n
  | 0, a => by
    have : a = Fin.elim0 := funext fun i => i.elim0
    simp [allAssignments, this]
  | n + 1, a => by
    simp only [allAssignments, List.mem_flatMap]
    refine ⟨Fin.tail a, mem_allAssignments n _, ?_⟩
    have h : Fin.cons (a 0) (Fin.tail a) = a := Fin.cons_self_tail a
    cases h0 : a 0 <;> simp_all
-- @endregion

-- @region complexity_theory.brute_force
-- @provenance definition
/-- The exponential-time algorithm: run the verifier on all `2 ^ n` assignments. -/
def bruteForce {n : ℕ} (φ : CNF n) : Bool :=
  (allAssignments n).any fun a => φ.eval a
-- @endregion

-- @region complexity_theory.brute_force_correct
-- @provenance independent
/-- **Brute force is correct**: it answers `true` exactly for the satisfiable formulas.
So SAT is decidable; the open question is whether it can be decided in polynomial time. -/
theorem bruteForce_correct {n : ℕ} (φ : CNF n) : bruteForce φ = true ↔ Satisfiable φ := by
  unfold bruteForce Satisfiable
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, -, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, mem_allAssignments n a, ha⟩
-- @endregion

-- @region complexity_theory.php32
-- @provenance definition
/-- The pigeonhole formula PHP(3, 2): variable `2 i + j` says "pigeon `i` sits in hole `j`"
(`i < 3`, `j < 2`). Every pigeon sits in some hole, and no hole holds two pigeons. -/
def php32 : CNF 6 :=
  [ [⟨0, true⟩, ⟨1, true⟩], [⟨2, true⟩, ⟨3, true⟩], [⟨4, true⟩, ⟨5, true⟩],
    [⟨0, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨4, false⟩], [⟨2, false⟩, ⟨4, false⟩],
    [⟨1, false⟩, ⟨3, false⟩], [⟨1, false⟩, ⟨5, false⟩], [⟨3, false⟩, ⟨5, false⟩] ]
-- @endregion

-- @region complexity_theory.php32_unsat
-- @provenance independent
/-- Three pigeons do not fit into two holes: PHP(3, 2) is unsatisfiable. The proof *runs* the
brute-force algorithm (64 assignments, checked by `decide`) and then uses its correctness.
For PHP(n + 1, n) the same method needs `2 ^ (n (n + 1))` assignments, and Haken (1985) proved
that even resolution proofs of these formulas must be exponentially long. -/
theorem php32_unsat : ¬ Satisfiable php32 := by
  rw [← bruteForce_correct]
  decide
-- @endregion

/-! ### Reductions between graph problems -/

-- @region complexity_theory.indep_iff_cover_compl
-- @provenance independent
/-- **Independent sets and vertex covers are complements.** `s` contains no edge if and only if
every edge has an endpoint outside `s`. -/
theorem indepSet_iff_vertexCover_compl {V : Type*} (G : SimpleGraph V) (s : Set V) :
    G.IsIndepSet s ↔ G.IsVertexCover sᶜ := by
  constructor
  · intro hs v w hadj
    by_contra h
    simp only [Set.mem_compl_iff, not_or, not_not] at h
    exact hs h.1 h.2 hadj.ne hadj
  · intro hc v hv w hw _ hadj
    rcases hc hadj with h | h
    · exact h hv
    · exact h hw
-- @endregion

-- @region complexity_theory.indep_iff_cover_compl_library
-- @provenance library
/-- The same fact from Mathlib: `SimpleGraph.isVertexCover_compl`. -/
theorem indepSet_iff_vertexCover_compl' {V : Type*} (G : SimpleGraph V) (s : Set V) :
    G.IsIndepSet s ↔ G.IsVertexCover sᶜ :=
  SimpleGraph.isVertexCover_compl.symm
-- @endregion

-- @region complexity_theory.indep_reduces_to_cover
-- @provenance independent
/-- **The reduction INDEPENDENT-SET ≤ₚ VERTEX-COVER.** A graph on `n` vertices has an
independent set of size at least `k` if and only if it has a vertex cover of size at most
`n - k`. The reduction maps `(G, k)` to `(G, n - k)` — clearly polynomial time. -/
theorem indep_reduces_to_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (hk : k ≤ Fintype.card V) :
    (∃ s : Finset V, k ≤ s.card ∧ G.IsIndepSet (s : Set V)) ↔
      (∃ c : Finset V, c.card ≤ Fintype.card V - k ∧ G.IsVertexCover (c : Set V)) := by
  constructor
  · rintro ⟨s, hks, hs⟩
    refine ⟨sᶜ, ?_, ?_⟩
    · rw [Finset.card_compl]
      omega
    · rw [Finset.coe_compl]
      exact (indepSet_iff_vertexCover_compl G s).1 hs
  · rintro ⟨c, hc, hcov⟩
    refine ⟨cᶜ, ?_, ?_⟩
    · rw [Finset.card_compl]
      omega
    · rw [Finset.coe_compl, indepSet_iff_vertexCover_compl, compl_compl]
      exact hcov
-- @endregion

-- @region complexity_theory.clique_iff_indep_compl
-- @provenance independent
/-- **The reduction CLIQUE ≤ₚ INDEPENDENT-SET**: `s` is a clique in `G` iff it is independent in
the complement graph `Gᶜ`, whose edges join distinct non-adjacent vertices. -/
theorem clique_iff_indepSet_compl {V : Type*} (G : SimpleGraph V) (s : Set V) :
    G.IsClique s ↔ Gᶜ.IsIndepSet s := by
  constructor
  · intro hs v hv w hw hne hadj
    exact ((SimpleGraph.compl_adj G v w).1 hadj).2 (hs hv hw hne)
  · intro hs v hv w hw hne
    by_contra hnot
    exact hs hv hw hne ((SimpleGraph.compl_adj G v w).2 ⟨hne, hnot⟩)
-- @endregion

-- @region complexity_theory.clique_iff_indep_compl_library
-- @provenance library
/-- The same fact from Mathlib: `SimpleGraph.isIndepSet_compl`. -/
theorem clique_iff_indepSet_compl' {V : Type*} (G : SimpleGraph V) (s : Set V) :
    G.IsClique s ↔ Gᶜ.IsIndepSet s :=
  (SimpleGraph.isIndepSet_compl G).symm
-- @endregion

/-! ### Colouring -/

-- @region complexity_theory.k4_not_three_colorable
-- @provenance library
/-- `K₄` is not 3-colourable: a clique of size 4 needs 4 colours. This applies Mathlib's
`SimpleGraph.IsClique.card_le_of_colorable` to the whole vertex set. Deciding 3-colourability
of an arbitrary graph is NP-complete, so no short general argument like this one is expected. -/
theorem k4_not_three_colorable : ¬ (⊤ : SimpleGraph (Fin 4)).Colorable 3 := by
  intro h
  have hclique :
      (⊤ : SimpleGraph (Fin 4)).IsClique ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) := by
    rw [Finset.coe_univ]
    exact SimpleGraph.isClique_univ.2 rfl
  have h43 := hclique.card_le_of_colorable h
  simp at h43
-- @endregion

end Lumenary.ComplexityTheory
