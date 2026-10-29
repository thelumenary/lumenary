/-
The Lumenary — formal mathematics
Knot theory: Fox colourings and their behaviour under Reidemeister moves, the dihedral quandle,
linking numbers, and the Kauffman bracket and Jones polynomial computed from planar diagram
codes — enough to see by computation that the trefoil's polynomial differs from its mirror's.

What is proved here and what Mathlib provides. Mathlib has no knots: there is no notion of a knot
as an embedding of the circle up to ambient isotopy, and no Reidemeister theorem. It does have
quandles (`Mathlib.Algebra.Quandle`), including the dihedral quandle `Quandle.Dihedral n` whose
operation `a ◃ b = 2a - b` is exactly the Fox colouring rule. So this module is *combinatorial*:
a knot diagram is encoded by finite data (arcs and crossings, or a planar diagram code), and
every statement is about those codes. The *independent* declarations prove: the local algebra
behind invariance of colourings under the three Reidemeister moves, the colouring counts that
tell the unknot, trefoil and figure-eight diagrams apart, linking numbers and their invariance
under the second move, the kink identity `Aδ + A⁻¹ = -A³` behind the Kauffman bracket, and the
bracket and Jones polynomial of the trefoil, its mirror and the figure-eight knot, by evaluating
the state sum (`decide`). The *library* declaration cites self-distributivity of Mathlib's
dihedral quandle.

Not formalised: knots as topological objects, Reidemeister's theorem, and hence the conclusion
that a diagram invariant is a knot invariant. The lesson proves those steps on paper; Lean
checks the algebra and the computations.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Quandle
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination

namespace Lumenary.KnotTheory

open scoped Quandles

/-! ### Fox colourings of knot diagrams -/

-- @region knot_theory.arc_diagram
-- @provenance definition
/-- A knot diagram, recorded by its **arcs** (the unbroken strands, numbered `0, …, arcs - 1`) and
its **crossings**. A crossing `(o, u₁, u₂)` lists the arc `o` passing over and the two arcs `u₁`,
`u₂` that end there, passing under. -/
structure ArcDiagram where
  arcs : ℕ
  crossings : List (Fin arcs × Fin arcs × Fin arcs)
-- @endregion

-- @region knot_theory.is_fox_colouring
-- @provenance definition
/-- A **Fox `p`-colouring** gives each arc a colour in `ZMod p` so that at every crossing
`2 · (over) = (under₁) + (under₂)`. For `p = 3` this says the three colours at a crossing are
all equal or all different — the tricolouring rule. -/
def IsFoxColouring (D : ArcDiagram) (p : ℕ) (c : Fin D.arcs → ZMod p) : Prop :=
  ∀ x ∈ D.crossings, 2 * c x.1 = c x.2.1 + c x.2.2
-- @endregion

-- @region knot_theory.is_fox_colouring_decidable
-- @provenance definition
/-- Whether a colouring is valid can be decided by checking the finitely many crossings. -/
instance isFoxColouringDecidable (D : ArcDiagram) (p : ℕ) (c : Fin D.arcs → ZMod p) :
    Decidable (IsFoxColouring D p c) := by
  unfold IsFoxColouring
  infer_instance
-- @endregion

-- @region knot_theory.unknot_diagram
-- @provenance definition
/-- The simplest diagram of the unknot: a round circle, one arc, no crossings. -/
abbrev unknotDiagram : ArcDiagram := ⟨1, []⟩
-- @endregion

-- @region knot_theory.trefoil_diagram
-- @provenance definition
/-- The standard trefoil diagram: three arcs and three crossings, each arc passing over once. -/
abbrev trefoilDiagram : ArcDiagram := ⟨3, [(0, 1, 2), (1, 2, 0), (2, 0, 1)]⟩
-- @endregion

-- @region knot_theory.figure_eight_diagram
-- @provenance definition
/-- The standard figure-eight diagram: four arcs `0 = A, 1 = B, 2 = C, 3 = D` and four crossings
(over; under, under) = (A; B, C), (C; D, A), (B; C, D), (D; A, B). -/
abbrev figureEightDiagram : ArcDiagram := ⟨4, [(0, 1, 2), (2, 3, 0), (1, 2, 3), (3, 0, 1)]⟩
-- @endregion

-- @region knot_theory.trefoil_tricolourable
-- @provenance independent
/-- **The trefoil diagram is tricolourable**: colour its arcs `0, 1, 2`. At each crossing the
three colours are all different, and `2 · 0 = 1 + 2`, `2 · 1 = 2 + 0`, `2 · 2 = 0 + 1` in
`ZMod 3`. -/
theorem trefoil_tricolourable :
    ∃ c : Fin 3 → ZMod 3, IsFoxColouring trefoilDiagram 3 c ∧ ∃ i j, c i ≠ c j :=
  ⟨![0, 1, 2], by decide, 0, 1, by decide⟩
-- @endregion

-- @region knot_theory.unknot_not_tricolourable
-- @provenance independent
/-- **The round unknot diagram is not tricolourable**: it has one arc, so any colouring uses one
colour. -/
theorem unknot_not_tricolourable :
    ¬ ∃ c : Fin 1 → ZMod 3, IsFoxColouring unknotDiagram 3 c ∧ ∃ i j, c i ≠ c j := by
  rintro ⟨c, -, i, j, hij⟩
  exact hij (by rw [Subsingleton.elim i j])
-- @endregion

-- @region knot_theory.trefoil_three_colourings
-- @provenance independent
/-- The trefoil diagram has exactly `9` Fox `3`-colourings: the `3` constant ones and `6` using
all three colours. Checked by trying all `27` colourings. -/
theorem trefoil_three_colourings :
    Fintype.card {c : Fin 3 → ZMod 3 // IsFoxColouring trefoilDiagram 3 c} = 9 := by
  decide
-- @endregion

-- @region knot_theory.figure_eight_three_colourings
-- @provenance independent
/-- The figure-eight diagram has only the `3` constant Fox `3`-colourings, so it is **not
tricolourable**. Checked by trying all `81` colourings. -/
theorem figure_eight_three_colourings :
    Fintype.card {c : Fin 4 → ZMod 3 // IsFoxColouring figureEightDiagram 3 c} = 3 := by
  decide
-- @endregion

-- @region knot_theory.trefoil_five_colourings
-- @provenance independent
/-- The trefoil diagram has only the `5` constant Fox `5`-colourings (all `125` checked). -/
theorem trefoil_five_colourings :
    Fintype.card {c : Fin 3 → ZMod 5 // IsFoxColouring trefoilDiagram 5 c} = 5 := by
  decide
-- @endregion

-- @region knot_theory.figure_eight_five_colourings
-- @provenance independent
/-- The figure-eight diagram has `25` Fox `5`-colourings — `20` of them non-constant, such as
`A, B, C, D ↦ 0, 1, 4, 3` — so `5`-colourings tell it apart from the trefoil (all `625`
checked). -/
theorem figure_eight_five_colourings :
    Fintype.card {c : Fin 4 → ZMod 5 // IsFoxColouring figureEightDiagram 5 c} = 25 := by
  decide
-- @endregion

/-! ### Why colourings survive Reidemeister moves: the local algebra -/

-- @region knot_theory.reidemeister_one
-- @provenance independent
/-- **Move I (a kink).** At a kink the over arc is also one of the under arcs, so the colouring
rule reads `2a = a + b`, which forces `b = a`: the kink adds no freedom and removes none. -/
theorem reidemeister_one {R : Type*} [CommRing R] (a b : R) : 2 * a = a + b ↔ b = a := by
  constructor
  · intro h
    linear_combination -h
  · intro h
    rw [h]
    ring
-- @endregion

-- @region knot_theory.reidemeister_two
-- @provenance independent
/-- **Move II.** A strand of colour `x` passes over another strand twice; the lower strand is cut
into pieces `a`, `m`, `b`. The two crossings say `2x = a + m` and `2x = m + b`, which hold exactly
when the middle colour is `m = 2x - a` and the outgoing colour is `b = a`. So colourings before
and after the move correspond one to one. -/
theorem reidemeister_two {R : Type*} [CommRing R] (x a m b : R) :
    (2 * x = a + m ∧ 2 * x = m + b) ↔ (m = 2 * x - a ∧ b = a) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination -h1, by linear_combination h1 - h2⟩
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring
-- @endregion

-- @region knot_theory.reidemeister_three
-- @provenance independent
/-- **Move III.** Strands with incoming colours `t` (top), `m` (middle) and `b` (bottom) cross;
the bottom strand passes under the other two in either order. Writing `x ◃ y = 2x - y` for the
colour of a strand `y` after it passes under `x`, the outgoing bottom colour is
`t ◃ (m ◃ b)` on one side of the move and `(t ◃ m) ◃ (t ◃ b)` on the other. They agree: this is
**self-distributivity**, the quandle axiom. -/
theorem reidemeister_three {R : Type*} [CommRing R] (t m b : R) :
    2 * t - (2 * m - b) = 2 * (2 * t - m) - (2 * t - b) := by
  ring
-- @endregion

-- @region knot_theory.dihedral_quandle_self_distrib
-- @provenance library
/-- Mathlib's **dihedral quandle** `Quandle.Dihedral n` is `ZMod n` with `a ◃ b = 2a - b`; Fox
colourings are exactly colourings by this quandle. Its self-distributivity is the general form of
`reidemeister_three`. This applies Mathlib's `Shelf.self_distrib` for the instance on
`Quandle.Dihedral n`. -/
theorem dihedral_quandle_self_distrib (n : ℕ) (x y z : Quandle.Dihedral n) :
    x ◃ (y ◃ z) = (x ◃ y) ◃ (x ◃ z) :=
  Shelf.self_distrib
-- @endregion

/-! ### Linking numbers -/

-- @region knot_theory.link_crossing
-- @provenance definition
/-- A crossing of a two-component link diagram: whether it is between the two components (rather
than a component crossing itself), and its sign `±1` (right-handed `+1`, left-handed `-1`). -/
structure LinkCrossing where
  between : Bool
  sign : ℤ
-- @endregion

-- @region knot_theory.linking_sum
-- @provenance definition
/-- The sum of the signs of the crossings *between* the two components. -/
def linkingSum (cs : List LinkCrossing) : ℤ :=
  ((cs.filter (·.between)).map (·.sign)).sum
-- @endregion

-- @region knot_theory.linking_number
-- @provenance definition
/-- The **linking number**: half the sum of the signs of the crossings between the components. -/
def linkingNumber (cs : List LinkCrossing) : ℤ := linkingSum cs / 2
-- @endregion

-- @region knot_theory.hopf_linking_number
-- @provenance independent
/-- The (positive) **Hopf link** has two crossings between its components, both `+1`: linking
number `1`. So it cannot be pulled apart, since the unlink has linking number `0`. -/
theorem hopf_linking_number : linkingNumber [⟨true, 1⟩, ⟨true, 1⟩] = 1 := by
  decide
-- @endregion

-- @region knot_theory.whitehead_linking_number
-- @provenance independent
/-- The **Whitehead link** (in its standard five-crossing diagram) has one self-crossing and
four crossings between its components, with signs `+1, -1, +1, -1`: linking number `0`, although
it is not the unlink. The linking number is not a complete invariant. -/
theorem whitehead_linking_number :
    linkingNumber [⟨false, 1⟩, ⟨true, 1⟩, ⟨true, -1⟩, ⟨true, 1⟩, ⟨true, -1⟩] = 0 := by
  decide
-- @endregion

-- @region knot_theory.linking_sum_reidemeister_two
-- @provenance independent
/-- **Move II does not change the linking sum**: it creates or removes two crossings between the
same strands with opposite signs. (Move I creates a self-crossing, which is not counted; move III
only rearranges crossings without changing their signs.) -/
theorem linking_sum_reidemeister_two (cs : List LinkCrossing) (s : ℤ) :
    linkingSum (cs ++ [⟨true, s⟩, ⟨true, -s⟩]) = linkingSum cs := by
  simp [linkingSum, List.filter_append]
-- @endregion

/-! ### The Kauffman bracket and the Jones polynomial, from planar diagram codes -/

-- @region knot_theory.pd
-- @provenance definition
/-- A **planar diagram (PD) code**: one quadruple `(i, j, k, l)` per crossing. The edges of the
diagram are numbered `1, …, 2n` along the knot; `i` is the incoming under-edge and `j, k, l`
follow it anticlockwise around the crossing (so `k` is the outgoing under-edge). -/
abbrev PD := List (ℕ × ℕ × ℕ × ℕ)
-- @endregion

-- @region knot_theory.all_states
-- @provenance definition
/-- All `2ⁿ` **states**: a choice of smoothing, `true` = A and `false` = B, at each crossing. -/
def allStates : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStates n).flatMap (fun s => [true :: s, false :: s])
-- @endregion

-- @region knot_theory.smoothing
-- @provenance definition
/-- Smoothing a crossing `(i, j, k, l)` joins its four edges in pairs: the **A-smoothing** joins
`i` with `j` and `k` with `l`; the **B-smoothing** joins `i` with `l` and `j` with `k`. -/
def smoothing (x : ℕ × ℕ × ℕ × ℕ) (s : Bool) : List (ℕ × ℕ) :=
  match x with
  | (i, j, k, l) => if s then [(i, j), (k, l)] else [(i, l), (j, k)]
-- @endregion

-- @region knot_theory.merge_labels
-- @provenance definition
/-- One step of counting components: `lab` assigns each edge a representative, and joining edges
`p.1` and `p.2` relabels the whole class of `p.1` with the representative of `p.2`. -/
def mergeLabels (lab : List ℕ) (p : ℕ × ℕ) : List ℕ :=
  let u := lab.getD p.1 0
  let w := lab.getD p.2 0
  lab.map (fun z => if z = u then w else z)
-- @endregion

-- @region knot_theory.loops
-- @provenance definition
/-- The number of **loops** (circles) obtained by smoothing every crossing according to the state:
join the edges as the smoothings say, and count the classes (edges that are their own
representative). -/
def loops (pd : PD) (st : List Bool) : ℕ :=
  let n2 := 2 * pd.length
  let pairs := (List.zipWith smoothing pd st).flatten
  let lab := pairs.foldl mergeLabels (List.range (n2 + 1))
  ((List.range' 1 n2).filter (fun i => lab.getD i 0 = i)).length
-- @endregion

-- @region knot_theory.state_monomials
-- @provenance definition
/-- The contribution `A^(a - b) · δ^(L - 1)` of a state with `a` A-smoothings, `b` B-smoothings
and `L` loops, where `δ = -A² - A⁻²`, expanded by the binomial theorem into monomials
`(exponent, coefficient)`: `δ^N = (-1)^N Σⱼ (N choose j) A^(2N - 4j)`. -/
def stateMonomials (pd : PD) (st : List Bool) : List (ℤ × ℤ) :=
  let a : ℤ := (st.filter id).length
  let b : ℤ := (st.filter (! ·)).length
  let N := loops pd st - 1
  (List.range (N + 1)).map (fun (j : ℕ) =>
    (a - b + 2 * (N : ℤ) - 4 * (j : ℤ), (-1) ^ N * (Nat.choose N j : ℤ)))
-- @endregion

-- @region knot_theory.bracket_monomials
-- @provenance definition
/-- The **Kauffman bracket** state sum `⟨D⟩ = Σ_states A^(a - b) δ^(L - 1)`, as a list of
monomials (not yet collected). -/
def bracketMonomials (pd : PD) : List (ℤ × ℤ) :=
  (allStates pd.length).flatMap (stateMonomials pd)
-- @endregion

-- @region knot_theory.normal_form
-- @provenance definition
/-- The **normal form** of a Laurent polynomial given by monomials: the distinct exponents in
increasing order, each with its total coefficient, dropping zeros. Two lists of monomials define
the same Laurent polynomial exactly when their normal forms are equal. -/
def normalForm (ms : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  ((ms.map Prod.fst).dedup.insertionSort (· ≤ ·)).filterMap (fun e =>
    let c := ((ms.filter (fun m => m.1 = e)).map Prod.snd).sum
    if c = 0 then none else some (e, c))
-- @endregion

-- @region knot_theory.crossing_sign
-- @provenance definition
/-- The **sign** of a crossing `(i, j, k, l)` in a diagram with `2n` edges (`n ≥ 2`): the over
strand runs `l → j` (sign `+1`, right-handed) when `j` follows `l` along the knot, and `j → l`
(sign `-1`) when `l` follows `j`. -/
def crossingSign (n2 : ℕ) (x : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  match x with
  | (_, j, _, l) =>
    if (j + n2 - l) % n2 = 1 then 1 else if (l + n2 - j) % n2 = 1 then -1 else 0
-- @endregion

-- @region knot_theory.writhe
-- @provenance definition
/-- The **writhe**: the sum of the signs of all crossings. -/
def writhe (pd : PD) : ℤ := (pd.map (crossingSign (2 * pd.length))).sum
-- @endregion

-- @region knot_theory.jones_monomials
-- @provenance definition
/-- The normalised bracket `f(D) = (-A³)^(-w(D)) ⟨D⟩`, in normal form. Substituting `A = t^(-1/4)`
turns it into the **Jones polynomial** `V(t)`: the monomial `A^e` becomes `t^(-e/4)`. -/
def jonesMonomials (pd : PD) : List (ℤ × ℤ) :=
  let w := writhe pd
  normalForm ((bracketMonomials pd).map (fun m => (m.1 - 3 * w, (-1) ^ w.natAbs * m.2)))
-- @endregion

-- @region knot_theory.trefoil_pd
-- @provenance definition
/-- A PD code of the **right-handed trefoil** (all three crossings positive). -/
def trefoilPD : PD := [(1, 5, 2, 4), (3, 1, 4, 6), (5, 3, 6, 2)]
-- @endregion

-- @region knot_theory.mirror_trefoil_pd
-- @provenance definition
/-- A PD code of its **mirror image**, the left-handed trefoil: every crossing switched. -/
def mirrorTrefoilPD : PD := [(4, 1, 5, 2), (6, 3, 1, 4), (2, 5, 3, 6)]
-- @endregion

-- @region knot_theory.figure_eight_pd
-- @provenance definition
/-- A PD code of the **figure-eight knot**. -/
def figureEightPD : PD := [(4, 2, 5, 1), (8, 6, 1, 5), (6, 3, 7, 4), (2, 7, 3, 8)]
-- @endregion

-- @region knot_theory.bracket_trefoil
-- @provenance independent
/-- `⟨right-handed trefoil⟩ = A⁻⁷ - A⁻³ - A⁵`, by evaluating the `8`-state sum. -/
theorem bracket_trefoil :
    normalForm (bracketMonomials trefoilPD) = [(-7, 1), (-3, -1), (5, -1)] := by
  decide
-- @endregion

-- @region knot_theory.bracket_mirror_trefoil
-- @provenance independent
/-- `⟨left-handed trefoil⟩ = -A⁻⁵ - A³ + A⁷`: the bracket of the mirror image is obtained by
replacing `A` with `A⁻¹`. -/
theorem bracket_mirror_trefoil :
    normalForm (bracketMonomials mirrorTrefoilPD) = [(-5, -1), (3, -1), (7, 1)] := by
  decide
-- @endregion

-- @region knot_theory.writhe_trefoils
-- @provenance independent
/-- The writhes of the two trefoil diagrams are `+3` and `-3`. -/
theorem writhe_trefoils : writhe trefoilPD = 3 ∧ writhe mirrorTrefoilPD = -3 := by
  decide
-- @endregion

-- @region knot_theory.jones_trefoil
-- @provenance independent
/-- The Jones polynomial of the right-handed trefoil: `f = -A⁻¹⁶ + A⁻¹² + A⁻⁴`, i.e.
`V(t) = t + t³ - t⁴`. -/
theorem jones_trefoil : jonesMonomials trefoilPD = [(-16, -1), (-12, 1), (-4, 1)] := by
  decide
-- @endregion

-- @region knot_theory.jones_mirror_trefoil
-- @provenance independent
/-- The Jones polynomial of the left-handed trefoil: `f = A⁴ + A¹² - A¹⁶`, i.e.
`V(t) = t⁻¹ + t⁻³ - t⁻⁴`. -/
theorem jones_mirror_trefoil : jonesMonomials mirrorTrefoilPD = [(4, 1), (12, 1), (16, -1)] := by
  decide
-- @endregion

-- @region knot_theory.jones_figure_eight
-- @provenance independent
/-- The Jones polynomial of the figure-eight knot, `V(t) = t⁻² - t⁻¹ + 1 - t + t²`, is
symmetric under `t ↦ t⁻¹` — as it must be, since the figure-eight knot is its own mirror image. -/
theorem jones_figure_eight :
    jonesMonomials figureEightPD = [(-8, 1), (-4, -1), (0, 1), (4, -1), (8, 1)] := by
  decide
-- @endregion

-- @region knot_theory.trefoil_jones_ne_mirror
-- @provenance independent
/-- The two trefoils have **different Jones polynomials**. Together with the theorem that the
Jones polynomial is a knot invariant (proved in the lesson, not here), this shows the trefoil is
not equivalent to its mirror image. -/
theorem trefoil_jones_ne_mirror :
    jonesMonomials trefoilPD ≠ jonesMonomials mirrorTrefoilPD := by
  decide
-- @endregion

-- @region knot_theory.kink_identity
-- @provenance independent
/-- **The kink identity.** With `B = A⁻¹` and `δ = -A² - B²`, removing a positive kink multiplies
the bracket by `Aδ + B = -A³` (and a negative kink by `A + Bδ = -B³`). This is why the bracket
is not invariant under move I, and why the factor `(-A³)^(-writhe)` repairs it. -/
theorem kink_identity {R : Type*} [CommRing R] (A B : R) (h : A * B = 1) :
    A * (-A ^ 2 - B ^ 2) + B = -A ^ 3 ∧ A + B * (-A ^ 2 - B ^ 2) = -B ^ 3 := by
  constructor
  · linear_combination (-B) * h
  · linear_combination (-A) * h
-- @endregion

end Lumenary.KnotTheory
