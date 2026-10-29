/-
The Lumenary — formal mathematics
Networks and puzzles: dots and lines, degrees, the handshake rule, and one-stroke tracing
("for grown-ups" companion to the Grades 3–5 lesson on networks).

A network is written as a list of lines; each line is a pair of dot numbers, so two lines may
join the same two dots (like two bridges between the same banks of a river). The degree of a
dot is the number of line ends at it. We prove, for every network:

* the handshake rule: the degrees add up to twice the number of lines;
* the key half of Euler's theorem: in a route that uses every line exactly once, a dot of odd
  degree must be where the route starts or where it ends.

From these, Lean shows that the seven bridges of Königsberg cannot be crossed in one walk. The
other half of Euler's theorem (with 0 or 2 odd dots a connected figure *can* be traced) is not
formalised here. Core Lean 4 only. Mathlib analogue: `SimpleGraph.sum_degrees_eq_twice_card_edges`
and `SimpleGraph.Walk.IsEulerian.card_odd_degree` (for simple graphs, without parallel lines).
-/

namespace Lumenary.NetworksPuzzles

/-! ### Dots, lines and degrees -/

-- @region networks_puzzles.network
-- @provenance definition
/-- A network is a list of lines. Each line joins two dots, which are numbered `0, 1, 2, …`.
The same pair of dots may be joined by several lines. -/
abbrev Network := List (Nat × Nat)
-- @endregion

-- @region networks_puzzles.ends
-- @provenance definition
/-- How many ends of the line `e` sit at the dot `v`: `0`, `1` or `2`. -/
def ends (v : Nat) (e : Nat × Nat) : Nat :=
  (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)
-- @endregion

-- @region networks_puzzles.degree
-- @provenance definition
/-- The degree of the dot `v`: the total number of line ends at `v`. -/
def degree (g : Network) (v : Nat) : Nat :=
  (g.map (ends v)).sum
-- @endregion

-- @region networks_puzzles.konigsberg
-- @provenance definition
/-- The seven bridges of Königsberg. Dot `0` is the island in the middle (Kneiphof), dots `1`
and `2` are the north and south banks, and dot `3` is the eastern land between the two arms of
the river. Two bridges join the island to each bank. -/
def konigsberg : Network :=
  [(0, 1), (0, 1), (0, 2), (0, 2), (0, 3), (1, 3), (2, 3)]
-- @endregion

-- @region networks_puzzles.konigsberg_degrees
-- @provenance independent
/-- The degrees in Königsberg are `5, 3, 3, 3`: all four dots are odd. Lean counts them. -/
theorem konigsberg_degrees :
    degree konigsberg 0 = 5 ∧ degree konigsberg 1 = 3 ∧
    degree konigsberg 2 = 3 ∧ degree konigsberg 3 = 3 := by
  decide
-- @endregion

/-! ### The handshake rule -/

-- @region networks_puzzles.total
-- @provenance definition
/-- `total n f` adds up `f 0 + f 1 + ⋯ + f (n - 1)`: one number for each of the dots
`0, 1, …, n - 1`. -/
def total : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => total n f + f n
-- @endregion

-- @region networks_puzzles.total_add
-- @provenance independent
/-- Adding two numbers at every dot, then totalling, is the same as totalling each and adding. -/
theorem total_add (n : Nat) (f g : Nat → Nat) :
    total n (fun v => f v + g v) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih]; omega
-- @endregion

-- @region networks_puzzles.total_one_dot
-- @provenance independent
/-- Counting, over the dots `0, …, n - 1`, the dots equal to `a` gives `1` if `a` is one of them
and `0` otherwise. -/
theorem total_one_dot (a n : Nat) :
    total n (fun v => if a = v then 1 else 0) = if a < n then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [total, ih]
    by_cases h1 : a < n
    · have h2 : a ≠ n := by omega
      have h3 : a < n + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : a = n
      · simp [h2]
      · have h3 : ¬ a < n + 1 := by omega
        simp [h1, h2, h3]
-- @endregion

-- @region networks_puzzles.handshake
-- @provenance independent
/-- **The handshake rule.** If every line of `g` joins dots among `0, …, n - 1`, then the degrees
of these dots add up to twice the number of lines: each line has two ends, and each end is
counted at exactly one dot. -/
theorem handshake (g : Network) (n : Nat) (h : ∀ e ∈ g, e.1 < n ∧ e.2 < n) :
    total n (degree g) = 2 * g.length := by
  induction g with
  | nil =>
    show total n (fun _ => 0) = 0
    induction n with
    | zero => rfl
    | succ n ih => simp [total, ih]
  | cons e es ih =>
    have he := h e (List.mem_cons_self ..)
    have hes : ∀ x ∈ es, x.1 < n ∧ x.2 < n := fun x hx => h x (List.mem_cons_of_mem e hx)
    have split : degree (e :: es) =
        fun v => ((if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)) + degree es v := by
      funext v
      simp [degree, ends]
    rw [split, total_add, total_add, total_one_dot, total_one_dot, ih hes]
    simp [he.1, he.2]
    omega
-- @endregion

-- @region networks_puzzles.konigsberg_handshake
-- @provenance independent
/-- In Königsberg the degrees add up to `5 + 3 + 3 + 3 = 14 = 2 × 7`. This uses our own
`handshake` theorem (proved above) for the seven bridges, whose ends all lie among the dots
`0, 1, 2, 3`; `decide` checks that last fact. -/
theorem konigsberg_handshake : total 4 (degree konigsberg) = 2 * konigsberg.length :=
  handshake konigsberg 4 (by decide)
-- @endregion

/-! ### Routes and one-stroke tracing -/

-- @region networks_puzzles.steps
-- @provenance definition
/-- The lines walked along by a route that visits the dots `x, y, z, …` in this order. -/
def steps : List Nat → Network
  | x :: y :: rest => (x, y) :: steps (y :: rest)
  | _ => []
-- @endregion

-- @region networks_puzzles.last_dot
-- @provenance definition
/-- The last dot of the route that starts at `x` and then visits the dots of `rest`. -/
def lastDot : Nat → List Nat → Nat
  | x, [] => x
  | _, y :: rest => lastDot y rest
-- @endregion

-- @region networks_puzzles.visits
-- @provenance definition
/-- How many times the dot `v` appears in a list of dots. -/
def visits (v : Nat) : List Nat → Nat
  | [] => 0
  | x :: rest => (if x = v then 1 else 0) + visits v rest
-- @endregion

-- @region networks_puzzles.route_degree
-- @provenance independent
/-- **Every visit uses two line ends.** Along a route, each time we pass through a dot we
arrive on one line and leave on another. Only the start and the end lose one of the two. So
the line ends at `v` used by the route, plus one if `v` is the start, plus one if `v` is the
end, make exactly twice the number of visits to `v`. -/
theorem route_degree (v : Nat) (rest : List Nat) : ∀ x : Nat,
    degree (steps (x :: rest)) v + (if x = v then 1 else 0)
      + (if lastDot x rest = v then 1 else 0) = 2 * visits v (x :: rest) := by
  induction rest with
  | nil =>
    intro x
    by_cases hx : x = v <;> simp [steps, lastDot, visits, degree, hx]
  | cons y rest ih =>
    intro x
    have h := ih y
    simp only [steps, lastDot, visits, degree, ends, List.map, List.sum_cons] at h ⊢
    -- Decide, for each of the three dots `x`, `y` and the last dot, whether it is `v`.
    by_cases hx : x = v <;> by_cases hy : y = v <;> by_cases hl : lastDot y rest = v <;>
      simp only [hx, hy, hl, ite_true, ite_false] at h ⊢ <;> omega
-- @endregion

-- @region networks_puzzles.norm
-- @provenance definition
/-- A line from `a` to `b` is the same line as from `b` to `a`. `norm` writes every line with
its smaller dot first, so that the direction of travel no longer matters. -/
def norm (e : Nat × Nat) : Nat × Nat :=
  if e.1 ≤ e.2 then e else (e.2, e.1)
-- @endregion

-- @region networks_puzzles.traces
-- @provenance definition
/-- The route that starts at `x` and then visits the dots of `rest` **traces `g` in one
stroke** when the lines it walks along are exactly the lines of `g`, each used once: the two
lists of lines are rearrangements of each other (`List.Perm`), ignoring direction. -/
def Traces (g : Network) (x : Nat) (rest : List Nat) : Prop :=
  List.Perm ((steps (x :: rest)).map norm) (g.map norm)
-- @endregion

-- @region networks_puzzles.degree_eq_of_traces
-- @provenance independent
/-- A route that traces `g` uses exactly as many line ends at each dot as `g` has: turning lines
round does not change their ends, and rearranging lines does not change a total (core Lean's
`List.Perm.sum_nat`). -/
theorem degree_eq_of_traces {g : Network} {x : Nat} {rest : List Nat}
    (h : Traces g x rest) (v : Nat) : degree (steps (x :: rest)) v = degree g v := by
  have ends_norm : ∀ e : Nat × Nat, ends v (norm e) = ends v e := by
    intro e
    unfold ends norm
    split <;> simp <;> omega
  have key : ∀ l : Network, degree (l.map norm) v = degree l v := by
    intro l
    induction l with
    | nil => rfl
    | cons e es ih =>
      simp only [degree, List.map, List.sum_cons] at ih ⊢
      rw [ends_norm, ih]
  rw [← key, ← key g]
  exact (h.map (ends v)).sum_nat
-- @endregion

-- @region networks_puzzles.odd_dot_is_an_end
-- @provenance independent
/-- **Euler's observation.** If a route traces `g` in one stroke, every dot of odd degree is the
start or the end of the route. (Every other dot is passed through, and each visit uses an even
number, two, of line ends.) -/
theorem odd_dot_is_an_end {g : Network} {x : Nat} {rest : List Nat}
    (h : Traces g x rest) (v : Nat) (odd : degree g v % 2 = 1) :
    v = x ∨ v = lastDot x rest := by
  have hv := route_degree v rest x
  rw [degree_eq_of_traces h v] at hv
  by_cases h1 : x = v
  · exact Or.inl h1.symm
  · by_cases h2 : lastDot x rest = v
    · exact Or.inr h2.symm
    · simp only [h1, h2, ite_false] at hv
      omega
-- @endregion

-- @region networks_puzzles.konigsberg_impossible
-- @provenance independent
/-- **The bridges of Königsberg cannot all be crossed in one walk** that uses each bridge exactly
once, wherever it starts. All four dots have odd degree, so all four would have to be the start
or the end — but a route has only one start and one end. -/
theorem konigsberg_impossible (x : Nat) (rest : List Nat) : ¬ Traces konigsberg x rest := by
  intro h
  obtain ⟨d0, d1, d2, d3⟩ := konigsberg_degrees
  have h0 := odd_dot_is_an_end h 0 (by rw [d0])
  have h1 := odd_dot_is_an_end h 1 (by rw [d1])
  have h2 := odd_dot_is_an_end h 2 (by rw [d2])
  have h3 := odd_dot_is_an_end h 3 (by rw [d3])
  omega
-- @endregion

-- @region networks_puzzles.closed_route_all_even
-- @provenance independent
/-- A route that traces `g` and comes back to where it started leaves **no** dot of odd degree:
with the start equal to the end, every dot has even degree. -/
theorem closed_route_all_even {g : Network} {x : Nat} {rest : List Nat}
    (h : Traces g x rest) (closed : lastDot x rest = x) (v : Nat) : degree g v % 2 = 0 := by
  have hv := route_degree v rest x
  rw [degree_eq_of_traces h v, closed] at hv
  by_cases h1 : x = v
  · simp only [h1, ite_true] at hv
    omega
  · simp only [h1, ite_false] at hv
    omega
-- @endregion

/-! ### A figure that *can* be traced -/

-- @region networks_puzzles.house
-- @provenance definition
/-- The "house" puzzle: a square `0`–`1`–`2`–`3` (bottom left, bottom right, top right, top
left) with both diagonals, and a roof whose top is dot `4`. Eight lines in all. -/
def house : Network :=
  [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3), (3, 4), (4, 2)]
-- @endregion

-- @region networks_puzzles.house_degrees
-- @provenance independent
/-- In the house, dots `0` and `1` are odd (degree 3) and the other dots are even. -/
theorem house_degrees :
    degree house 0 = 3 ∧ degree house 1 = 3 ∧ degree house 2 = 4 ∧
    degree house 3 = 4 ∧ degree house 4 = 2 := by
  decide
-- @endregion

-- @region networks_puzzles.house_traced
-- @provenance independent
/-- The route `0, 1, 2, 3, 0, 2, 4, 3, 1` traces the house in one stroke: it starts at one odd
dot and ends at the other. Lean checks that the eight lines walked are exactly the eight lines
of the house. -/
theorem house_traced : Traces house 0 [1, 2, 3, 0, 2, 4, 3, 1] := by
  unfold Traces
  decide
-- @endregion

-- @region networks_puzzles.house_needs_odd_start
-- @provenance independent
/-- A route tracing the house must start or end at dot `0`, and also at dot `1`: the odd dots
are forced to be its two ends. So starting at the roof top `4` can never work. -/
theorem house_needs_odd_start (rest : List Nat) : ¬ Traces house 4 rest := by
  intro h
  obtain ⟨d0, d1, _, _, _⟩ := house_degrees
  have h0 := odd_dot_is_an_end h 0 (by rw [d0])
  have h1 := odd_dot_is_an_end h 1 (by rw [d1])
  omega
-- @endregion

/-! ### Shortest routes -/

-- @region networks_puzzles.roads
-- @provenance definition
/-- Wanjiru's road map, with lengths in kilometres. The places are `0` Home, `1` Well,
`2` School, `3` Bridge and `4` Market; each road is `(place, place, length)`. -/
def roads : List (Nat × Nat × Nat) :=
  [(0, 1, 7), (1, 4, 6), (0, 2, 2), (2, 3, 3), (3, 4, 4), (1, 3, 2)]
-- @endregion

-- @region networks_puzzles.road_length
-- @provenance definition
/-- The length of the road joining towns `a` and `b` (in either direction), or `none` if there
is no such road. -/
def roadLength (a b : Nat) : Option Nat :=
  match roads.find? (fun r => (r.1 == a && r.2.1 == b) || (r.1 == b && r.2.1 == a)) with
  | some r => some r.2.2
  | none => none
-- @endregion

-- @region networks_puzzles.route_length
-- @provenance definition
/-- The length of a route through the given towns: the sum of its road lengths, or `none` if
some step has no road. -/
def routeLength : List Nat → Option Nat
  | a :: b :: rest =>
    match roadLength a b, routeLength (b :: rest) with
    | some d, some r => some (d + r)
    | _, _ => none
  | _ => some 0
-- @endregion

-- @region networks_puzzles.fewest_roads_not_shortest
-- @provenance independent
/-- **Fewest roads is not the same as shortest.** Home → Well → Market uses 2 roads and is
13 km; Home → School → Bridge → Market uses 3 roads but is only 9 km. -/
theorem fewest_roads_not_shortest :
    routeLength [0, 1, 4] = some 13 ∧ routeLength [0, 2, 3, 4] = some 9 := by
  decide
-- @endregion

end Lumenary.NetworksPuzzles
