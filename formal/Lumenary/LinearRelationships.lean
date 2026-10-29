/-
The Lumenary — formal mathematics
Linear relationships and simultaneous equations: slope, the form `y = m·x + b`, constant rate
of change, where two lines meet, and why a system of linear equations has one solution, none,
or infinitely many.

We work in core Lean's rational numbers `Rat`. A point of the plane is a pair of numbers, and
"the point lies on the line `y = m·x + b`" is the equation `y = m * x + b`. The theorems are
proved here from the arithmetic of `Rat` (`@provenance independent`), with `slope` as our own
small definition. Routine rearrangements of sums and products are finished by `grind`.
Mathlib develops the same ideas in great generality: lines as affine subspaces, slopes via
`slope` in `Mathlib.LinearAlgebra.AffineSpace.Slope`, and systems of equations as matrices
(`Matrix.det`, Cramer's rule `Matrix.cramer`).
-/

namespace Lumenary.LinearRelationships

/-! ### Slope -/

-- @region linear_relationships.slope
-- @provenance definition
/-- The slope of the line through `(x₁, y₁)` and `(x₂, y₂)`: rise over run,
`(y₂ − y₁) / (x₂ − x₁)`. It is meaningful only when `x₁ ≠ x₂`; the theorems below always
assume that. (Lean's `Rat` sets `a / 0 = 0`, which is a convention, not a slope.) -/
def slope (x₁ y₁ x₂ y₂ : Rat) : Rat := (y₂ - y₁) / (x₂ - x₁)
-- @endregion

-- @region linear_relationships.slope_symm
-- @provenance independent
/-- The order of the two points does not matter, as long as we subtract in the same order on
top and bottom: `(y₂ − y₁)/(x₂ − x₁) = (y₁ − y₂)/(x₁ − x₂)`. -/
theorem slope_symm (x₁ y₁ x₂ y₂ : Rat) (h : x₁ ≠ x₂) :
    slope x₁ y₁ x₂ y₂ = slope x₂ y₂ x₁ y₁ := by
  have h₁ : x₂ - x₁ ≠ 0 := fun h0 => h (by grind)
  have h₂ : x₁ - x₂ ≠ 0 := fun h0 => h (by grind)
  unfold slope
  grind
-- @endregion

-- @region linear_relationships.rise_eq_slope_mul_run
-- @provenance independent
/-- On the line `y = m·x + b`, the rise between two points is `m` times the run:
`(m·x₂ + b) − (m·x₁ + b) = m·(x₂ − x₁)`. The intercept `b` cancels and the distributive law
does the rest. -/
theorem rise_eq_slope_mul_run (m b x₁ x₂ : Rat) :
    (m * x₂ + b) - (m * x₁ + b) = m * (x₂ - x₁) := by
  grind
-- @endregion

-- @region linear_relationships.slope_of_line
-- @provenance independent
/-- The slope between **any** two points of the line `y = m·x + b` is `m`. This is why a line
has one well-defined slope: the rise is `m·(run)`, so rise ÷ run is `m` for every choice of
points. -/
theorem slope_of_line (m b x₁ x₂ : Rat) (h : x₁ ≠ x₂) :
    slope x₁ (m * x₁ + b) x₂ (m * x₂ + b) = m := by
  have hrun : x₂ - x₁ ≠ 0 := fun h0 => h (by grind)
  unfold slope
  rw [rise_eq_slope_mul_run]
  exact Rat.mul_div_cancel hrun
-- @endregion

-- @region linear_relationships.linear_of_constant_rate
-- @provenance independent
/-- The converse: a relationship with a **constant rate of change** `m` — every rise is `m`
times its run — is linear, `f(x) = m·x + b` with `b = f(0)`. Take the two points `0` and `x`. -/
theorem linear_of_constant_rate (f : Rat → Rat) (m : Rat)
    (h : ∀ x₁ x₂, f x₂ - f x₁ = m * (x₂ - x₁)) : ∀ x, f x = m * x + f 0 := by
  intro x
  have hx := h 0 x
  grind
-- @endregion

-- @region linear_relationships.line_through_point
-- @provenance independent
/-- The line with slope `m` passes through `(x₁, y₁)` exactly when its intercept is
`b = y₁ − m·x₁`. So a slope and one point determine the line: `y = m·x + (y₁ − m·x₁)`, which
is the same as the point–slope form `y − y₁ = m·(x − x₁)`. -/
theorem line_through_point (m b x₁ y₁ : Rat) : m * x₁ + b = y₁ ↔ b = y₁ - m * x₁ := by
  constructor
  · intro h
    grind
  · intro h
    rw [h]
    grind
-- @endregion

-- @region linear_relationships.line_through_two_points
-- @provenance independent
/-- Two points with different `x`-coordinates determine a line: with `m` the slope between
them and `b = y₁ − m·x₁`, the line `y = m·x + b` passes through both points. The second point
works because `m·(x₂ − x₁) = y₂ − y₁` (`Rat.div_mul_cancel`). -/
theorem line_through_two_points (x₁ y₁ x₂ y₂ : Rat) (h : x₁ ≠ x₂) :
    slope x₁ y₁ x₂ y₂ * x₁ + (y₁ - slope x₁ y₁ x₂ y₂ * x₁) = y₁ ∧
      slope x₁ y₁ x₂ y₂ * x₂ + (y₁ - slope x₁ y₁ x₂ y₂ * x₁) = y₂ := by
  have hrun : x₂ - x₁ ≠ 0 := fun h0 => h (by grind)
  have hm : slope x₁ y₁ x₂ y₂ * (x₂ - x₁) = y₂ - y₁ := by
    unfold slope
    exact Rat.div_mul_cancel hrun
  constructor
  · grind
  · calc slope x₁ y₁ x₂ y₂ * x₂ + (y₁ - slope x₁ y₁ x₂ y₂ * x₁)
        = slope x₁ y₁ x₂ y₂ * (x₂ - x₁) + y₁ := by grind
      _ = (y₂ - y₁) + y₁ := by rw [hm]
      _ = y₂ := by grind
-- @endregion

-- @region linear_relationships.proportional_iff
-- @provenance independent
/-- A linear relationship `y = m·x + b` is **proportional** (`y = k·x` for some constant `k`)
exactly when `b = 0`, i.e. when its graph passes through the origin. Forwards: put `x = 0`. -/
theorem proportional_iff (m b : Rat) : (∃ k, ∀ x, m * x + b = k * x) ↔ b = 0 := by
  constructor
  · intro ⟨k, hk⟩
    have h0 := hk 0
    grind
  · intro hb
    exact ⟨m, fun x => by rw [hb]; grind⟩
-- @endregion

-- @region linear_relationships.comp_linear
-- @provenance independent
/-- Doing one linear function after another gives a linear function: applying
`x ↦ m₂·x + b₂` and then `x ↦ m₁·x + b₁` gives `x ↦ (m₁·m₂)·x + (m₁·b₂ + b₁)`.
The slopes multiply. -/
theorem comp_linear (m₁ b₁ m₂ b₂ x : Rat) :
    m₁ * (m₂ * x + b₂) + b₁ = (m₁ * m₂) * x + (m₁ * b₂ + b₁) := by
  calc m₁ * (m₂ * x + b₂) + b₁ = m₁ * (m₂ * x) + m₁ * b₂ + b₁ := by rw [Rat.mul_add]
    _ = (m₁ * m₂) * x + (m₁ * b₂ + b₁) := by grind
-- @endregion

/-! ### Where two lines meet -/

-- @region linear_relationships.lines_meet_once
-- @provenance independent
/-- Two lines with **different** slopes meet in exactly one point: `m₁·x + b₁ = m₂·x + b₂`
holds exactly when `x = (b₂ − b₁)/(m₁ − m₂)`. (Subtract, then divide by `m₁ − m₂ ≠ 0`.) -/
theorem lines_meet_once (m₁ b₁ m₂ b₂ x : Rat) (h : m₁ ≠ m₂) :
    m₁ * x + b₁ = m₂ * x + b₂ ↔ x = (b₂ - b₁) / (m₁ - m₂) := by
  have hd : m₁ - m₂ ≠ 0 := fun h0 => h (by grind)
  constructor
  · intro heq
    have hx : (m₁ - m₂) * x = b₂ - b₁ := by grind
    calc x = (m₁ - m₂) * x / (m₁ - m₂) := by rw [Rat.mul_comm, Rat.mul_div_cancel hd]
      _ = (b₂ - b₁) / (m₁ - m₂) := by rw [hx]
  · intro hx
    have hmul : (m₁ - m₂) * x = b₂ - b₁ := by
      rw [hx, Rat.mul_comm, Rat.div_mul_cancel hd]
    grind
-- @endregion

-- @region linear_relationships.parallel_never_meet
-- @provenance independent
/-- Two different lines with the **same** slope never meet: if `b₁ ≠ b₂` then
`m·x + b₁ ≠ m·x + b₂` for every `x` — the gap between them is always `b₂ − b₁`. -/
theorem parallel_never_meet (m b₁ b₂ x : Rat) (h : b₁ ≠ b₂) : m * x + b₁ ≠ m * x + b₂ := by
  intro heq
  exact h (Rat.add_left_cancel (m * x) heq)
-- @endregion

/-! ### Simultaneous equations -/

-- @region linear_relationships.chickens_rabbits
-- @provenance independent
/-- The *Sunzi Suanjing* puzzle: chickens and rabbits in a cage have `35` heads and `94` legs.
Elimination: subtract twice the heads equation from the legs equation to get `2r = 24`, so
`r = 12` rabbits and `c = 23` chickens. -/
theorem chickens_rabbits (c r : Rat) (h₁ : c + r = 35) (h₂ : 2 * c + 4 * r = 94) :
    c = 23 ∧ r = 12 := by
  have h2r : 2 * r = 24 :=
    calc 2 * r = (2 * c + 4 * r) - 2 * (c + r) := by grind
      _ = 94 - 2 * 35 := by rw [h₂, h₁]
      _ = 24 := by grind
  have hr : r = 12 := by grind
  have hc : c = 23 := by grind
  exact ⟨hc, hr⟩
-- @endregion

-- @region linear_relationships.celsius_fahrenheit
-- @provenance independent
/-- The temperature at which the Celsius and Fahrenheit scales show the same number: the
system `F = (9/5)·C + 32`, `F = C`. Substituting the second into the first leaves
`(9/5)·C + 32 = C`, whose only solution is `C = −40`. -/
theorem celsius_fahrenheit (c : Rat) : 9 / 5 * c + 32 = c ↔ c = -40 := by
  constructor
  · intro h
    grind
  · intro h
    rw [h]
    grind
-- @endregion

-- @region linear_relationships.cramer
-- @provenance independent
/-- A system `a·x + b·y = e`, `c·x + d·y = f` with `a·d − b·c ≠ 0` has exactly one solution.
Eliminating `y` (multiply the equations by `d` and `b` and subtract) gives
`(a·d − b·c)·x = e·d − b·f`; eliminating `x` gives `(a·d − b·c)·y = a·f − e·c`. -/
theorem cramer (a b c d e f : Rat) (h : a * d - b * c ≠ 0) :
    ∃ x y, (a * x + b * y = e ∧ c * x + d * y = f) ∧
      ∀ x' y', a * x' + b * y' = e → c * x' + d * y' = f → x' = x ∧ y' = y := by
  refine ⟨(e * d - b * f) / (a * d - b * c), (a * f - e * c) / (a * d - b * c), ⟨?_, ?_⟩, ?_⟩
  · grind
  · grind
  · intro x' y' h₁ h₂
    have hx : (a * d - b * c) * x' = e * d - b * f := by grind
    have hy : (a * d - b * c) * y' = a * f - e * c := by grind
    constructor
    · calc x' = (a * d - b * c) * x' / (a * d - b * c) := by
            rw [Rat.mul_comm, Rat.mul_div_cancel h]
        _ = (e * d - b * f) / (a * d - b * c) := by rw [hx]
    · calc y' = (a * d - b * c) * y' / (a * d - b * c) := by
            rw [Rat.mul_comm, Rat.mul_div_cancel h]
        _ = (a * f - e * c) / (a * d - b * c) := by rw [hy]
-- @endregion

-- @region linear_relationships.parallel_system
-- @provenance independent
/-- A system with no solution: `x + y = 3` and `2x + 2y = 10`. Doubling the first equation
gives `2x + 2y = 6`, so a solution would make `6 = 10`. (The graphs are parallel lines.) -/
theorem parallel_system : ¬ ∃ x y : Rat, x + y = 3 ∧ 2 * x + 2 * y = 10 := by
  intro ⟨x, y, h₁, h₂⟩
  have h610 : (6 : Rat) = 10 :=
    calc (6 : Rat) = 2 * (x + y) := by rw [h₁]; grind
      _ = 2 * x + 2 * y := by grind
      _ = 10 := h₂
  exact absurd h610 (by decide)
-- @endregion

-- @region linear_relationships.same_line_system
-- @provenance independent
/-- A system with infinitely many solutions: `x + 2y = 4` and `2x + 4y = 8` describe the same
line, and for every number `t` the point `(4 − 2t, t)` solves both. -/
theorem same_line_system (t : Rat) :
    (4 - 2 * t) + 2 * t = 4 ∧ 2 * (4 - 2 * t) + 4 * t = 8 := by
  constructor <;> grind
-- @endregion

-- @region linear_relationships.between_solutions
-- @provenance independent
/-- If two points solve the linear equation `a·x + b·y = e`, so does every point
`((1 − t)·x₁ + t·x₂, (1 − t)·y₁ + t·y₂)` on the line through them:
the left side becomes `(1 − t)·e + t·e = e`. Applied to each equation of a system, this shows
that a system with two solutions has a whole line of solutions. -/
theorem between_solutions (a b e x₁ y₁ x₂ y₂ t : Rat)
    (h₁ : a * x₁ + b * y₁ = e) (h₂ : a * x₂ + b * y₂ = e) :
    a * ((1 - t) * x₁ + t * x₂) + b * ((1 - t) * y₁ + t * y₂) = e :=
  calc a * ((1 - t) * x₁ + t * x₂) + b * ((1 - t) * y₁ + t * y₂)
      = (1 - t) * (a * x₁ + b * y₁) + t * (a * x₂ + b * y₂) := by grind
    _ = (1 - t) * e + t * e := by rw [h₁, h₂]
    _ = e := by grind
-- @endregion

-- @region linear_relationships.between_points_distinct
-- @provenance independent
/-- Different values of `t` give different points, as long as the two starting points differ.
So "two different solutions" really does give **infinitely many**: one for each number `t`. -/
theorem between_points_distinct (x₁ y₁ x₂ y₂ s t : Rat) (hne : (x₁, y₁) ≠ (x₂, y₂))
    (hst : s ≠ t) :
    ((1 - s) * x₁ + s * x₂, (1 - s) * y₁ + s * y₂) ≠
      ((1 - t) * x₁ + t * x₂, (1 - t) * y₁ + t * y₂) := by
  intro heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hx, hy⟩ := heq
  have hst' : s - t ≠ 0 := fun h0 => hst (by grind)
  have hx' : (s - t) * (x₂ - x₁) = 0 := by grind
  have hy' : (s - t) * (y₂ - y₁) = 0 := by grind
  have ex : x₂ - x₁ = 0 := (Rat.mul_eq_zero.mp hx').resolve_left hst'
  have ey : y₂ - y₁ = 0 := (Rat.mul_eq_zero.mp hy').resolve_left hst'
  exact hne (by rw [show x₁ = x₂ by grind, show y₁ = y₂ by grind])
-- @endregion

end Lumenary.LinearRelationships
