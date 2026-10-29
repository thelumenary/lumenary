/-
The Lumenary — formal mathematics
Linear equations and inequalities: equivalent equations, the moves that keep the solutions
the same, the three possible outcomes for `a·x = b`, and why multiplying an inequality by a
negative number reverses it.

We work in core Lean's rational numbers `Rat`, where every non-zero number can be divided by
(in the integers, `2 * x = 1` has no solution at all). An equation is a statement about a
variable `x`, so "two equations are equivalent" becomes a theorem of the form
`∀ x, (first equation) ↔ (second equation)`. The basic moves are proved here from the
arithmetic of `Rat` (`@provenance independent`); two order facts simply apply core lemmas
(`@provenance library`). Small routine rearrangements are closed by `grind`, which decides
linear arithmetic and normalises sums and products. Mathlib proves the same facts in every
field or ordered field (`mul_left_cancel₀`, `mul_lt_mul_left_of_neg`, …).
-/

namespace Lumenary.LinearEquations

/-! ### Moves that give equivalent equations -/

-- @region linear_equations.add_both_sides
-- @provenance independent
/-- Adding the same number `c` to both sides gives an equivalent equation:
`p = q ↔ p + c = q + c`. Forwards, equal numbers plus `c` are equal. Backwards, the move can
be **undone**: subtract `c` again, `p = (p + c) − c = (q + c) − c = q`. -/
theorem add_both_sides (p q c : Rat) : p = q ↔ p + c = q + c := by
  constructor
  · intro h
    rw [h]
  · intro h
    calc p = p + c - c := Rat.add_sub_cancel.symm
      _ = q + c - c := by rw [h]
      _ = q := Rat.add_sub_cancel
-- @endregion

-- @region linear_equations.mul_both_sides
-- @provenance independent
/-- Multiplying both sides by a **non-zero** number `c` gives an equivalent equation:
`p = q ↔ c·p = c·q`. Backwards, the move is undone by dividing by `c`, which is only possible
because `c ≠ 0` (`Rat.mul_div_cancel`). -/
theorem mul_both_sides (p q c : Rat) (hc : c ≠ 0) : p = q ↔ c * p = c * q := by
  constructor
  · intro h
    rw [h]
  · intro h
    calc p = c * p / c := by rw [Rat.mul_comm, Rat.mul_div_cancel hc]
      _ = c * q / c := by rw [h]
      _ = q := by rw [Rat.mul_comm, Rat.mul_div_cancel hc]
-- @endregion

-- @region linear_equations.mul_zero_not_reversible
-- @provenance independent
/-- Why `c ≠ 0` is needed: multiplying both sides by `0` cannot be undone. `0 · 0 = 0 · 1` is
true, but `0 = 1` is false, so "`0·p = 0·q` implies `p = q`" fails. -/
theorem mul_zero_not_reversible : ¬ ∀ p q : Rat, 0 * p = 0 * q → p = q := by
  intro h
  have h01 : (0 : Rat) = 1 := h 0 1 (by rw [Rat.zero_mul, Rat.zero_mul])
  exact absurd h01 (by decide)
-- @endregion

-- @region linear_equations.extra_solution
-- @provenance independent
/-- Multiplying both sides by an *expression that can be zero* can add solutions. The
equation `x = 3` has only the solution `3`, but after multiplying both sides by `x − 2` the
new equation `(x − 2)·x = (x − 2)·3` is also solved by `x = 2`. -/
theorem extra_solution : ∃ x : Rat, (x - 2) * x = (x - 2) * 3 ∧ x ≠ 3 :=
  ⟨2, by grind, by decide⟩
-- @endregion

-- @region linear_equations.square_eq_double_iff
-- @provenance independent
/-- Dividing by an expression that can be zero can *lose* solutions: `x² = 2x` has the two
solutions `0` and `2`, but "dividing by `x`" leaves only `x = 2`. Proof: `x² − 2x = x(x − 2)`,
and a product is zero exactly when a factor is (`Rat.mul_eq_zero`). -/
theorem square_eq_double_iff (x : Rat) : x * x = 2 * x ↔ x = 0 ∨ x = 2 := by
  constructor
  · intro h
    have hfac : x * (x - 2) = 0 := by grind
    rcases Rat.mul_eq_zero.mp hfac with h0 | h2
    · exact Or.inl h0
    · right
      grind
  · rintro (rfl | rfl) <;> grind
-- @endregion

/-! ### Solving linear equations -/

-- @region linear_equations.solve_both_sides
-- @provenance independent
/-- The worked example `3x + 1 = x + 9`, solved by a chain of equivalent equations, exactly as
in the lesson: subtract `x + 1` from both sides, then multiply both sides by `1/2`. Every step
is an `↔`, so the final answer `x = 4` is not just *a* solution: it is the only one. -/
theorem solve_both_sides (x : Rat) : 3 * x + 1 = x + 9 ↔ x = 4 :=
  calc (3 * x + 1 = x + 9)
        ↔ (3 * x + 1) + (-x - 1) = (x + 9) + (-x - 1) := add_both_sides _ _ _
    _ ↔ 2 * x = 8 := by
        rw [show (3 * x + 1) + (-x - 1) = 2 * x by grind,
          show (x + 9) + (-x - 1) = (8 : Rat) by grind]
    _ ↔ (1 / 2) * (2 * x) = (1 / 2) * 8 := mul_both_sides _ _ _ (by grind)
    _ ↔ x = 4 := by
        rw [show (1 / 2 : Rat) * (2 * x) = x by grind, show (1 / 2 : Rat) * 8 = 4 by grind]
-- @endregion

-- @region linear_equations.solve_fractions
-- @provenance independent
/-- An equation with fractions: `x/3 + 1/2 = (x − 1)/4`. Multiplying both sides by `12`, the
least common multiple of the denominators, clears the fractions: `4x + 6 = 3x − 3`, so
`x = −9`. -/
theorem solve_fractions (x : Rat) : x / 3 + 1 / 2 = (x - 1) / 4 ↔ x = -9 :=
  calc (x / 3 + 1 / 2 = (x - 1) / 4)
        ↔ 12 * (x / 3 + 1 / 2) = 12 * ((x - 1) / 4) := mul_both_sides _ _ _ (by decide)
    _ ↔ 4 * x + 6 = 3 * x - 3 := by
        rw [show 12 * (x / 3 + 1 / 2) = 4 * x + 6 by grind,
          show 12 * ((x - 1) / 4) = 3 * x - 3 by grind]
    _ ↔ x = -9 := by
        constructor <;> intro h <;> grind
-- @endregion

-- @region linear_equations.to_standard_form
-- @provenance independent
/-- Every linear equation `a·x + b = c·x + d` is equivalent to one of the form `A·x = B`:
subtract `c·x + b` from both sides to get `(a − c)·x = d − b`. -/
theorem to_standard_form (a b c d x : Rat) :
    a * x + b = c * x + d ↔ (a - c) * x = d - b := by
  rw [add_both_sides (a * x + b) (c * x + d) (-(c * x) - b)]
  rw [show a * x + b + (-(c * x) - b) = (a - c) * x by grind,
    show c * x + d + (-(c * x) - b) = d - b by grind]
-- @endregion

-- @region linear_equations.ax_eq_b_trichotomy
-- @provenance independent
/-- The three possible outcomes for `a·x = b`:
* if `a ≠ 0` there is exactly one solution, `x = b / a`;
* if `a = 0` and `b ≠ 0` there is no solution (`0·x` is always `0`);
* if `a = 0` and `b = 0` every number is a solution. -/
theorem ax_eq_b_trichotomy (a b : Rat) :
    (a ≠ 0 → ∀ x, a * x = b ↔ x = b / a) ∧
    (a = 0 → b ≠ 0 → ∀ x, a * x ≠ b) ∧
    (a = 0 → b = 0 → ∀ x, a * x = b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ha x
    constructor
    · intro h
      calc x = a * x / a := by rw [Rat.mul_comm, Rat.mul_div_cancel ha]
        _ = b / a := by rw [h]
    · intro h
      rw [h, Rat.mul_comm, Rat.div_mul_cancel ha]
  · intro ha hb x h
    rw [ha, Rat.zero_mul] at h
    exact hb h.symm
  · intro ha hb x
    rw [ha, hb, Rat.zero_mul]
-- @endregion

-- @region linear_equations.two_solutions_all
-- @provenance independent
/-- A linear equation never has exactly two solutions: if two *different* numbers solve
`a·x + b = c·x + d`, then every number does. In standard form `(a − c)·x = d − b`; two
solutions give `(a − c)(x₁ − x₂) = 0` with `x₁ − x₂ ≠ 0`, so `a − c = 0`, then `d − b = 0`. -/
theorem two_solutions_all (a b c d x₁ x₂ : Rat) (hne : x₁ ≠ x₂)
    (h₁ : a * x₁ + b = c * x₁ + d) (h₂ : a * x₂ + b = c * x₂ + d) :
    ∀ x, a * x + b = c * x + d := by
  rw [to_standard_form] at h₁ h₂
  have hprod : (a - c) * (x₁ - x₂) = 0 := by grind
  have hac : a - c = 0 := by
    rcases Rat.mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd (by grind) hne
  intro x
  rw [to_standard_form]
  grind
-- @endregion

-- @region linear_equations.no_solution_example
-- @provenance independent
/-- `2(x + 3) = 2x + 5` has no solution: expanding gives `2x + 6 = 2x + 5`, and subtracting
`2x` from both sides leaves the false statement `6 = 5`. -/
theorem no_solution_example : ¬ ∃ x : Rat, 2 * (x + 3) = 2 * x + 5 := by
  intro ⟨x, h⟩
  have h65 : (6 : Rat) = 5 := by grind
  exact absurd h65 (by decide)
-- @endregion

-- @region linear_equations.identity_example
-- @provenance independent
/-- `3(x − 2) + x = 4x − 6` is true for every `x`: expanding the left side gives
`3x − 6 + x = 4x − 6`. Every number is a solution. -/
theorem identity_example (x : Rat) : 3 * (x - 2) + x = 4 * x - 6 := by
  grind
-- @endregion

-- @region linear_equations.tanks_meet
-- @provenance independent
/-- The two rainwater tanks of the lesson: one holds `500 − 20t` litres after `t` minutes,
the other `100 + 30t`. They hold the same amount exactly when `t = 8`. -/
theorem tanks_meet (t : Rat) : 500 - 20 * t = 100 + 30 * t ↔ t = 8 := by
  constructor
  · intro h
    grind
  · intro h
    rw [h]
    grind
-- @endregion

/-! ### Inequalities -/

-- @region linear_equations.ineq_add_both_sides
-- @provenance library
/-- Adding the same number to both sides of an inequality keeps it true, and in the same
direction: `p < q ↔ p + c < q + c`. This applies core Lean's `Rat.add_lt_add_right`. -/
theorem ineq_add_both_sides (p q c : Rat) : p < q ↔ p + c < q + c :=
  Rat.add_lt_add_right.symm
-- @endregion

-- @region linear_equations.ineq_mul_pos
-- @provenance library
/-- Multiplying both sides of an inequality by a **positive** number keeps its direction:
for `c > 0`, `p < q ↔ c·p < c·q`. This applies core Lean's `Rat.mul_lt_mul_left`. -/
theorem ineq_mul_pos (p q c : Rat) (hc : 0 < c) : p < q ↔ c * p < c * q :=
  (Rat.mul_lt_mul_left hc).symm
-- @endregion

-- @region linear_equations.ineq_mul_neg
-- @provenance independent
/-- Multiplying both sides of an inequality by a **negative** number reverses it:
if `c < 0` and `p < q` then `c·q < c·p`. The human proof: `q − p` is positive and `−c` is
positive, so their product `(−c)(q − p) = c·p − c·q` is positive, which says `c·q < c·p`. -/
theorem ineq_mul_neg (p q c : Rat) (hc : c < 0) (h : p < q) : c * q < c * p := by
  have h1 : 0 < q - p := (Rat.lt_iff_sub_pos p q).mp h
  have h2 : 0 < -c := by grind
  have h3 : 0 < -c * (q - p) := Rat.mul_pos h2 h1
  have h4 : -c * (q - p) = c * p - c * q := by grind
  rw [h4] at h3
  exact (Rat.lt_iff_sub_pos (c * q) (c * p)).mpr h3
-- @endregion

-- @region linear_equations.ineq_mul_neg_iff
-- @provenance independent
/-- The reversal is an equivalence: for `c < 0`, `p < q ↔ c·q < c·p`. Backwards: if `p < q`
failed, then `q = p` (so `c·q = c·p`) or `q < p` (so `c·p < c·q` by `ineq_mul_neg`); either
way `c·q < c·p` would be impossible. -/
theorem ineq_mul_neg_iff (p q c : Rat) (hc : c < 0) : p < q ↔ c * q < c * p := by
  constructor
  · exact ineq_mul_neg p q c hc
  · intro h
    by_cases hpq : p < q
    · exact hpq
    · exfalso
      rcases Rat.le_iff_lt_or_eq.mp (Rat.not_lt.mp hpq) with hlt | heq
      · -- `q < p`, so `c·p < c·q`, contradicting `c·q < c·p`.
        have h' : c * p < c * q := ineq_mul_neg q p c hc hlt
        grind
      · -- `q = p`, so `c·q < c·p` would say `c·p < c·p`.
        rw [heq] at h
        exact Rat.lt_irrefl h
-- @endregion

-- @region linear_equations.ineq_example
-- @provenance independent
/-- The worked example `7 − 3x ≤ 19`: subtracting `7` gives `−3x ≤ 12`, and dividing by `−3`
**reverses** the inequality, giving `x ≥ −4`. Here `grind` checks the linear arithmetic of both
directions. -/
theorem ineq_example (x : Rat) : 7 - 3 * x ≤ 19 ↔ -4 ≤ x := by
  constructor <;> intro h <;> grind
-- @endregion

-- @region linear_equations.notebooks
-- @provenance independent
/-- Whole-number solutions: with `200` dirhams, a `45`-dirham book and `n` notebooks at `12`
dirhams each are affordable exactly when `n ≤ 12`, since `45 + 12n ≤ 200 ↔ 12n ≤ 155` and
`155 / 12 ≈ 12.9`. (`omega` decides such statements about whole numbers.) -/
theorem notebooks (n : Nat) : 45 + 12 * n ≤ 200 ↔ n ≤ 12 := by
  omega
-- @endregion

end Lumenary.LinearEquations
