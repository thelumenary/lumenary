/-
The Lumenary — formal mathematics
Graphs of change: the average rate of change, what its sign says about a graph, how the rates
over two intervals combine, and two classic surprises about average speed.

A quantity that changes is modelled as a function `f : Rat → Rat` (for example, distance in
kilometres after `t` hours), and its average rate of change between times `a` and `b` is
`(f b − f a) / (b − a)`: the slope of the segment joining two points of the graph. Everything is
proved here from the arithmetic and order of core Lean's rational numbers `Rat`
(`@provenance independent`); routine rearrangements are closed by `grind`. Mathlib has the
same notion as `slope f a b` (`Mathlib.LinearAlgebra.AffineSpace.Slope`) and, for functions on
the real numbers, the mean value theorem `exists_deriv_eq_slope`, which connects average
rates to instantaneous ones.
-/

namespace Lumenary.GraphsOfChange

/-! ### Average rate of change -/

-- @region graphs_of_change.avg_rate
-- @provenance definition
/-- The average rate of change of `f` between `a` and `b`: change in the quantity divided by
the change in time, `(f b − f a) / (b − a)`. It is the slope of the segment of the graph from
`(a, f a)` to `(b, f b)`. Meaningful only for `a ≠ b`; the theorems below assume that. -/
def avgRate (f : Rat → Rat) (a b : Rat) : Rat := (f b - f a) / (b - a)
-- @endregion

-- @region graphs_of_change.change_eq_rate_mul_time
-- @provenance independent
/-- Change = average rate × elapsed time. On a distance–time graph: distance covered = average
speed × time taken. (This is the definition of `avgRate`, multiplied out.) -/
theorem change_eq_rate_mul_time (f : Rat → Rat) (a b : Rat) (h : a ≠ b) :
    f b - f a = avgRate f a b * (b - a) := by
  have hrun : b - a ≠ 0 := fun h0 => h (by grind)
  unfold avgRate
  exact (Rat.div_mul_cancel hrun).symm
-- @endregion

-- @region graphs_of_change.avg_rate_linear
-- @provenance independent
/-- For a quantity changing at a constant rate, `f(t) = m·t + c`, the average rate of change
over **every** interval is `m`: the graph is a straight line of slope `m`. -/
theorem avg_rate_linear (m c a b : Rat) (h : a ≠ b) :
    avgRate (fun t => m * t + c) a b = m := by
  have hrun : b - a ≠ 0 := fun h0 => h (by grind)
  unfold avgRate
  rw [show m * b + c - (m * a + c) = m * (b - a) by grind]
  exact Rat.mul_div_cancel hrun
-- @endregion

-- @region graphs_of_change.avg_rate_const
-- @provenance independent
/-- A quantity that does not change has average rate of change `0` over every interval: a
horizontal graph. -/
theorem avg_rate_const (k a b : Rat) : avgRate (fun _ => k) a b = 0 := by
  unfold avgRate
  rw [Rat.sub_self, Rat.div_def, Rat.zero_mul]
-- @endregion

/-! ### What the sign of the rate tells us -/

-- @region graphs_of_change.increasing_iff_avg_rate_pos
-- @provenance independent
/-- A graph is increasing (`y` gets larger whenever `x` gets larger) exactly when every average
rate of change is positive. For `x < y` the run `y − x` is positive, so the quotient
`(f y − f x)/(y − x)` is positive exactly when the rise `f y − f x` is (`Rat.lt_div_iff`). -/
theorem increasing_iff_avg_rate_pos (f : Rat → Rat) :
    (∀ x y, x < y → f x < f y) ↔ (∀ x y, x < y → 0 < avgRate f x y) := by
  have key : ∀ x y, x < y → (0 < avgRate f x y ↔ f x < f y) := by
    intro x y hxy
    have hrun : 0 < y - x := (Rat.lt_iff_sub_pos x y).mp hxy
    unfold avgRate
    rw [Rat.lt_div_iff hrun, Rat.zero_mul]
    exact (Rat.lt_iff_sub_pos (f x) (f y)).symm
  constructor
  · intro hinc x y hxy
    exact (key x y hxy).mpr (hinc x y hxy)
  · intro hpos x y hxy
    exact (key x y hxy).mp (hpos x y hxy)
-- @endregion

-- @region graphs_of_change.constant_iff_avg_rate_zero
-- @provenance independent
/-- A quantity is constant exactly when its average rate of change is `0` over every interval:
"a horizontal graph means the quantity is not changing", and conversely. -/
theorem constant_iff_avg_rate_zero (f : Rat → Rat) :
    (∀ x y, f x = f y) ↔ (∀ x y, x < y → avgRate f x y = 0) := by
  constructor
  · intro hconst x y _
    unfold avgRate
    rw [hconst y x, Rat.sub_self, Rat.div_def, Rat.zero_mul]
  · intro hzero
    -- For `x < y`, change = rate × time = 0 × time = 0.
    have step : ∀ x y, x < y → f x = f y := by
      intro x y hxy
      have hch := change_eq_rate_mul_time f x y (Rat.ne_of_lt hxy)
      rw [hzero x y hxy, Rat.zero_mul] at hch
      grind
    intro x y
    rcases Rat.le_total (a := x) (b := y) with hxy | hyx
    · rcases Rat.le_iff_lt_or_eq.mp hxy with hlt | heq
      · exact step x y hlt
      · rw [heq]
    · rcases Rat.le_iff_lt_or_eq.mp hyx with hlt | heq
      · exact (step y x hlt).symm
      · rw [heq]
-- @endregion

/-! ### Combining intervals -/

-- @region graphs_of_change.avg_rate_split
-- @provenance independent
/-- The average rate over a whole interval is a **weighted average** of the rates over its two
parts, weighted by their lengths:
`(c − a)·R(a, c) = (b − a)·R(a, b) + (c − b)·R(b, c)`.
Both sides equal the total change `f c − f a` (`change_eq_rate_mul_time`). -/
theorem avg_rate_split (f : Rat → Rat) (a b c : Rat) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    (c - a) * avgRate f a c = (b - a) * avgRate f a b + (c - b) * avgRate f b c := by
  have h1 := change_eq_rate_mul_time f a c hac
  have h2 := change_eq_rate_mul_time f a b hab
  have h3 := change_eq_rate_mul_time f b c hbc
  grind
-- @endregion

-- @region graphs_of_change.avg_rate_between
-- @provenance independent
/-- The average speed over a whole journey lies between the average speeds of its two legs:
for `a < b < c`, if `R(a, b) ≤ R(b, c)` then `R(a, b) ≤ R(a, c) ≤ R(b, c)`.
Proof: in the weighted average `(c − a)·R(a, c) = (b − a)·R(a, b) + (c − b)·R(b, c)`, replace
the larger rate by the smaller one (or the smaller by the larger), then divide by `c − a > 0`. -/
theorem avg_rate_between (f : Rat → Rat) (a b c : Rat) (hab : a < b) (hbc : b < c)
    (hle : avgRate f a b ≤ avgRate f b c) :
    avgRate f a b ≤ avgRate f a c ∧ avgRate f a c ≤ avgRate f b c := by
  have hac : a < c := by grind
  have hsplit := avg_rate_split f a b c (Rat.ne_of_lt hab) (Rat.ne_of_lt hbc) (Rat.ne_of_lt hac)
  have h1 : 0 ≤ b - a := Rat.le_of_lt ((Rat.lt_iff_sub_pos a b).mp hab)
  have h2 : 0 ≤ c - b := Rat.le_of_lt ((Rat.lt_iff_sub_pos b c).mp hbc)
  have h3 : 0 < c - a := (Rat.lt_iff_sub_pos a c).mp hac
  -- Replace one rate by the other, in each term of the weighted average.
  have low : (c - b) * avgRate f a b ≤ (c - b) * avgRate f b c :=
    Rat.mul_le_mul_of_nonneg_left hle h2
  have high : (b - a) * avgRate f a b ≤ (b - a) * avgRate f b c :=
    Rat.mul_le_mul_of_nonneg_left hle h1
  constructor
  · apply Rat.le_of_mul_le_mul_left _ h3
    calc (c - a) * avgRate f a b
        = (b - a) * avgRate f a b + (c - b) * avgRate f a b := by grind
      _ ≤ (b - a) * avgRate f a b + (c - b) * avgRate f b c := by grind
      _ = (c - a) * avgRate f a c := hsplit.symm
  · apply Rat.le_of_mul_le_mul_left _ h3
    calc (c - a) * avgRate f a c
        = (b - a) * avgRate f a b + (c - b) * avgRate f b c := hsplit
      _ ≤ (b - a) * avgRate f b c + (c - b) * avgRate f b c := by grind
      _ = (c - a) * avgRate f b c := by grind
-- @endregion

/-! ### Two surprises about average speed -/

-- @region graphs_of_change.steady
-- @provenance definition
/-- A steady runner: `5` metres every second, so `5t` metres after `t` seconds. -/
def steady (t : Rat) : Rat := 5 * t
-- @endregion

-- @region graphs_of_change.sprinter
-- @provenance definition
/-- A runner who starts fast and tires: `7` m/s for the first `10` seconds, then `3` m/s. -/
def sprinter (t : Rat) : Rat := if t ≤ 10 then 7 * t else 70 + 3 * (t - 10)
-- @endregion

-- @region graphs_of_change.same_average_different_journeys
-- @provenance independent
/-- Same average rate, different behaviour: over the `20` seconds both runners average
`5` m/s (both cover `100` m), yet after `10` seconds one is at `50` m and the other at `70` m.
An average rate does not tell you what happens inside the interval. -/
theorem same_average_different_journeys :
    avgRate steady 0 20 = 5 ∧ avgRate sprinter 0 20 = 5 ∧ steady 10 ≠ sprinter 10 := by
  have h20 : ¬ ((20 : Rat) ≤ 10) := by decide
  have h0 : (0 : Rat) ≤ 10 := by decide
  have h10 : (10 : Rat) ≤ 10 := by decide
  refine ⟨?_, ?_, ?_⟩
  · unfold avgRate steady
    grind
  · unfold avgRate sprinter
    rw [ite_eq_right h20, ite_eq_left h0]
    grind
  · unfold steady sprinter
    rw [ite_eq_left h10]
    grind
-- @endregion

-- @region graphs_of_change.round_trip_average
-- @provenance independent
/-- Going a distance `d` at speed `u` and coming back at speed `v`, the average speed is total
distance ÷ total time `= 2d / (d/u + d/v) = 2uv / (u + v)` — not `(u + v)/2`. (The distance
`d` cancels.) -/
theorem round_trip_average (d u v : Rat) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) :
    (d + d) / (d / u + d / v) = 2 * u * v / (u + v) := by
  have hd' : d ≠ 0 := Rat.ne_of_gt hd
  have hu' : u ≠ 0 := Rat.ne_of_gt hu
  have hv' : v ≠ 0 := Rat.ne_of_gt hv
  have huv : u + v ≠ 0 := Rat.ne_of_gt (by grind)
  grind
-- @endregion

-- @region graphs_of_change.round_trip_example
-- @provenance independent
/-- The classic puzzle: `60` km out at `30` km/h (2 hours) and `60` km back at `60` km/h
(1 hour) is `120` km in `3` hours — an average of `40` km/h, not `45`. -/
theorem round_trip_example : (60 + 60 : Rat) / (60 / 30 + 60 / 60) = 40 := by
  grind
-- @endregion

-- @region graphs_of_change.round_trip_le_mean
-- @provenance independent
/-- The round-trip average speed is never more than the mean of the two speeds:
`2uv/(u + v) ≤ (u + v)/2`. The difference is `(u − v)² / (2(u + v))`, and a square is never
negative; equality holds only when `u = v`. -/
theorem round_trip_le_mean (u v : Rat) (hu : 0 < u) (hv : 0 < v) :
    2 * u * v / (u + v) ≤ (u + v) / 2 := by
  have hpos : 0 < u + v := by grind
  have huv : u + v ≠ 0 := Rat.ne_of_gt hpos
  -- A square is never negative.
  have hsq : 0 ≤ (u - v) * (u - v) := by
    rcases Rat.le_total (a := 0) (b := u - v) with h | h
    · exact Rat.mul_nonneg h h
    · have h' : 0 ≤ -(u - v) := by grind
      have := Rat.mul_nonneg h' h'
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this
      exact this
  have hinv : 0 ≤ (2 * (u + v))⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by grind))
  have hdiff : (u + v) / 2 - 2 * u * v / (u + v) = (u - v) * (u - v) * (2 * (u + v))⁻¹ := by
    grind
  have hnonneg : 0 ≤ (u + v) / 2 - 2 * u * v / (u + v) := by
    rw [hdiff]
    exact Rat.mul_nonneg hsq hinv
  exact (Rat.le_iff_sub_nonneg _ _).mpr hnonneg
-- @endregion

end Lumenary.GraphsOfChange
