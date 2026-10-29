/-
The Lumenary — formal mathematics
Statistics: the mean as a balance point, how the mean and the median react to an outlier,
shifting and scaling data, and why the mean is the best centre for squared distances.

A data set is a list of rational numbers (`List Rat`), so every calculation is exact. The mean
is the sum divided by the number of values. The median is defined for a list that is already
sorted, by position: the middle value, or the average of the two middle values. Everything is
proved here from the field laws of `Rat` by induction on lists (`@provenance independent`);
routine algebra is closed by `grind`, core Lean's automatic prover. The worked examples are
computed by Lean and checked with `decide +kernel`.
Mathlib analogue: `Finset.sum`, `Finset.sum_sub_distrib`, and for variance
`ProbabilityTheory.variance`; Mathlib has no school-style median.
-/

namespace Lumenary.StatisticsIntro

/-! ### The mean -/

-- @region statistics_intro.mean
-- @provenance definition
/-- The **mean** of a list of numbers: their sum divided by how many there are.
(For the empty list Lean's convention `0 / 0 = 0` gives `0`.) -/
def mean (xs : List Rat) : Rat := xs.sum / xs.length
-- @endregion

-- @region statistics_intro.mean_mul_length
-- @provenance independent
/-- Mean times number of values equals the total: share the total out fairly, and each of the
`n` values gets the mean. -/
theorem mean_mul_length (xs : List Rat) (h : xs ≠ []) : mean xs * xs.length = xs.sum := by
  have hn : (xs.length : Rat) ≠ 0 := by
    have : xs.length ≠ 0 := fun h0 => h (List.eq_nil_of_length_eq_zero h0)
    simpa using this
  unfold mean
  rw [Rat.div_mul_cancel hn]
-- @endregion

-- @region statistics_intro.sum_map_sub
-- @provenance independent
/-- Subtracting `c` from every value lowers the total by `n · c`:
`Σ (xᵢ - c) = Σ xᵢ - n · c`. Proof by induction on the list. -/
theorem sum_map_sub (xs : List Rat) (c : Rat) :
    (xs.map (fun x => x - c)).sum = xs.sum - xs.length * c := by
  induction xs with
  | nil => simp [Rat.sub_self]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    grind
-- @endregion

-- @region statistics_intro.sum_deviations_zero
-- @provenance independent
/-- **The mean is the balance point.** The deviations from the mean add up to zero:
`Σ (xᵢ - x̄) = Σ xᵢ - n · x̄ = 0`. Values above the mean exactly balance values below it. -/
theorem sum_deviations_zero (xs : List Rat) : (xs.map (fun x => x - mean xs)).sum = 0 := by
  rw [sum_map_sub]
  cases xs with
  | nil => simp [Rat.sub_self]
  | cons y ys =>
    rw [Rat.mul_comm, mean_mul_length (y :: ys) (List.cons_ne_nil y ys), Rat.sub_self]
-- @endregion

-- @region statistics_intro.mean_add_const
-- @provenance independent
/-- **Shifting the data shifts the mean.** Adding `c` to every value adds `c` to the mean. -/
theorem mean_add_const (xs : List Rat) (h : xs ≠ []) (c : Rat) :
    mean (xs.map (fun x => x + c)) = mean xs + c := by
  have hn : (xs.length : Rat) ≠ 0 := by
    have : xs.length ≠ 0 := fun h0 => h (List.eq_nil_of_length_eq_zero h0)
    simpa using this
  have hsum : (xs.map (fun x => x + c)).sum = xs.sum + xs.length * c := by
    have := sum_map_sub xs (-c)
    simp only [Rat.sub_eq_add_neg, Rat.neg_neg] at this
    grind
  unfold mean
  rw [hsum, List.length_map]
  grind
-- @endregion

-- @region statistics_intro.mean_scale
-- @provenance independent
/-- **Scaling the data scales the mean.** Multiplying every value by `a` (for instance,
converting hours to minutes with `a = 60`) multiplies the mean by `a`. -/
theorem mean_scale (xs : List Rat) (a : Rat) : mean (xs.map (fun x => a * x)) = a * mean xs := by
  have hsum : (xs.map (fun x => a * x)).sum = a * xs.sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [Rat.mul_add]
  unfold mean
  rw [hsum, List.length_map, Rat.div_def, Rat.div_def, Rat.mul_assoc]
-- @endregion

-- @region statistics_intro.mean_change_last
-- @provenance independent
/-- **The mean is sensitive to every value.** Increasing one value by `d` (here, the last one)
increases the mean by `d / n`, where `n` is the number of values. An outlier `d` units away
drags the mean `d / n` units with it. -/
theorem mean_change_last (xs : List Rat) (y d : Rat) :
    mean (xs ++ [y + d]) = mean (xs ++ [y]) + d / (xs.length + 1) := by
  unfold mean
  simp only [List.sum_append, List.sum_cons, List.sum_nil, List.length_append,
    List.length_cons, List.length_nil]
  push_cast
  have hpos : (0 : Rat) < (xs.length : Rat) + 1 := by
    have := (Rat.natCast_nonneg (a := xs.length))
    grind
  have hne : (xs.length : Rat) + 1 ≠ 0 := Rat.ne_of_gt hpos
  grind
-- @endregion

/-! ### The median -/

-- @region statistics_intro.median_sorted
-- @provenance definition
/-- The **median** of a list that is already sorted from smallest to largest: the middle value
if there is an odd number of values, otherwise the mean of the two middle values.
(`l.getD i 0` is the value in position `i`, counting from `0`.) -/
def medianSorted (l : List Rat) : Rat :=
  if l.length % 2 = 1 then l.getD (l.length / 2) 0
  else (l.getD (l.length / 2 - 1) 0 + l.getD (l.length / 2) 0) / 2
-- @endregion

-- @region statistics_intro.median_resistant
-- @provenance independent
/-- **The median resists outliers.** In a sorted list of at least three values, replacing the
largest value (position `n - 1`) by any value `v` does not change the median. The median
only looks at the middle position(s), `n/2` and possibly `n/2 - 1`, and both are before
`n - 1` once `n ≥ 3`. If `v` is at least the old largest value, the list stays sorted, so this
says: making the largest value as extreme as you like leaves the median alone. -/
theorem median_resistant (l : List Rat) (hl : 3 ≤ l.length) (v : Rat) :
    medianSorted (l.set (l.length - 1) v) = medianSorted l := by
  have h1 : l.length / 2 ≠ l.length - 1 := by omega
  have h2 : l.length / 2 - 1 ≠ l.length - 1 := by omega
  unfold medianSorted
  simp only [List.length_set, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h2)]
-- @endregion

-- @region statistics_intro.outlier_example
-- @provenance independent
/-- A worked example, computed by Lean. Minutes to walk to school for seven students: the
median is `5` and the mean is `38/7 ≈ 5.4`. Replace the largest value `8` by an outlier `80`:
the median is still `5`, but the mean jumps to `110/7 ≈ 15.7`. -/
theorem outlier_example :
    medianSorted [3, 4, 5, 5, 6, 7, 8] = 5 ∧ mean [3, 4, 5, 5, 6, 7, 8] = 38 / 7 ∧
    medianSorted [3, 4, 5, 5, 6, 7, 80] = 5 ∧ mean [3, 4, 5, 5, 6, 7, 80] = 110 / 7 := by
  decide +kernel
-- @endregion

/-! ### Quartiles and the interquartile range -/

-- @region statistics_intro.lower_half
-- @provenance definition
/-- The lower half of a sorted list: the values before the median position. For an odd number
of values the median itself is left out (the convention used in this lesson). -/
def lowerHalf (l : List Rat) : List Rat := l.take (l.length / 2)
-- @endregion

-- @region statistics_intro.upper_half
-- @provenance definition
/-- The upper half of a sorted list: the values after the median position. -/
def upperHalf (l : List Rat) : List Rat := l.drop ((l.length + 1) / 2)
-- @endregion

-- @region statistics_intro.iqr
-- @provenance definition
/-- The **interquartile range** `Q₃ - Q₁` of a sorted list, where the quartiles `Q₁` and `Q₃` are
the medians of the lower and upper halves. -/
def iqr (l : List Rat) : Rat := medianSorted (upperHalf l) - medianSorted (lowerHalf l)
-- @endregion

-- @region statistics_intro.class_a
-- @provenance definition
/-- The lesson's data: minutes taken to get to school by 15 students, sorted. -/
def classA : List Rat := [5, 8, 10, 10, 12, 12, 12, 15, 15, 18, 20, 20, 25, 30, 45]
-- @endregion

-- @region statistics_intro.class_a_summary
-- @provenance independent
/-- The summary of `classA`, computed by Lean: mean `257/15 ≈ 17.1`, median `15`, quartiles
`Q₁ = 10` and `Q₃ = 20`, so the interquartile range is `10`. -/
theorem class_a_summary :
    mean classA = 257 / 15 ∧ medianSorted classA = 15 ∧
    medianSorted (lowerHalf classA) = 10 ∧ medianSorted (upperHalf classA) = 20 ∧
    iqr classA = 10 := by
  decide +kernel
-- @endregion

/-! ### Why the mean? The best centre for squared distances -/

-- @region statistics_intro.sum_sq_expand
-- @provenance independent
/-- Expanding squares: `Σ (xᵢ - c)² = Σ xᵢ² - 2c · Σ xᵢ + n · c²`. Proof by induction, expanding
`(x - c)² = x² - 2cx + c²` for one value at a time. -/
theorem sum_sq_expand (xs : List Rat) (c : Rat) :
    (xs.map (fun x => (x - c) * (x - c))).sum
      = (xs.map (fun x => x * x)).sum - 2 * c * xs.sum + xs.length * (c * c) := by
  induction xs with
  | nil => simp [Rat.sub_self, Rat.add_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    grind
-- @endregion

-- @region statistics_intro.sum_sq_dev
-- @provenance independent
/-- The total squared distance from any number `c` is the total squared distance from the mean
`m`, plus `n · (m - c)²`:
`Σ (xᵢ - c)² = Σ (xᵢ - m)² + n · (m - c)²`. Expand both sides with `sum_sq_expand` and use
`Σ xᵢ = n · m`. -/
theorem sum_sq_dev (xs : List Rat) (h : xs ≠ []) (c : Rat) :
    (xs.map (fun x => (x - c) * (x - c))).sum
      = (xs.map (fun x => (x - mean xs) * (x - mean xs))).sum
        + xs.length * ((mean xs - c) * (mean xs - c)) := by
  have hm : mean xs * xs.length = xs.sum := mean_mul_length xs h
  rw [sum_sq_expand xs c, sum_sq_expand xs (mean xs)]
  grind
-- @endregion

-- @region statistics_intro.mul_self_nonneg
-- @provenance independent
/-- A square is never negative: `0 ≤ r · r` (positive times positive, or negative times
negative, or zero). -/
theorem mul_self_nonneg (r : Rat) : 0 ≤ r * r := by
  rcases Rat.le_total (a := 0) (b := r) with h | h
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -r := by
      have := Rat.neg_le_neg h
      simpa using this
    have := Rat.mul_nonneg h' h'
    grind
-- @endregion

-- @region statistics_intro.mean_minimises_sq
-- @provenance independent
/-- **The mean is the best centre for squared distances.** For every number `c`, the total
squared distance of the data from `c` is at least the total squared distance from the mean.
This follows from `sum_sq_dev`, because `n · (m - c)² ≥ 0`. -/
theorem mean_minimises_sq (xs : List Rat) (h : xs ≠ []) (c : Rat) :
    (xs.map (fun x => (x - mean xs) * (x - mean xs))).sum
      ≤ (xs.map (fun x => (x - c) * (x - c))).sum := by
  rw [sum_sq_dev xs h c]
  have hnn : 0 ≤ (xs.length : Rat) * ((mean xs - c) * (mean xs - c)) :=
    Rat.mul_nonneg Rat.natCast_nonneg (mul_self_nonneg _)
  grind
-- @endregion

end Lumenary.StatisticsIntro
