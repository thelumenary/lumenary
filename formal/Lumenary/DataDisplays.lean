/-
The Lumenary — formal mathematics
Data displays and the mean as a fair share ("for grown-ups" companion to the Grades 3–5 lesson).

A data set is a list of whole numbers — for example the number of cubes in each child's tower.
Sharing fairly means moving cubes from tower to tower until all towers are level. We prove:

* moving cubes never changes the total or the number of towers;
* so if the towers end up level at height `m`, then `m × (number of towers) = total`: the fair
  share is the total divided by the number of towers, whatever moves were made;
* the fair share is never more than the tallest tower;
* a bar chart whose axis starts above zero makes the ratio of two bars look bigger than it is.

Core Lean 4 only (whole numbers, no fractions). Mathlib analogue: `Finset.sum_const`,
`Finset.sum_le_card_nsmul`, and the mean as `(∑ i, x i) / n` over a field.
-/

namespace Lumenary.DataDisplays

/-! ### Fair shares by levelling towers -/

-- @region data_displays.data
-- @provenance definition
/-- A data set: a list of whole-number amounts, such as the cubes in each child's tower. -/
abbrev Data := List Nat
-- @endregion

-- @region data_displays.move
-- @provenance definition
/-- One **move**: take one cube off a tower and put it on another tower. The towers are listed
in order; `xs`, `ys` and `zs` are the towers we do not touch. The cube can move to a tower
further right, or to a tower further left. -/
inductive Move : Data → Data → Prop
  | right (xs ys zs : Data) (a b : Nat) :
      Move (xs ++ (a + 1) :: ys ++ b :: zs) (xs ++ a :: ys ++ (b + 1) :: zs)
  | left (xs ys zs : Data) (a b : Nat) :
      Move (xs ++ a :: ys ++ (b + 1) :: zs) (xs ++ (a + 1) :: ys ++ b :: zs)
-- @endregion

-- @region data_displays.reach
-- @provenance definition
/-- `Reach d e`: the towers `d` can be turned into the towers `e` by some moves, one after
another (perhaps none). -/
inductive Reach : Data → Data → Prop
  | refl (d : Data) : Reach d d
  | step {d e f : Data} : Move d e → Reach e f → Reach d f
-- @endregion

-- @region data_displays.move_total
-- @provenance independent
/-- A move keeps the total: one tower loses a cube and another gains it. -/
theorem move_total {d e : Data} (h : Move d e) : e.sum = d.sum := by
  cases h <;> simp [List.sum_append, List.sum_cons] <;> omega
-- @endregion

-- @region data_displays.move_length
-- @provenance independent
/-- A move keeps the number of towers. -/
theorem move_length {d e : Data} (h : Move d e) : e.length = d.length := by
  cases h <;> simp
-- @endregion

-- @region data_displays.reach_total
-- @provenance independent
/-- However many moves we make, the total and the number of towers stay the same. -/
theorem reach_total {d e : Data} (h : Reach d e) : e.sum = d.sum ∧ e.length = d.length := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step hm _ ih => exact ⟨ih.1.trans (move_total hm), ih.2.trans (move_length hm)⟩
-- @endregion

-- @region data_displays.level_total
-- @provenance independent
/-- `n` towers that are all `m` tall hold `n × m` cubes. -/
theorem level_total (n m : Nat) : (List.replicate n m).sum = n * m := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega
-- @endregion

-- @region data_displays.level_total_library
-- @provenance library
/-- The same fact, applying core Lean's `List.sum_replicate_nat`. -/
theorem level_total_library (n m : Nat) : (List.replicate n m).sum = n * m :=
  List.sum_replicate_nat
-- @endregion

-- @region data_displays.fair_share
-- @provenance independent
/-- **The mean as a fair share.** If moves turn the towers `d` into level towers of height `m`,
then `m × (number of towers) = total`. So the level is always total ÷ number of towers — it
does not depend on which moves were made. -/
theorem fair_share {d : Data} {m : Nat} (h : Reach d (List.replicate d.length m)) :
    d.length * m = d.sum := by
  rw [← level_total, (reach_total h).1]
-- @endregion

-- @region data_displays.cubes_levelled
-- @provenance independent
/-- Four towers of 4, 6, 8 and 2 cubes can be levelled at 5 in four moves:
`4 6 8 2 → 5 5 8 2 → 5 5 7 3 → 5 5 6 4 → 5 5 5 5`. -/
theorem cubes_levelled : Reach [4, 6, 8, 2] [5, 5, 5, 5] :=
  .step (.left [] [] [8, 2] 4 5) <|
  .step (.right [5, 5] [] [] 7 2) <|
  .step (.right [5, 5] [] [] 6 3) <|
  .step (.right [5, 5] [] [] 5 4) <|
  .refl _
-- @endregion

-- @region data_displays.mean_not_a_value
-- @provenance independent
/-- The fair share of 4, 6, 8 and 2 is 5 — and 5 is **not** one of the data values. -/
theorem mean_not_a_value : [4, 6, 8, 2].length * 5 = [4, 6, 8, 2].sum ∧ 5 ∉ [4, 6, 8, 2] :=
  ⟨fair_share cubes_levelled, by decide⟩
-- @endregion

-- @region data_displays.cannot_level
-- @provenance independent
/-- Towers of 3, 7, 2 and 6 cubes (18 in all) can **never** be levelled with whole cubes: four
equal towers would need `4 × m = 18`, and 18 is not a multiple of 4. The fair share is
`4½`, which needs a cube cut in half. -/
theorem cannot_level (m : Nat) : ¬ Reach [3, 7, 2, 6] (List.replicate 4 m) := by
  intro h
  have := fair_share h
  simp at this
  omega
-- @endregion

-- @region data_displays.sum_le_length_mul
-- @provenance independent
/-- If no tower is taller than `M`, the total is at most `(number of towers) × M`. -/
theorem sum_le_length_mul (d : Data) (M : Nat) (h : ∀ x ∈ d, x ≤ M) : d.sum ≤ d.length * M := by
  induction d with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega
-- @endregion

-- @region data_displays.fair_share_le_max
-- @provenance independent
/-- **The fair share is never more than the tallest tower.** If the towers `d` can be levelled
at height `m`, and no tower is taller than `M`, then `m ≤ M`. -/
theorem fair_share_le_max {d : Data} {m M : Nat} (hd : d ≠ [])
    (h : Reach d (List.replicate d.length m)) (hM : ∀ x ∈ d, x ≤ M) : m ≤ M := by
  have h1 := fair_share h
  have h2 := sum_le_length_mul d M hM
  have hpos : 0 < d.length := List.length_pos_iff.mpr hd
  exact Nat.le_of_mul_le_mul_left (h1 ▸ h2) hpos
-- @endregion

/-! ### Bar charts and scales -/

-- @region data_displays.drawn
-- @provenance definition
/-- The drawn height of a bar for the value `v` when the axis starts at `base` (instead of 0). -/
def drawn (base v : Nat) : Nat := v - base
-- @endregion

-- @region data_displays.misleading_example
-- @provenance independent
/-- Two schools collect 52 kg and 48 kg of paper. With the axis starting at 40, the bars are
drawn 12 and 8 units tall: one looks one and a half times as tall as the other
(`2 × 12 = 3 × 8`), although 52 kg is not even 1.1 times 48 kg (`10 × 52 < 11 × 48`). -/
theorem misleading_example :
    drawn 40 52 = 12 ∧ drawn 40 48 = 8 ∧ 2 * drawn 40 52 = 3 * drawn 40 48 ∧
    10 * 52 < 11 * 48 := by
  decide
-- @endregion

-- @region data_displays.baseline_exaggerates
-- @provenance independent
/-- **An axis that does not start at zero exaggerates differences.** If the axis starts at
`b > 0` and two values satisfy `b < c < a`, then the drawn bars compare as
`(a − b) : (c − b)`, which is a bigger ratio than the true one, `a : c`. Written without
fractions: `a × (c − b) < (a − b) × c`. -/
theorem baseline_exaggerates (a b c : Nat) (hb : 0 < b) (hbc : b < c) (hca : c < a) :
    a * (c - b) < (a - b) * c := by
  rw [Nat.mul_sub, Nat.sub_mul]
  have h1 : b * c < a * b := by
    rw [Nat.mul_comm a b]
    exact Nat.mul_lt_mul_of_pos_left hca hb
  have h2 : a * b ≤ a * c := Nat.mul_le_mul_left a (Nat.le_of_lt hbc)
  omega
-- @endregion

end Lumenary.DataDisplays
