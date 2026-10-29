/-
The Lumenary — formal mathematics
Ratios, rates and proportional reasoning: equivalent ratios, proportional relationships
`y = k·x`, ratio tables, and percentage change.

We work with core Lean's rational numbers `Rat`, so every quantity is an exact fraction.
Proportional relationships are modelled as functions `f : Rat → Rat` with `f x = k * x` for a
fixed constant `k`. Everything here is proved from the field laws of `Rat`
(`@provenance independent`); routine algebra steps are closed by `grind`, core Lean's automatic
prover, which knows those laws. No Mathlib is used. Mathlib analogue: a proportional
relationship is a linear map `ℚ →ₗ[ℚ] ℚ` (`LinearMap`), and every such map is multiplication by
a constant (`LinearMap.toSpanSingleton`, `Module.End`).
-/

namespace Lumenary.RatiosProportions

/-! ### Equivalent ratios -/

-- @region ratios_proportions.equivalent
-- @provenance definition
/-- The ratio `a : b` is *equivalent* to `c : d` if `c : d` is a scaled copy of it:
`c = k · a` and `d = k · b` for one scale factor `k > 0`. -/
def Equivalent (a b c d : Rat) : Prop := ∃ k : Rat, 0 < k ∧ c = k * a ∧ d = k * b
-- @endregion

-- @region ratios_proportions.equivalent_iff_cross_mul
-- @provenance independent
/-- **Cross-multiplication.** For positive quantities, `a : b` is equivalent to `c : d` exactly
when `a · d = b · c`. One way: `a·(k·b) = b·(k·a)`. The other way: the scale factor is
`k = c / a`, and `a·d = b·c` gives `d = k·b`. (Only `a > 0` and `c > 0` are needed.) -/
theorem equivalent_iff_cross_mul {a b c d : Rat} (ha : 0 < a) (hc : 0 < c) :
    Equivalent a b c d ↔ a * d = b * c := by
  constructor
  · intro ⟨k, _, hck, hdk⟩
    rw [hck, hdk]
    grind
  · intro h
    have ha0 : a ≠ 0 := Rat.ne_of_gt ha
    refine ⟨c / a, ?_, ?_, ?_⟩
    · rw [Rat.lt_div_iff ha]
      simpa using hc
    · grind
    · -- From `a · d = b · c`: `d = (b · c) / a = (c / a) · b`.
      grind
-- @endregion

-- @region ratios_proportions.lemonade
-- @provenance independent
/-- The lemonade puzzle: `2 : 3` (concentrate to water) and `3 : 5` are **not** equivalent,
because `2 · 5 = 10` but `3 · 3 = 9`. Adding one cup of each is not scaling. -/
theorem lemonade : ¬ Equivalent 2 3 3 5 := by
  rw [equivalent_iff_cross_mul (by decide) (by decide)]
  decide +kernel
-- @endregion

/-! ### Proportional relationships -/

-- @region ratios_proportions.is_proportional
-- @provenance definition
/-- A relationship `y = f x` is *proportional* if there is one constant `k` (the constant of
proportionality) with `f x = k · x` for every `x`. -/
def IsProportional (f : Rat → Rat) : Prop := ∃ k : Rat, ∀ x, f x = k * x
-- @endregion

-- @region ratios_proportions.proportional_zero
-- @provenance independent
/-- A proportional relationship sends `0` to `0`: `f 0 = k · 0 = 0`. Its graph passes through
the origin. -/
theorem proportional_zero {f : Rat → Rat} (hf : IsProportional f) : f 0 = 0 := by
  obtain ⟨k, hk⟩ := hf
  rw [hk, Rat.mul_zero]
-- @endregion

-- @region ratios_proportions.affine_not_proportional
-- @provenance independent
/-- `y = 2x + 1` is a straight line but **not** proportional: it gives `1`, not `0`, at `x = 0`. -/
theorem affine_not_proportional : ¬ IsProportional (fun x => 2 * x + 1) := by
  intro hf
  have h0 := proportional_zero hf
  grind
-- @endregion

-- @region ratios_proportions.proportional_iff_ratio_const
-- @provenance independent
/-- **Spotting proportionality in a table.** `f` is proportional exactly when `f 0 = 0` and the
ratio `f x / x` is the same for every `x ≠ 0`. Then `k = f 1`, and `f x / x = f 1` gives
`f x = f 1 · x`. -/
theorem proportional_iff_ratio_const (f : Rat → Rat) :
    IsProportional f ↔ f 0 = 0 ∧ ∀ x, x ≠ 0 → f x / x = f 1 := by
  constructor
  · intro hf
    refine ⟨proportional_zero hf, ?_⟩
    obtain ⟨k, hk⟩ := hf
    intro x hx
    rw [hk x, hk 1]
    grind
  · intro ⟨h0, hratio⟩
    refine ⟨f 1, ?_⟩
    intro x
    by_cases hx : x = 0
    · rw [hx, h0, Rat.mul_zero]
    · have h := hratio x hx
      grind
-- @endregion

-- @region ratios_proportions.slope_const
-- @provenance independent
/-- **The graph is a straight line through the origin.** Between any two different points of
the graph of `y = k · x`, the slope `(y₂ - y₁)/(x₂ - x₁)` is the same number `k`. -/
theorem slope_const (k x₁ x₂ : Rat) (h : x₁ ≠ x₂) :
    (k * x₂ - k * x₁) / (x₂ - x₁) = k := by
  have hne : x₂ - x₁ ≠ 0 := by
    intro h0
    apply h
    grind
  grind
-- @endregion

-- @region ratios_proportions.proportional_add
-- @provenance independent
/-- **Adding rows of a ratio table.** If `f` is proportional, then
`f (x + y) = k·(x + y) = k·x + k·y = f x + f y`. -/
theorem proportional_add {f : Rat → Rat} (hf : IsProportional f) (x y : Rat) :
    f (x + y) = f x + f y := by
  obtain ⟨k, hk⟩ := hf
  rw [hk, hk x, hk y, Rat.mul_add]
-- @endregion

-- @region ratios_proportions.proportional_scale
-- @provenance independent
/-- **Scaling a row of a ratio table.** If `f` is proportional, then `f (c · x) = c · f x`. -/
theorem proportional_scale {f : Rat → Rat} (hf : IsProportional f) (c x : Rat) :
    f (c * x) = c * f x := by
  obtain ⟨k, hk⟩ := hf
  rw [hk, hk x]
  grind
-- @endregion

-- @region ratios_proportions.additive_nat
-- @provenance independent
/-- **Additive implies proportional (for whole numbers).** If the price of `m + n` items is
always the price of `m` items plus the price of `n` items, then the price of `n` items is
`n` times the price of one: `f n = n · f 1`. Proof by induction on `n`. -/
theorem additive_nat (f : Nat → Rat) (hadd : ∀ m n, f (m + n) = f m + f n) :
    ∀ n : Nat, f n = n * f 1 := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0
    simp at h
    grind
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [hadd n 1, ih]
    push_cast
    grind
-- @endregion

/-! ### Percentages -/

-- @region ratios_proportions.percent_of
-- @provenance definition
/-- `p` percent of `x` is `p/100` of `x`. -/
def percentOf (p x : Rat) : Rat := p / 100 * x
-- @endregion

-- @region ratios_proportions.increase_by_percent
-- @provenance independent
/-- Increasing `x` by `p` percent multiplies it by `1 + p/100`:
`x + (p/100)·x = (1 + p/100)·x`. -/
theorem increase_by_percent (p x : Rat) : x + percentOf p x = (1 + p / 100) * x := by
  unfold percentOf
  grind
-- @endregion

-- @region ratios_proportions.successive_changes_commute
-- @provenance independent
/-- Successive percentage changes **multiply**, so their order does not matter: a rise of `p`%
then a rise of `q`% gives the same result as `q`% then `p`%. -/
theorem successive_changes_commute (x p q : Rat) :
    x * (1 + p / 100) * (1 + q / 100) = x * (1 + q / 100) * (1 + p / 100) := by
  grind
-- @endregion

-- @region ratios_proportions.ten_up_ten_down
-- @provenance independent
/-- A 10% rise followed by a 10% fall multiplies by `1.1 × 0.9 = 0.99`: you end 1% lower. -/
theorem ten_up_ten_down (x : Rat) : x * (110 / 100) * (90 / 100) = 99 / 100 * x := by
  grind
-- @endregion

-- @region ratios_proportions.up_down_factor
-- @provenance independent
/-- Up by a fraction `r`, then down by the same fraction `r`: the overall factor is
`(1 + r)(1 - r) = 1 - r²`. -/
theorem up_down_factor (x r : Rat) : x * (1 + r) * (1 - r) = x * (1 - r * r) := by
  grind
-- @endregion

-- @region ratios_proportions.sq_pos
-- @provenance independent
/-- The square of a non-zero rational number is positive (a positive times a positive, or a
negative times a negative). -/
theorem sq_pos {r : Rat} (hr : r ≠ 0) : 0 < r * r := by
  rcases Rat.le_total (a := r) (b := 0) with hle | hge
  · -- `r < 0`, so `-r > 0` and `r · r = (-r) · (-r) > 0`.
    have hneg : r < 0 := Rat.lt_of_le_of_ne hle hr
    have h : 0 < -r := by
      have := Rat.neg_lt_neg hneg
      simpa using this
    have := Rat.mul_pos h h
    grind
  · -- `r > 0`, so `r · r > 0`.
    exact Rat.mul_pos (Rat.lt_of_le_of_ne hge (Ne.symm hr)) (Rat.lt_of_le_of_ne hge (Ne.symm hr))
-- @endregion

-- @region ratios_proportions.up_down_lt
-- @provenance independent
/-- **Up and down by the same percentage never gets you back.** For a positive amount `x` and
any non-zero change `r`, rising by `r` and then falling by `r` leaves less than `x`:
`x · (1 - r²) = x - x·r² < x`. -/
theorem up_down_lt {x r : Rat} (hx : 0 < x) (hr : r ≠ 0) : x * (1 + r) * (1 - r) < x := by
  rw [up_down_factor]
  have hxr : 0 < x * (r * r) := Rat.mul_pos hx (sq_pos hr)
  grind
-- @endregion

-- @region ratios_proportions.undo_increase
-- @provenance independent
/-- **Undoing a percentage rise.** A rise of `p`% is undone by a fall of `100p/(100 + p)`%, not
of `p`%: `(1 + p/100) · (1 - p/(100 + p)) = 1`. For `p = 25` the fall is `20`%. -/
theorem undo_increase (p : Rat) (hp : 0 ≤ p) : (1 + p / 100) * (1 - p / (100 + p)) = 1 := by
  have hpos : (0 : Rat) < 100 + p := by
    have : (0 : Rat) < 100 := by decide
    grind
  have hne : (100 : Rat) + p ≠ 0 := Rat.ne_of_gt hpos
  grind
-- @endregion

end Lumenary.RatiosProportions
