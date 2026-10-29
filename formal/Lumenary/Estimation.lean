/-
The Lumenary — formal mathematics
Estimation and rounding: rounding to the nearest ten or hundred, how far rounding can move a
number, upper and lower bounds, and how rounding errors add up.

Core Lean 4 only (no Mathlib). We define rounding to the nearest ten with halves rounded up,
`roundTen n = (n + 5) / 10 × 10` (Lean's `/` on whole numbers throws away the remainder), and
prove that it gives a multiple of ten, that it moves `n` by at most `5`, that no other
multiple of ten is closer, and that rounding `k` numbers before adding can move the total by
up to `5 × k`. Decimals are modelled as whole numbers of hundredths (`3.46` is `346`
hundredths). Many proofs end with `omega`, Lean's decision procedure for whole-number
arithmetic with `+`, `−`, `≤` and division by fixed numbers. Mathlib analogue: `round`,
`Int.floor` and `Nat.add_le_add`; Mathlib's `round` also rounds halves up.
-/

namespace Lumenary.Estimation

/-! ### Rounding -/

-- @region estimation.round_ten
-- @provenance definition
/-- Round to the nearest ten, with halves rounded **up**: add `5`, then knock off the ones
digit. (`(n + 5) / 10` counts the whole tens in `n + 5`.) -/
def roundTen (n : Nat) : Nat := (n + 5) / 10 * 10
-- @endregion

-- @region estimation.round_hundred
-- @provenance definition
/-- Round to the nearest hundred, with halves rounded up. -/
def roundHundred (n : Nat) : Nat := (n + 50) / 100 * 100
-- @endregion

-- @region estimation.round_examples
-- @provenance independent
/-- The lesson's examples: `37 → 40`, `34 → 30`, the halfway case `35 → 40`, `999 → 1000`,
and `4372` rounds to `4370` (nearest ten) and `4400` (nearest hundred); `2950 → 3000`. -/
theorem round_examples :
    roundTen 37 = 40 ∧ roundTen 34 = 30 ∧ roundTen 35 = 40 ∧ roundTen 999 = 1000 ∧
      roundTen 4372 = 4370 ∧ roundHundred 4372 = 4400 ∧ roundHundred 2950 = 3000 := by
  decide
-- @endregion

-- @region estimation.round_ten_multiple
-- @provenance library
/-- Rounding to the nearest ten always gives a multiple of ten. This applies core Lean's
`Nat.mul_mod_left`: `(m × 10) % 10 = 0`. -/
theorem roundTen_multiple (n : Nat) : roundTen n % 10 = 0 := Nat.mul_mod_left _ _
-- @endregion

-- @region estimation.round_ten_error
-- @provenance independent
/-- Rounding to the nearest ten moves a whole number **up by at most 5** or **down by at most
4**. So the rounding error is never more than `5`. -/
theorem roundTen_error (n : Nat) : roundTen n ≤ n + 5 ∧ n ≤ roundTen n + 4 := by
  unfold roundTen
  omega
-- @endregion

-- @region estimation.gap
-- @provenance definition
/-- The gap (distance) between two whole numbers: the bigger minus the smaller. -/
def gap (a b : Nat) : Nat := if a ≤ b then b - a else a - b
-- @endregion

-- @region estimation.round_ten_nearest
-- @provenance independent
/-- `roundTen n` really is a **nearest** multiple of ten: no multiple of ten `m` is closer to
`n`. (At a halfway point such as `35`, both `30` and `40` are equally close; we chose `40`.) -/
theorem roundTen_nearest (n m : Nat) (hm : m % 10 = 0) : gap n (roundTen n) ≤ gap n m := by
  unfold gap roundTen
  split <;> split <;> omega
-- @endregion

-- @region estimation.round_hundred_error
-- @provenance independent
/-- Rounding to the nearest hundred moves a whole number by at most `50`. -/
theorem roundHundred_error (n : Nat) : roundHundred n ≤ n + 50 ∧ n ≤ roundHundred n + 49 := by
  unfold roundHundred
  omega
-- @endregion

/-! ### Upper and lower bounds -/

-- @region estimation.add_bounds
-- @provenance library
/-- If `a` is between `la` and `ua`, and `b` is between `lb` and `ub`, then `a + b` is between
`la + lb` and `ua + ub`. This applies core Lean's `Nat.add_le_add` twice. -/
theorem add_bounds {a b la ua lb ub : Nat} (ha₁ : la ≤ a) (ha₂ : a ≤ ua)
    (hb₁ : lb ≤ b) (hb₂ : b ≤ ub) : la + lb ≤ a + b ∧ a + b ≤ ua + ub :=
  ⟨Nat.add_le_add ha₁ hb₁, Nat.add_le_add ha₂ hb₂⟩
-- @endregion

-- @region estimation.bounds_example
-- @provenance independent
/-- The example from the lesson: if `30 ≤ a ≤ 40` and `20 ≤ b ≤ 30`, then `50 ≤ a + b ≤ 70`.
It is `add_bounds` with the numbers filled in. -/
theorem bounds_example (a b : Nat) (ha₁ : 30 ≤ a) (ha₂ : a ≤ 40) (hb₁ : 20 ≤ b) (hb₂ : b ≤ 30) :
    50 ≤ a + b ∧ a + b ≤ 70 :=
  add_bounds ha₁ ha₂ hb₁ hb₂
-- @endregion

-- @region estimation.sub_bounds
-- @provenance independent
/-- Bounds for a difference work **crosswise**: the largest `a − b` uses the largest `a` and the
smallest `b`. If `la ≤ a ≤ ua`, `lb ≤ b ≤ ub` and `ub ≤ la` (so no subtraction goes below
zero), then `la − ub ≤ a − b ≤ ua − lb`. -/
theorem sub_bounds {a b la ua lb ub : Nat} (ha₁ : la ≤ a) (ha₂ : a ≤ ua)
    (hb₁ : lb ≤ b) (hb₂ : b ≤ ub) (h : ub ≤ la) : la - ub ≤ a - b ∧ a - b ≤ ua - lb := by
  omega
-- @endregion

-- @region estimation.mul_bounds
-- @provenance library
/-- Bounds for a product: if `la ≤ a ≤ ua` and `lb ≤ b ≤ ub` (whole numbers, so nothing is
negative), then `la × lb ≤ a × b ≤ ua × ub`. This applies core Lean's `Nat.mul_le_mul`. -/
theorem mul_bounds {a b la ua lb ub : Nat} (ha₁ : la ≤ a) (ha₂ : a ≤ ua)
    (hb₁ : lb ≤ b) (hb₂ : b ≤ ub) : la * lb ≤ a * b ∧ a * b ≤ ua * ub :=
  ⟨Nat.mul_le_mul ha₁ hb₁, Nat.mul_le_mul ha₂ hb₂⟩
-- @endregion

-- @region estimation.shopping
-- @provenance independent
/-- Wanjiru's shopping: prices between `200` and `300`, `400` and `500`, and `100` and `200`
shillings always total between `700` and `1000`. So `1000` shillings is certainly enough.
The actual prices `289 + 412 + 198 = 899` fit. -/
theorem shopping (a b c : Nat) (ha₁ : 200 ≤ a) (ha₂ : a ≤ 300) (hb₁ : 400 ≤ b) (hb₂ : b ≤ 500)
    (hc₁ : 100 ≤ c) (hc₂ : c ≤ 200) : 700 ≤ a + b + c ∧ a + b + c ≤ 1000 := by
  omega
-- @endregion

-- @region estimation.product_estimate
-- @provenance independent
/-- Checking a calculator: `39 × 61` is near `40 × 60 = 2400`, so `1379` must be wrong. The
area model gives the exact gap: `(40 − 1) × (60 + 1) = 2400 + 40 − 60 − 1 = 2379`. -/
theorem product_estimate : 39 * 61 = 2379 ∧ 40 * 60 = 2400 ∧ 39 * 61 ≠ 1379 := by decide
-- @endregion

/-! ### Rounding errors add up -/

-- @region estimation.round_each_step_differs
-- @provenance independent
/-- Rounding at every step can change the answer: rounding each `14` first gives
`10 + 10 + 10 = 30`, but the total `42` rounds to `40`. -/
theorem round_each_step_differs :
    roundTen 14 + roundTen 14 + roundTen 14 = 30 ∧ roundTen (14 + 14 + 14) = 40 := by decide
-- @endregion

-- @region estimation.total
-- @provenance definition
/-- The total of a list of whole numbers. -/
def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs
-- @endregion

-- @region estimation.total_rounded
-- @provenance definition
/-- Round every number in the list to the nearest ten first, then add. -/
def totalRounded : List Nat → Nat
  | [] => 0
  | x :: xs => roundTen x + totalRounded xs
-- @endregion

-- @region estimation.rounded_total_error
-- @provenance independent
/-- Rounding `k` numbers before adding can move the total by up to `5` for each number: the
rounded total is at most `5 × k` above and at most `4 × k` below the true total. Induction on
the list, adding one number's rounding error (`roundTen_error`) at a time. -/
theorem rounded_total_error (xs : List Nat) :
    totalRounded xs ≤ total xs + 5 * xs.length ∧ total xs ≤ totalRounded xs + 4 * xs.length := by
  induction xs with
  | nil => simp [totalRounded, total]
  | cons x xs ih =>
    have hx := roundTen_error x
    simp only [totalRounded, total, List.length_cons]
    omega
-- @endregion

-- @region estimation.error_bound_reached
-- @provenance independent
/-- The bound `5 × k` can really be reached: `15 + 15 + 15 = 45`, but rounding each `15` up
to `20` gives `60`, which is `15 = 5 × 3` too much. -/
theorem error_bound_reached :
    totalRounded [15, 15, 15] = 60 ∧ total [15, 15, 15] = 45 ∧ 60 = 45 + 5 * 3 := by decide
-- @endregion

-- @region estimation.double_rounding
-- @provenance independent
/-- Rounding twice can go wrong. In hundredths, `3.46` is `346`. Rounded to the nearest whole
(`roundHundred`) it is `300`, that is `3`. But rounding first to the nearest tenth (`350`, that
is `3.5`) and then to the nearest whole gives `400`, that is `4`. -/
theorem double_rounding : roundHundred 346 = 300 ∧ roundTen 346 = 350 ∧ roundHundred 350 = 400 := by
  decide
-- @endregion

end Lumenary.Estimation
