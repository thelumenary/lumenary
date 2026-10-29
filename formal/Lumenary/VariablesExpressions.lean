/-
The Lumenary — formal mathematics
Variables and algebraic expressions: equivalent expressions, the distributive law, the square
of a sum, and the laws of exponents for whole-number powers.

A variable in Lean is exactly what it is on paper: a name for an arbitrary number of a given
type. A theorem that starts `∀ n : Int` (or takes `(n : Int)` as an argument) claims something
for *every* integer at once, which is what "these two expressions are equivalent" means. Core
Lean already knows the laws of arithmetic for `Int` (`Int.mul_add`, `Int.pow_add`, …). Some
results below apply such a library law directly (`@provenance library`); the others are proved
here, step by step, the way the lesson proves them (`@provenance independent`). No Mathlib is
needed: everything uses core Lean only. Mathlib proves the same identities in every commutative
ring (`add_sq`, `pow_add`, `pow_mul`, `mul_pow`).
-/

namespace Lumenary.VariablesExpressions

/-! ### Like terms and equivalent expressions -/

-- @region variables_expressions.like_terms
-- @provenance library
/-- Combining like terms: `a·x + b·x = (a + b)·x` for all integers. This is the distributive
law read from right to left; the proof applies core Lean's `Int.add_mul`. -/
theorem like_terms (a b x : Int) : a * x + b * x = (a + b) * x :=
  (Int.add_mul a b x).symm
-- @endregion

-- @region variables_expressions.stick_formulas_agree
-- @provenance independent
/-- The stick pattern: a row of `n` squares needs `3n + 1` sticks. Two other ways of
counting give `4 + 3(n − 1)` ("first square, then 3 more each time") and `4n − (n − 1)`
("4 per square, minus the shared sides"). All three expressions are equivalent: they agree for
*every* integer `n`, not just for the values we tried. -/
theorem stick_formulas_agree (n : Int) :
    4 + 3 * (n - 1) = 3 * n + 1 ∧ 4 * n - (n - 1) = 3 * n + 1 := by
  constructor
  · calc 4 + 3 * (n - 1) = 4 + (3 * n - 3 * 1) := by rw [Int.mul_sub]
      _ = 3 * n + 1 := by omega
  · omega
-- @endregion

/-! ### The square of a sum -/

-- @region variables_expressions.square_of_sum
-- @provenance independent
/-- The square of a sum: `(a + b)² = a² + 2ab + b²`, proved by using the distributive law
twice, exactly as in the lesson:
`(a + b)(a + b) = a(a + b) + b(a + b) = (a² + ab) + (ba + b²)`, then collect like terms. -/
theorem square_of_sum (a b : Int) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
  calc (a + b) ^ 2 = (a + b) * (a + b) := by
        rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
    _ = a * (a + b) + b * (a + b) := Int.add_mul a b (a + b)
    _ = (a * a + a * b) + (b * a + b * b) := by rw [Int.mul_add, Int.mul_add]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by grind
-- @endregion

-- @region variables_expressions.square_of_difference
-- @provenance independent
/-- The square of a difference, `(a − b)² = a² − 2ab + b²`, obtained from `square_of_sum`
by putting `−b` in place of `b`: a variable can stand for *any* integer, negative ones
included. -/
theorem square_of_difference (a b : Int) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 :=
  calc (a - b) ^ 2 = (a + -b) ^ 2 := by rw [Int.sub_eq_add_neg]
    _ = a ^ 2 + 2 * a * -b + (-b) ^ 2 := square_of_sum a (-b)
    _ = a ^ 2 - 2 * a * b + b ^ 2 := by grind
-- @endregion

-- @region variables_expressions.square_of_sum_counterexample
-- @provenance independent
/-- `(a + b)² = a² + b²` is **not** an identity: one counterexample is enough to refute it.
With `a = b = 1` the left side is `4` and the right side is `2`. -/
theorem square_of_sum_counterexample : ¬ ∀ a b : Int, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  intro h
  have h11 := h 1 1
  -- `h11 : (1 + 1) ^ 2 = 1 ^ 2 + 1 ^ 2`, i.e. `4 = 2`, which `decide` refutes.
  revert h11
  decide
-- @endregion

-- @region variables_expressions.square_of_sum_eq_iff
-- @provenance independent
/-- Exactly when does the tempting mistake give the right answer?
`(a + b)² = a² + b²` holds precisely when `a = 0` or `b = 0`. By `square_of_sum` the equation
says `2ab = 0`, so `ab = 0`, and a product of integers is `0` only if a factor is `0`
(`Int.mul_eq_zero`). -/
theorem square_of_sum_eq_iff (a b : Int) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 ↔ a = 0 ∨ b = 0 := by
  rw [square_of_sum]
  constructor
  · intro h
    have hab : a * b = 0 := by grind
    exact Int.mul_eq_zero.mp hab
  · rintro (rfl | rfl) <;> grind
-- @endregion

-- @region variables_expressions.two_mul_eq_sq_iff
-- @provenance independent
/-- `2x` and `x²` are different expressions, but they *can* take equal values: exactly when
`x = 0` or `x = 2`. Proof: `2x = x²` means `x² − 2x = 0`, that is `x(x − 2) = 0`, and a product
is zero only if one factor is zero. -/
theorem two_mul_eq_sq_iff (x : Int) : 2 * x = x ^ 2 ↔ x = 0 ∨ x = 2 := by
  constructor
  · intro h
    have hfac : x * (x - 2) = 0 := by grind
    rcases Int.mul_eq_zero.mp hfac with h0 | h2
    · exact Or.inl h0
    · right; omega
  · rintro (rfl | rfl) <;> decide
-- @endregion

-- @region variables_expressions.few_tests_mislead
-- @provenance independent
/-- Testing can refute an equivalence but cannot prove it. The expressions
`x + x(x − 1)(x − 2)(x − 3)` and `x` agree for `x = 0, 1, 2, 3` — four successful tests — yet
they are not equivalent, because at `x = 4` the first is `28`. -/
theorem few_tests_mislead :
    (∀ x : Int, 0 ≤ x → x ≤ 3 → x + x * (x - 1) * (x - 2) * (x - 3) = x) ∧
      (4 : Int) + 4 * (4 - 1) * (4 - 2) * (4 - 3) ≠ 4 := by
  constructor
  · intro x h0 h3
    have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  · decide
-- @endregion

/-! ### Laws of exponents (whole-number powers)

In Lean, as in the lesson, `a ^ 0 = 1` and `a ^ (n + 1) = a ^ n * a`: a power is a repeated
product. The laws are proved by induction on the exponent — the "domino" argument: prove the
law for exponent `0`, then show that if it holds for `n` it holds for `n + 1`. -/

-- @region variables_expressions.pow_add_law
-- @provenance independent
/-- `aᵐ · aⁿ = aᵐ⁺ⁿ`: `m` factors of `a` followed by `n` more make `m + n` factors.
Proof by induction on `n`, using associativity of multiplication for the step. -/
theorem pow_add_law (a : Int) (m n : Nat) : a ^ m * a ^ n = a ^ (m + n) := by
  induction n with
  | zero => rw [Int.pow_zero, Int.mul_one, Nat.add_zero]
  | succ k ih =>
    calc a ^ m * a ^ (k + 1) = a ^ m * (a ^ k * a) := by rw [Int.pow_succ]
      _ = (a ^ m * a ^ k) * a := (Int.mul_assoc _ _ _).symm
      _ = a ^ (m + k) * a := by rw [ih]
      _ = a ^ (m + (k + 1)) := by rw [← Nat.add_assoc, Int.pow_succ]
-- @endregion

-- @region variables_expressions.pow_add_library
-- @provenance library
/-- The same law, by applying core Lean's `Int.pow_add` (which states it the other way
round). Compare `pow_add_law`, which proves it here by induction. -/
theorem pow_add_library (a : Int) (m n : Nat) : a ^ m * a ^ n = a ^ (m + n) :=
  (Int.pow_add a m n).symm
-- @endregion

-- @region variables_expressions.pow_mul_law
-- @provenance independent
/-- `(aᵐ)ⁿ = aᵐⁿ`: `n` blocks of `m` factors each make `m·n` factors.
Proof by induction on `n`, using `pow_add_law` for the step. -/
theorem pow_mul_law (a : Int) (m n : Nat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => rw [Int.pow_zero, Nat.mul_zero, Int.pow_zero]
  | succ k ih =>
    calc (a ^ m) ^ (k + 1) = (a ^ m) ^ k * a ^ m := Int.pow_succ _ _
      _ = a ^ (m * k) * a ^ m := by rw [ih]
      _ = a ^ (m * k + m) := pow_add_law a (m * k) m
      _ = a ^ (m * (k + 1)) := by rw [Nat.mul_succ]
-- @endregion

-- @region variables_expressions.mul_pow_law
-- @provenance independent
/-- `(ab)ⁿ = aⁿbⁿ`: regroup the factors `ab · ab ⋯ ab` as `a ⋯ a · b ⋯ b`. The regrouping
uses commutativity, which is why this law fails for operations that do not commute (such as
matrix multiplication, later). Proof by induction on `n`. -/
theorem mul_pow_law (a b : Int) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [Int.pow_zero, Int.pow_zero, Int.pow_zero, Int.mul_one]
  | succ k ih =>
    calc (a * b) ^ (k + 1) = (a * b) ^ k * (a * b) := Int.pow_succ _ _
      _ = (a ^ k * b ^ k) * (a * b) := by rw [ih]
      _ = (a ^ k * a) * (b ^ k * b) := by grind
      _ = a ^ (k + 1) * b ^ (k + 1) := by rw [Int.pow_succ, Int.pow_succ]
-- @endregion

-- @region variables_expressions.pow_zero_forced
-- @provenance independent
/-- Why `a⁰ = 1`: if the law `a¹ · a⁰ = a¹⁺⁰ = a¹` is to hold, then for `a ≠ 0` the number
`a⁰` must be a `z` with `a · z = a`, and the only such `z` is `1` (cancel the non-zero
factor `a`, using `Int.eq_of_mul_eq_mul_left`). So the definition `a⁰ = 1` is not arbitrary:
it is the only choice that keeps the exponent laws true. -/
theorem pow_zero_forced (a z : Int) (ha : a ≠ 0) (h : a * z = a) : z = 1 := by
  have h' : a * z = a * 1 := by rw [Int.mul_one]; exact h
  exact Int.eq_of_mul_eq_mul_left ha h'
-- @endregion

end Lumenary.VariablesExpressions
