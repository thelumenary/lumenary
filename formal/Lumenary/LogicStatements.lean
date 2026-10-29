/-
The Lumenary — formal mathematics
True, false, and, or, not ("for grown-ups" companion to the Grades 3–5 lesson).

A statement is a sentence that is either true or false. Lean can check a statement about small
numbers by calculating (`decide`), and it can prove a statement about *every* number by
reasoning. Here we check the lesson's examples of "and", "or" and "not"; write out the truth
tables of `&&`, `||` and `!` on `Bool` and prove De Morgan's laws by checking all four rows;
prove the same law for statements (`Prop`) by reasoning; refute two "every" claims with a single
counterexample each, even though one of them has five confirming examples; contrast checking
100 cases with proving all cases; and prove, for any list and any yes-or-no test, that the
opposite of "all pass" is "at least one fails".

Core Lean 4 only. Mathlib analogue: `not_and_or`, `not_or`, `not_forall`, `Bool.not_and`.
-/

namespace Lumenary.LogicStatements

/-! ### And, or, not on small numbers -/

-- @region logic_statements.and_example
-- @provenance independent
/-- "12 is even **and** 12 is bigger than 20" is false, because its second part is false.
"12 is even **and** 12 is smaller than 20" is true, because both parts are true. -/
theorem and_example : ¬ (12 % 2 = 0 ∧ 12 > 20) ∧ (12 % 2 = 0 ∧ 12 < 20) := by
  decide
-- @endregion

-- @region logic_statements.or_example
-- @provenance independent
/-- "Or" is inclusive. "6 is even **or** 6 is a multiple of 3" is true — and both of its parts
are true. "7 is even or 7 is bigger than 10" is false, because neither part is true. -/
theorem or_example : (6 % 2 = 0 ∨ 6 % 3 = 0) ∧ ¬ (7 % 2 = 0 ∨ 7 > 10) := by
  decide
-- @endregion

-- @region logic_statements.not_example
-- @provenance independent
/-- "Not" swaps true and false. "7 is even" is false, so "7 is **not** even" is true. -/
theorem not_example : ¬ (7 % 2 = 0) := by
  decide
-- @endregion

/-! ### Truth tables: there are only four rows -/

-- @region logic_statements.and_table
-- @provenance independent
/-- The whole truth table of **and**: `p && q` is true in just one row, the row where both are
true. -/
theorem and_table :
    (true && true) = true ∧ (true && false) = false ∧
    (false && true) = false ∧ (false && false) = false := by
  decide
-- @endregion

-- @region logic_statements.or_table
-- @provenance independent
/-- The whole truth table of **or**: `p || q` is false in just one row, the row where both are
false. In the first row both parts are true, and so is `p || q`: this "or" is inclusive. -/
theorem or_table :
    (true || true) = true ∧ (true || false) = true ∧
    (false || true) = true ∧ (false || false) = false := by
  decide
-- @endregion

-- @region logic_statements.not_not
-- @provenance independent
/-- "Not not p" is the same as `p`: swapping true and false twice changes nothing. Two rows to
check. -/
theorem not_not (p : Bool) : (!!p) = p := by
  cases p <;> rfl
-- @endregion

-- @region logic_statements.de_morgan_and
-- @provenance independent
/-- **De Morgan's law for "and".** "Not (p and q)" has the same truth value as
"(not p) or (not q)" in every row. There are only four rows (`cases p <;> cases q`), so
checking all of them is a complete proof. -/
theorem de_morgan_and (p q : Bool) : (!(p && q)) = (!p || !q) := by
  cases p <;> cases q <;> rfl
-- @endregion

-- @region logic_statements.de_morgan_or
-- @provenance independent
/-- **De Morgan's law for "or".** "Not (p or q)" has the same truth value as
"(not p) and (not q)" in all four rows. -/
theorem de_morgan_or (p q : Bool) : (!(p || q)) = (!p && !q) := by
  cases p <;> cases q <;> rfl
-- @endregion

-- @region logic_statements.not_or_iff
-- @provenance independent
/-- The same law for statements (`Prop`), proved by reasoning instead of a table. If neither
`P` nor `Q` may hold, then `P` fails and `Q` fails; and if both fail, "P or Q" cannot hold. -/
theorem not_or_iff (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩
-- @endregion

/-! ### Every, some, and counterexamples -/

-- @region logic_statements.ending_in_two_examples
-- @provenance independent
/-- Five confirming examples: 12, 32, 52, 72 and 92 all end in 2, and all of them are divisible
by 4. -/
theorem ending_in_two_examples : ∀ n ∈ [12, 32, 52, 72, 92], n % 10 = 2 ∧ n % 4 = 0 := by
  decide
-- @endregion

-- @region logic_statements.ending_in_two_counterexample
-- @provenance independent
/-- …and yet "every number that ends in 2 is divisible by 4" is **false**. One counterexample
is enough: 22 ends in 2, but 22 = 4 × 5 + 2 leaves a remainder. -/
theorem ending_in_two_counterexample : ¬ ∀ n : Nat, n % 10 = 2 → n % 4 = 0 :=
  fun h => absurd (h 22 rfl) (by decide)
-- @endregion

-- @region logic_statements.odd_not_always_prime
-- @provenance independent
/-- "Every odd number bigger than 1 is prime" (has no factors except 1 and itself) is false:
3, 5 and 7 fit, but 9 is odd and has the factor 3. -/
theorem odd_not_always_prime :
    ¬ ∀ n : Nat, n > 1 → n % 2 = 1 → ∀ d, d ∣ n → d = 1 ∨ d = n := by
  intro h
  have h3 := h 9 (by decide) (by decide) 3 ⟨3, rfl⟩
  omega
-- @endregion

-- @region logic_statements.even_prime_exists
-- @provenance independent
/-- A "some" statement needs just one example. "Some number is even and has no factors except 1
and itself" is true: 2 is such a number. -/
theorem even_prime_exists : ∃ n : Nat, n % 2 = 0 ∧ n > 1 ∧ ∀ d, d ∣ n → d = 1 ∨ d = n := by
  refine ⟨2, rfl, by decide, fun d hd => ?_⟩
  have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
  omega
-- @endregion

/-! ### Checking cases versus proving all cases -/

-- @region logic_statements.double_checked_to_100
-- @provenance independent
/-- Checking 100 cases: for each of the numbers 0, 1, …, 99, the double is even. Lean checks
the cases one by one. This says nothing yet about 100, or 1000. -/
theorem double_checked_to_100 : ∀ n, n < 100 → (2 * n) % 2 = 0 := by
  decide
-- @endregion

-- @region logic_statements.double_is_even
-- @provenance library
/-- Proving every case at once: for **every** whole number `n`, `2 × n` is even, because
`2 × n` is `n` groups of 2 with nothing left over. This applies core Lean's
`Nat.mul_mod_right`. -/
theorem double_is_even (n : Nat) : (2 * n) % 2 = 0 :=
  Nat.mul_mod_right 2 n
-- @endregion

-- @region logic_statements.not_all_iff_exists_not
-- @provenance independent
/-- **The opposite of "all pass" is "at least one fails"** — not "none pass". For any list of
things and any yes-or-no test `p`: it is *not* true that every item passes exactly when some
item fails. Proved for every list, by working through the list one item at a time. -/
theorem not_all_iff_exists_not {α : Type} (items : List α) (p : α → Bool) :
    ¬ (∀ x ∈ items, p x = true) ↔ ∃ x ∈ items, p x = false := by
  induction items with
  | nil => simp
  | cons a as ih =>
    cases h : p a <;> simp [h, ih]
-- @endregion

-- @region logic_statements.not_all_ripe
-- @provenance independent
/-- A basket of four mangoes, ripe or not. "All the mangoes are ripe" is false, but "none of the
mangoes is ripe" is false too: the opposite of "all" is "at least one is not". -/
theorem not_all_ripe :
    ¬ (∀ ripe ∈ [true, true, false, true], ripe = true) ∧
    ¬ (∀ ripe ∈ [true, true, false, true], ripe = false) ∧
    (∃ ripe ∈ [true, true, false, true], ripe = false) := by
  decide
-- @endregion

end Lumenary.LogicStatements
