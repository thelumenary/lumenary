/-
The Lumenary — formal mathematics
Set-builder notation, quantifiers and infinite sets.

Lean's logic is built from exactly the quantifiers of this lesson: `∀ x, P x` ("for all") and
`∃ x, P x` ("there exists"). A set described by a property, `{n ∈ ℕ | P n}`, is represented by
the property itself, a predicate `Nat → Prop` (Mathlib's `Set ℕ` is defined to be exactly this).

What is formalised: set-builder descriptions and when two of them describe the same set; the
rules for negating `∀` and `∃` (proved here, and compared with core Lean's `Classical.not_forall`
and `not_exists`); that the order of mixed quantifiers matters; vacuous truth; the difference
between checking finitely many cases (`decide`) and proving a statement about all natural numbers;
and that ℕ and the even numbers are infinite: no finite list contains them all. Core Lean only.
-/

namespace Lumenary.Quantifiers

/-! ### Set-builder notation -/

-- @region quantifiers.evens
-- @provenance definition
/-- The set `{n ∈ ℕ | n is even}`, written as a predicate: `Evens n` is the statement that `n`
leaves remainder `0` on division by `2`. -/
def Evens (n : Nat) : Prop := n % 2 = 0
-- @endregion

-- @region quantifiers.evens_examples
-- @provenance independent
/-- Membership is checked by evaluating the property: `10` is in the set, `7` is not. -/
theorem evens_examples : Evens 10 ∧ ¬ Evens 7 := by
  unfold Evens
  decide
-- @endregion

-- @region quantifiers.evens_iff_double
-- @provenance independent
/-- Two set-builder descriptions of the same set: `{n ∈ ℕ | n is even} = {2k | k ∈ ℕ}`.
A number is even exactly when it is `2k` for some natural number `k`. -/
theorem evens_iff_double (n : Nat) : Evens n ↔ ∃ k, n = 2 * k := by
  unfold Evens
  constructor
  · intro h
    exact ⟨n / 2, by omega⟩
  · intro ⟨k, hk⟩
    omega
-- @endregion

-- @region quantifiers.small_squares
-- @provenance independent
/-- `{n ∈ ℕ | n² < 20} = {0, 1, 2, 3, 4}`: a natural number has square below `20` exactly when it
is at most `4`. If `n ≥ 5` then `n · n ≥ 5 · 5 = 25`; if `n ≤ 4` then `n · n ≤ 4 · 4 = 16`. -/
theorem small_squares (n : Nat) : n * n < 20 ↔ n ≤ 4 := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro h5
    have : 5 * 5 ≤ n * n := Nat.mul_le_mul h5 h5
    omega
  · intro h
    have : n * n ≤ 4 * 4 := Nat.mul_le_mul h h
    omega
-- @endregion

/-! ### Negating quantifiers -/

-- @region quantifiers.not_forall_iff
-- @provenance independent
/-- **"Not every `x` has `P`" means "some `x` does not have `P`".**
(←) If `x` fails `P`, then not every element has `P`.
(→) By contradiction: if *no* `x` failed `P`, then every `x` would have `P` — again by
contradiction — which we were told is false. This direction uses classical logic
(`Classical.byContradiction`, a form of the law of excluded middle). -/
theorem not_forall_iff {α : Type} (P : α → Prop) : (¬ ∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hnone
    apply h
    intro x
    apply Classical.byContradiction
    intro hx
    exact hnone ⟨x, hx⟩
  · intro ⟨x, hx⟩ hall
    exact hx (hall x)
-- @endregion

-- @region quantifiers.not_forall_library
-- @provenance library
/-- The same law, applying core Lean's `Classical.not_forall`. -/
theorem not_forall_library {α : Type} (P : α → Prop) : (¬ ∀ x, P x) ↔ ∃ x, ¬ P x :=
  Classical.not_forall
-- @endregion

-- @region quantifiers.not_exists_iff
-- @provenance independent
/-- **"No `x` has `P`" means "every `x` fails `P`".** Both directions are direct: an `x` with
`P x` would contradict "every `x` fails `P`", and vice versa. (Core Lean: `not_exists`.) -/
theorem not_exists_iff {α : Type} (P : α → Prop) : (¬ ∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h ⟨x, hx⟩
    exact h x hx
-- @endregion

-- @region quantifiers.not_forall_exists
-- @provenance independent
/-- Negating a statement with two quantifiers: apply the two rules one after the other.
`¬ (∀ x, ∃ y, R x y)` becomes `∃ x, ¬ ∃ y, R x y`, which becomes `∃ x, ∀ y, ¬ R x y`. -/
theorem not_forall_exists {α β : Type} (R : α → β → Prop) :
    (¬ ∀ x, ∃ y, R x y) ↔ ∃ x, ∀ y, ¬ R x y := by
  rw [not_forall_iff]
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, (not_exists_iff (R x)).mp hx⟩
  · intro ⟨x, hx⟩
    exact ⟨x, (not_exists_iff (R x)).mpr hx⟩
-- @endregion

/-! ### The order of quantifiers -/

-- @region quantifiers.forall_exists_gt
-- @provenance independent
/-- In ℕ, **for every `x` there is a `y` with `y > x`**: given `x`, take `y = x + 1`.
Notice that `y` is allowed to depend on `x`. -/
theorem forall_exists_gt : ∀ x : Nat, ∃ y, y > x :=
  fun x => ⟨x + 1, Nat.lt_succ_self x⟩
-- @endregion

-- @region quantifiers.not_exists_forall_gt
-- @provenance independent
/-- In ℕ, **there is no `y` with `y > x` for every `x`**: such a `y` would have to be bigger
than itself. Same symbols as `forall_exists_gt`, different order — and the opposite answer. -/
theorem not_exists_forall_gt : ¬ ∃ y : Nat, ∀ x, y > x := by
  intro ⟨y, hy⟩
  exact Nat.lt_irrefl y (hy y)
-- @endregion

-- @region quantifiers.int_forall_exists
-- @provenance independent
/-- In ℤ, every number has a partner that adds to zero: `∀ x, ∃ y, x + y = 0` (take `y = -x`). -/
theorem int_forall_exists : ∀ x : Int, ∃ y, x + y = 0 :=
  fun x => ⟨-x, by omega⟩
-- @endregion

-- @region quantifiers.int_not_exists_forall
-- @provenance independent
/-- But no single number is a partner for *every* `x`: `¬ ∃ y, ∀ x, x + y = 0`. Taking `x = 0`
forces `y = 0`, and then `x = 1` gives `1 = 0`. -/
theorem int_not_exists_forall : ¬ ∃ y : Int, ∀ x : Int, x + y = 0 := by
  intro ⟨y, hy⟩
  have h0 := hy 0
  have h1 := hy 1
  omega
-- @endregion

/-! ### Vacuous truth -/

-- @region quantifiers.vacuous_empty_list
-- @provenance independent
/-- **Vacuous truth.** "Every element of the empty list is even" is true — and so is "every
element of the empty list is odd". There is no element to check, so there is no counterexample. -/
theorem vacuous_empty_list :
    (∀ n, n ∈ ([] : List Nat) → Evens n) ∧ (∀ n, n ∈ ([] : List Nat) → ¬ Evens n) := by
  constructor
  · intro n h
    exact absurd h (List.not_mem_nil)
  · intro n h
    exact absurd h (List.not_mem_nil)
-- @endregion

-- @region quantifiers.vacuous_below_zero
-- @provenance independent
/-- "Every natural number less than `0` equals `42`" is (vacuously) true: no natural number is
less than `0`. -/
theorem vacuous_below_zero : ∀ n : Nat, n < 0 → n = 42 := by
  intro n h
  omega
-- @endregion

/-! ### Checking cases versus proving for all -/

-- @region quantifiers.squares_mod_four_check
-- @provenance independent
/-- For each of the `50` numbers `n < 50`, `n²` leaves remainder `0` or `1` on division by `4`.
`decide` proves this by checking all fifty cases — a proof about these fifty numbers only. -/
theorem squares_mod_four_check : ∀ n, n < 50 → n * n % 4 = 0 ∨ n * n % 4 = 1 := by
  decide
-- @endregion

-- @region quantifiers.squares_mod_four
-- @provenance independent
/-- The same fact for **every** natural number. No computer can check infinitely many cases, but
an argument can: the remainder of `n · n` on division by `4` depends only on the remainder `r` of
`n` (`Nat.mul_mod`), and there are only four possible remainders `r = 0, 1, 2, 3`. -/
theorem squares_mod_four (n : Nat) : n * n % 4 = 0 ∨ n * n % 4 = 1 := by
  have four_cases : ∀ r, r < 4 → r * r % 4 = 0 ∨ r * r % 4 = 1 := by decide
  rw [Nat.mul_mod]
  exact four_cases (n % 4) (Nat.mod_lt n (by decide))
-- @endregion

/-! ### Infinite sets -/

-- @region quantifiers.list_max
-- @provenance definition
/-- The largest number in a finite list of natural numbers (`0` for the empty list). -/
def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)
-- @endregion

-- @region quantifiers.le_list_max
-- @provenance independent
/-- Every number in a list is at most `listMax` of the list. Proof by induction on the list:
the head is at most `max head rest`, and every element of the tail is at most `listMax tail`,
which is at most `max head (listMax tail)`. -/
theorem le_listMax : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ listMax l
  | [], x, h => absurd h List.not_mem_nil
  | y :: ys, x, h => by
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ h' => exact Nat.le_trans (le_listMax ys x h') (Nat.le_max_right y (listMax ys))
-- @endregion

-- @region quantifiers.nat_infinite
-- @provenance independent
/-- **ℕ is infinite**: for every finite list of natural numbers, one more than its largest
number is missing from it. (If `listMax l + 1` were in the list, it would be at most
`listMax l`.) -/
theorem nat_infinite (l : List Nat) : listMax l + 1 ∉ l := by
  intro h
  have := le_listMax l (listMax l + 1) h
  omega
-- @endregion

-- @region quantifiers.no_list_of_all_nats
-- @provenance independent
/-- So no finite list contains every natural number. -/
theorem no_list_of_all_nats : ¬ ∃ l : List Nat, ∀ n, n ∈ l := by
  intro ⟨l, hl⟩
  exact nat_infinite l (hl (listMax l + 1))
-- @endregion

-- @region quantifiers.evens_infinite
-- @provenance independent
/-- **The even numbers are infinite too**: for every finite list, `2 · (largest + 1)` is even,
bigger than every number in the list, and therefore missing from it. -/
theorem evens_infinite (l : List Nat) : ∃ n, Evens n ∧ n ∉ l := by
  refine ⟨2 * (listMax l + 1), ?_, ?_⟩
  · unfold Evens
    omega
  · intro h
    have := le_listMax l (2 * (listMax l + 1)) h
    omega
-- @endregion

end Lumenary.Quantifiers
