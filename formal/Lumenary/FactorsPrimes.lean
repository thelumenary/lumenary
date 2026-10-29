/-
The Lumenary — formal mathematics
Factors, multiples and primes: factor lists, prime numbers, divisibility tests, factor trees,
and Euclid's proof that the primes never run out.

Core Lean 4 only (no Mathlib). Core Lean writes "`b` is a factor of `a`" as `b ∣ a`, which by
definition means `∃ k, a = b * k`. We define primes ourselves (`IsPrime`) with the school
definition, prove that it can be checked by trying the numbers below `p` (so `decide` can test
small numbers), and then prove that every number from `1` on is a product of primes, and that
there are infinitely many primes. That the product of primes is *unique* (the fundamental
theorem of arithmetic) is not proved here. Mathlib analogue: `Nat.Prime`, `Nat.primeFactorsList`,
`Nat.prod_primeFactorsList`, `Nat.exists_infinite_primes`, and `Nat.three_dvd_iff`,
`Nat.nine_dvd_iff` for the digit tests.
-/

namespace Lumenary.FactorsPrimes

/-! ### Factors and multiples -/

-- @region factors_primes.factor_def
-- @provenance independent
/-- "`b` is a factor of `a`" (equivalently, "`a` is a multiple of `b`") means `a = b × k`
for some whole number `k`. In Lean this is exactly what `b ∣ a` means, so `Iff.rfl` proves it. -/
theorem factor_def (b a : Nat) : b ∣ a ↔ ∃ k, a = b * k := Iff.rfl
-- @endregion

-- @region factors_primes.three_and_twelve
-- @provenance independent
/-- `3` is a factor of `12` (`12 = 3 × 4`), but `12` is not a factor of `3`: the two words
point in opposite directions. -/
theorem three_and_twelve : 3 ∣ 12 ∧ ¬ (12 ∣ 3) := by decide
-- @endregion

-- @region factors_primes.factors
-- @provenance definition
/-- The list of factors of `n`: every `d` from `1` to `n` that divides `n` with remainder `0`.
(`!=` and `==` are the yes/no tests "is not equal" and "is equal".) -/
def factors (n : Nat) : List Nat := (List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)
-- @endregion

-- @region factors_primes.factors_examples
-- @provenance independent
/-- The factors of `24` and `36`, as in the lesson. `36` has an odd number of factors because
it is a square: the pair `6 × 6` contributes only one factor. -/
theorem factors_examples :
    factors 24 = [1, 2, 3, 4, 6, 8, 12, 24] ∧ factors 36 = [1, 2, 3, 4, 6, 9, 12, 18, 36] := by
  decide
-- @endregion

-- @region factors_primes.common_factors_24_36
-- @provenance independent
/-- The common factors of `24` and `36` are `1, 2, 3, 4, 6, 12`, so the greatest common factor
is `12`. -/
theorem common_factors_24_36 : (factors 24).filter (fun d => 36 % d == 0) = [1, 2, 3, 4, 6, 12] := by
  decide
-- @endregion

-- @region factors_primes.lcm_4_6
-- @provenance independent
/-- `12` is a common multiple of `4` and `6`, and no smaller positive number is.
So the least common multiple of `4` and `6` is `12`, not `4 × 6 = 24`. -/
theorem lcm_4_6 : 4 ∣ 12 ∧ 6 ∣ 12 ∧ ∀ m, m < 12 → 0 < m → ¬ (4 ∣ m ∧ 6 ∣ m) := by decide
-- @endregion

-- @region factors_primes.dvd_add_of_dvd
-- @provenance independent
/-- If `d` is a factor of `a` and of `b`, it is a factor of `a + b`:
from `a = d × j` and `b = d × k`, the distributive law gives `a + b = d × (j + k)`. -/
theorem dvd_add_of_dvd {d a b : Nat} (ha : d ∣ a) (hb : d ∣ b) : d ∣ a + b := by
  obtain ⟨j, hj⟩ := ha
  obtain ⟨k, hk⟩ := hb
  exact ⟨j + k, by rw [hj, hk, Nat.mul_add]⟩
-- @endregion

/-! ### Prime numbers -/

-- @region factors_primes.is_prime
-- @provenance definition
/-- A **prime** is a whole number greater than `1` whose only factors are `1` and itself. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
-- @endregion

-- @region factors_primes.is_prime_iff_bounded
-- @provenance independent
/-- To test whether `p` is prime it is enough to try the numbers smaller than `p`: `p ≥ 2` is
prime exactly when the only factor below `p` is `1`. (A factor of `p` is never bigger than `p`,
by `Nat.le_of_dvd`.) -/
theorem isPrime_iff_bounded (p : Nat) :
    IsPrime p ↔ 2 ≤ p ∧ ∀ m, m < p → m ∣ p → m = 1 := by
  constructor
  · intro ⟨h2, h⟩
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases h m hdvd with h1 | hp
    · exact h1
    · omega
  · intro ⟨h2, h⟩
    refine ⟨h2, fun m hdvd => ?_⟩
    have hle : m ≤ p := Nat.le_of_dvd (by omega) hdvd
    by_cases hmp : m = p
    · exact Or.inr hmp
    · exact Or.inl (h m (by omega) hdvd)
-- @endregion

-- @region factors_primes.inst_decidable_is_prime
-- @provenance definition
/-- Thanks to `isPrime_iff_bounded`, Lean can decide whether a particular number is prime by
trying every smaller number, so `decide` can check `IsPrime 97`. -/
instance instDecidableIsPrime (p : Nat) : Decidable (IsPrime p) :=
  decidable_of_iff _ (isPrime_iff_bounded p).symm
-- @endregion

-- @region factors_primes.one_not_prime
-- @provenance independent
/-- `1` is not prime: the definition asks for a number greater than `1`. -/
theorem one_not_prime : ¬ IsPrime 1 := by
  intro ⟨h2, _⟩
  -- `h2 : 2 ≤ 1`, which is false.
  exact absurd h2 (by decide)
-- @endregion

-- @region factors_primes.primes_below_30
-- @provenance independent
/-- The primes below `30`, found by testing every number. -/
theorem primes_below_30 :
    (List.range 30).filter (fun n => decide (IsPrime n)) = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] := by
  decide
-- @endregion

-- @region factors_primes.prime_97
-- @provenance independent
/-- `97` is prime, and `91 = 7 × 13` and `51 = 3 × 17` are not. -/
theorem prime_97 : IsPrime 97 ∧ ¬ IsPrime 91 ∧ ¬ IsPrime 51 := by decide
-- @endregion

-- @region factors_primes.odd_not_always_prime
-- @provenance independent
/-- "Every odd number greater than `1` is prime" is false: `9 = 3 × 3` is a counterexample. -/
theorem odd_not_always_prime : ¬ ∀ n, n % 2 = 1 → 1 < n → IsPrime n := by
  intro h
  have h9 : IsPrime 9 := h 9 (by decide) (by decide)
  exact absurd h9 (by decide)
-- @endregion

/-! ### Divisibility tests -/

-- @region factors_primes.last_digit_test
-- @provenance independent
/-- The tests for `2`, `5` and `10`: if `d` is a factor of `10`, then `d` divides `n` exactly
when it divides the last digit `n % 10`. Reason: `n = 10 × (n / 10) + n % 10`, and the first
part is always a multiple of `d`. (`Nat.dvd_add_right`: if `d ∣ x` then `d ∣ x + y ↔ d ∣ y`.) -/
theorem last_digit_test (n d : Nat) (hd : d ∣ 10) : d ∣ n ↔ d ∣ n % 10 := by
  have hsplit : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
  have htens : d ∣ 10 * (n / 10) := Nat.dvd_trans hd ⟨n / 10, rfl⟩
  constructor
  · intro h
    rw [hsplit] at h
    exact (Nat.dvd_add_right htens).mp h
  · intro h
    rw [hsplit]
    exact (Nat.dvd_add_right htens).mpr h
-- @endregion

-- @region factors_primes.of_digits
-- @provenance definition
/-- The number with digits `ds`, listed ones digit first: `ofDigits [2, 7, 5] = 572`. -/
def ofDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * ofDigits ds
-- @endregion

-- @region factors_primes.digit_sum
-- @provenance definition
/-- The sum of a list of digits: `digitSum [2, 7, 5] = 2 + 7 + 5 = 14`. -/
def digitSum : List Nat → Nat
  | [] => 0
  | d :: ds => d + digitSum ds
-- @endregion

-- @region factors_primes.nine_rule
-- @provenance independent
/-- A number and the sum of its digits leave the **same remainder** on division by `9`.
Induction on the digits: `d + 10 × m` and `d + s` have the same remainder whenever `m` and
`s` do, because `10 × m = 9 × m + m`. (`omega` does this remainder bookkeeping.) -/
theorem nine_rule (ds : List Nat) : ofDigits ds % 9 = digitSum ds % 9 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [ofDigits, digitSum]
    omega
-- @endregion

-- @region factors_primes.three_rule
-- @provenance independent
/-- The same for `3`: a number and its digit sum leave the same remainder on division by `3`. -/
theorem three_rule (ds : List Nat) : ofDigits ds % 3 = digitSum ds % 3 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [ofDigits, digitSum]
    omega
-- @endregion

-- @region factors_primes.nine_dvd_iff
-- @provenance independent
/-- The divisibility test for `9`: a number is divisible by `9` exactly when its digit sum is. -/
theorem nine_dvd_iff (ds : List Nat) : 9 ∣ ofDigits ds ↔ 9 ∣ digitSum ds := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, nine_rule]
-- @endregion

-- @region factors_primes.example_572
-- @provenance independent
/-- `572` has digit sum `14`. Both leave remainder `5` on division by `9`, and remainder `2` on
division by `3`, so `572` is divisible by neither. -/
theorem example_572 :
    ofDigits [2, 7, 5] = 572 ∧ digitSum [2, 7, 5] = 14 ∧ 572 % 9 = 5 ∧ 14 % 9 = 5 ∧
      572 % 3 = 2 ∧ 14 % 3 = 2 := by
  decide
-- @endregion

/-! ### Factor trees: every number is built from primes -/

-- @region factors_primes.not_prime_split
-- @provenance independent
/-- A number `n ≥ 2` that is not prime splits as `n = a × b` with both parts between `2` and
`n − 1`: this is one branching of a factor tree. -/
theorem not_prime_split {n : Nat} (h2 : 2 ≤ n) (hn : ¬ IsPrime n) :
    ∃ a b, 2 ≤ a ∧ a < n ∧ 2 ≤ b ∧ b < n ∧ n = a * b := by
  rw [isPrime_iff_bounded] at hn
  -- Some factor `m` below `n` is not `1`.
  have hm : ∃ m, m < n ∧ m ∣ n ∧ m ≠ 1 := by
    apply Classical.byContradiction
    intro hno
    apply hn
    refine ⟨h2, fun m hmn hdvd => ?_⟩
    apply Classical.byContradiction
    intro hm1
    exact hno ⟨m, hmn, hdvd, hm1⟩
  obtain ⟨m, hmn, ⟨k, hk⟩, hm1⟩ := hm
  -- Neither `m` nor `k` can be `0`, and `k` cannot be `1` (else `m = n`).
  have hm0 : m ≠ 0 := by
    intro h0; subst h0; omega
  have hk0 : k ≠ 0 := by
    intro h0; subst h0; omega
  have hk1 : k ≠ 1 := by
    intro h1; subst h1; omega
  -- Since `m ≥ 2`, `n = m × k ≥ 2 × k`, so `k < n`.
  have hkn : k < n := by
    have hle : 2 * k ≤ m * k := Nat.mul_le_mul_right k (by omega)
    omega
  exact ⟨m, k, by omega, hmn, by omega, hkn, hk⟩
-- @endregion

-- @region factors_primes.exists_prime_factor
-- @provenance independent
/-- Every number `n ≥ 2` has a prime factor. Strong induction: if `n` is prime, it is its own
prime factor; otherwise `n = a × b` with `2 ≤ a < n`, and a prime factor of the smaller number
`a` is also a factor of `n`. -/
theorem exists_prime_factor (n : Nat) (h2 : 2 ≤ n) : ∃ p, IsPrime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hp : IsPrime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · obtain ⟨a, b, ha2, han, _, _, hab⟩ := not_prime_split h2 hp
      obtain ⟨p, hpp, hpa⟩ := ih a han ha2
      exact ⟨p, hpp, Nat.dvd_trans hpa ⟨b, hab⟩⟩
-- @endregion

-- @region factors_primes.list_prod
-- @provenance definition
/-- The product of a list of numbers: `listProd [2, 3, 5] = 30`, and the empty product is `1`. -/
def listProd : List Nat → Nat
  | [] => 1
  | p :: ps => p * listProd ps
-- @endregion

-- @region factors_primes.list_prod_append
-- @provenance independent
/-- Multiplying two lists' products is the product of the joined list (associative law). -/
theorem listProd_append (xs ys : List Nat) : listProd (xs ++ ys) = listProd xs * listProd ys := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih => simp only [List.cons_append, listProd, ih, Nat.mul_assoc]
-- @endregion

-- @region factors_primes.factorisation_exists
-- @provenance independent
/-- Every whole number `n ≥ 1` is a product of primes (`1` is the empty product). This is the
factor tree, made precise: split any number that is not prime into two smaller factors, and
keep going. The numbers get smaller, so the splitting must stop, and then every leaf is prime.
Uniqueness of the primes (up to order) is *not* proved here. -/
theorem factorisation_exists (n : Nat) (h1 : 1 ≤ n) :
    ∃ ps : List Nat, (∀ p ∈ ps, IsPrime p) ∧ listProd ps = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn1 : n = 1
    · exact ⟨[], by simp, by simp [listProd, hn1]⟩
    · have h2 : 2 ≤ n := by omega
      by_cases hp : IsPrime n
      · exact ⟨[n], by simpa using hp, by simp [listProd]⟩
      · obtain ⟨a, b, ha2, han, hb2, hbn, hab⟩ := not_prime_split h2 hp
        obtain ⟨xs, hxs, hxa⟩ := ih a han (by omega)
        obtain ⟨ys, hys, hyb⟩ := ih b hbn (by omega)
        refine ⟨xs ++ ys, ?_, ?_⟩
        · intro p hp'
          rcases List.mem_append.mp hp' with hx | hy
          · exact hxs p hx
          · exact hys p hy
        · rw [listProd_append, hxa, hyb, hab]
-- @endregion

-- @region factors_primes.factor_tree_360
-- @provenance independent
/-- The factor tree in the lesson: `360 = 2 × 2 × 2 × 3 × 3 × 5`, and every leaf is prime. -/
theorem factor_tree_360 :
    listProd [2, 2, 2, 3, 3, 5] = 360 ∧ ∀ p ∈ [2, 2, 2, 3, 3, 5], IsPrime p := by
  decide
-- @endregion

-- @region factors_primes.is_even_prime
-- @provenance definition
/-- In the world of **even numbers only**, call an even number `n > 0` an *even-prime* if it is
not a product of two even numbers. (Testing pairs up to `n` is enough.) -/
def IsEvenPrime (n : Nat) : Prop :=
  n % 2 = 0 ∧ 0 < n ∧ ∀ a, a < n + 1 → ∀ b, b < n + 1 → a % 2 = 0 → b % 2 = 0 → a * b ≠ n
-- @endregion

-- @region factors_primes.inst_decidable_is_even_prime
-- @provenance definition
/-- Even-primeness of a particular number is a finite check, so `decide` can test it. -/
instance instDecidableIsEvenPrime (n : Nat) : Decidable (IsEvenPrime n) := by
  unfold IsEvenPrime
  exact inferInstance
-- @endregion

-- @region factors_primes.even_world_not_unique
-- @provenance independent
/-- Unique factorisation is not automatic. In the even-number world, `2`, `6`, `10` and `30`
are all even-primes, and `60 = 6 × 10 = 2 × 30` has two *different* factorisations into
even-primes. Ordinary whole numbers never behave like this, but that needs a proof. -/
theorem even_world_not_unique :
    IsEvenPrime 2 ∧ IsEvenPrime 6 ∧ IsEvenPrime 10 ∧ IsEvenPrime 30 ∧
      60 = 6 * 10 ∧ 60 = 2 * 30 := by
  decide
-- @endregion

/-! ### Euclid: the primes never run out -/

-- @region factors_primes.fact
-- @provenance definition
/-- The product `1 × 2 × ⋯ × n` (written `n!` and called "`n` factorial"). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
-- @endregion

-- @region factors_primes.fact_pos
-- @provenance independent
/-- `n!` is never `0`. -/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih
-- @endregion

-- @region factors_primes.dvd_fact
-- @provenance independent
/-- Every number from `1` to `n` is a factor of `n! = 1 × 2 × ⋯ × n`. -/
theorem dvd_fact {k n : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : k = n + 1
    · exact ⟨fact n, by rw [h]; rfl⟩
    · have hk' : k ∣ fact n := ih (by omega)
      exact Nat.dvd_trans hk' ⟨n + 1, by rw [fact, Nat.mul_comm]⟩
-- @endregion

-- @region factors_primes.infinitely_many_primes
-- @provenance independent
/-- **Euclid**: there is a prime bigger than any number `n`. Take a prime factor `p` of
`n! + 1`. If `p` were at most `n`, it would divide `n!` and `n! + 1`, hence `1`; impossible.
So `p > n`. -/
theorem infinitely_many_primes (n : Nat) : ∃ p, n < p ∧ IsPrime p := by
  have h2 : 2 ≤ fact n + 1 := by have := fact_pos n; omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_factor (fact n + 1) h2
  refine ⟨p, ?_, hp⟩
  apply Classical.byContradiction
  intro hle
  have hpf : p ∣ fact n := dvd_fact (by have := hp.1; omega) (by omega)
  have h1 : p ∣ 1 := (Nat.dvd_add_right hpf).mp hpd
  have hp1 : p ≤ 1 := Nat.le_of_dvd (by decide) h1
  have hp2 : 2 ≤ p := hp.1
  omega
-- @endregion

-- @region factors_primes.euclid_30031
-- @provenance independent
/-- Euclid's numbers need not be prime: `2 × 3 × 5 × 7 × 11 × 13 + 1 = 30031 = 59 × 509`.
But its prime factors `59` and `509` are new: neither is on the list `2, 3, 5, 7, 11, 13`. -/
theorem euclid_30031 : 2 * 3 * 5 * 7 * 11 * 13 + 1 = 59 * 509 ∧ IsPrime 59 ∧ IsPrime 509 := by
  -- Testing all 509 smaller numbers is a long computation, so we let Lean's kernel do it.
  decide +kernel
-- @endregion

end Lumenary.FactorsPrimes
