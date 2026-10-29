/-
The Lumenary — formal mathematics
Enumerative combinatorics: derangements, integer partitions, Stirling numbers, and counting
up to symmetry with Burnside's lemma.

Proved here (`@provenance independent`): the derangement formula
`D(n) = n! · Σ_{k ≤ n} (-1)^k / k!` from the recurrence; the double-counting step of Burnside's
lemma, `Σ_g |Fix g| = Σ_x |Stab x|`; and the necklace count — binary necklaces of length 6 up to
rotation — both directly, by listing canonical representatives, and through the fixed-point
counts `2^gcd(k, 6)` that Burnside's lemma averages (all checked by `decide`).

From Mathlib (`@provenance library`): `card_derangements_eq_numDerangements` (the recurrence
really counts derangements), `numDerangements_tendsto_inv_e` (`D(n)/n! → 1/e`), Euler's
partition theorem `Nat.Partition.card_odds_eq_card_distincts` (proved in Mathlib through the
generating functions of the lesson), `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`, the
orbit–stabiliser theorem and Burnside's lemma
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`.

Not formalised here: Pólya's enumeration theorem with cycle indices, and exponential generating
functions as formal power series (Mathlib has `PowerSeries`, but the species-style dictionary of
the lesson is not developed in it).
-/
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.GroupAction.Quotient

namespace Lumenary.EnumerativeCombinatorics

open Finset

/-! ### Derangements -/

-- @region enumerative_combinatorics.card_derangements
-- @provenance library
/-- The number of fixed-point-free permutations of a finite set depends only on its size, and
is computed by Mathlib's recursively defined `numDerangements`, which satisfies
`D(n + 2) = (n + 1) (D(n) + D(n + 1))`. This applies `card_derangements_eq_numDerangements`. -/
theorem card_derangements (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (derangements α) = numDerangements (Fintype.card α) :=
  card_derangements_eq_numDerangements α
-- @endregion

-- @region enumerative_combinatorics.derangements_formula
-- @provenance independent
/-- **The derangement formula** `D(n) = n! Σ_{k=0}^{n} (-1)^k / k!` (the inclusion–exclusion
formula of the lesson), proved by induction from the recurrence `D(n + 1) = (n + 1) D(n) + (-1)^(n+1)`
(Mathlib's `numDerangements_succ`): multiplying the formula for `n` by `n + 1` gives
`(n + 1)! Σ_{k ≤ n}`, and the new term is `(n + 1)! (-1)^(n+1) / (n + 1)! = (-1)^(n+1)`. -/
theorem derangements_formula (n : ℕ) :
    (numDerangements n : ℚ) =
      n.factorial * ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / k.factorial := by
  induction n with
  | zero => simp [numDerangements_zero]
  | succ n ih =>
    have h : (numDerangements (n + 1) : ℚ) = (n + 1) * (numDerangements n : ℚ) - (-1) ^ n := by
      exact_mod_cast numDerangements_succ n
    rw [h, ih, sum_range_succ (fun k => (-1 : ℚ) ^ k / k.factorial) (n + 1),
      Nat.factorial_succ]
    push_cast
    have hfact : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring
-- @endregion

-- @region enumerative_combinatorics.derangements_tendsto
-- @provenance library
/-- **A random permutation is a derangement with probability tending to `1/e`.** This applies
Mathlib's `numDerangements_tendsto_inv_e`. -/
theorem derangements_tendsto :
    Filter.Tendsto (fun n => (numDerangements n : ℝ) / n.factorial) Filter.atTop
      (nhds (Real.exp (-1))) :=
  numDerangements_tendsto_inv_e
-- @endregion

/-! ### Partitions and Stirling numbers -/

-- @region enumerative_combinatorics.euler_partition
-- @provenance library
/-- **Euler's partition theorem** (1748): the partitions of `n` into odd parts are as numerous as
the partitions of `n` into distinct parts. Mathlib proves it, as in the lesson, by showing that
the two generating functions `Π 1/(1 - x^(2k-1))` and `Π (1 + x^k)` are equal (as the case
`m = 2` of Glaisher's theorem). This applies `Nat.Partition.card_odds_eq_card_distincts`. -/
theorem euler_partition (n : ℕ) :
    (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card :=
  Nat.Partition.card_odds_eq_card_distincts n
-- @endregion

-- @region enumerative_combinatorics.pow_eq_sum_stirling
-- @provenance library
/-- **Counting functions by their image**: `m^k = Σ_j S(k, j) · m(m-1)⋯(m-j+1)`, where the
Stirling number of the second kind `S(k, j)` counts partitions of a `k`-set into `j` blocks: a
function from a `k`-set to an `m`-set is a partition of its domain into `j` nonempty fibres
together with an injective labelling of the fibres. This applies Mathlib's
`Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`. -/
theorem pow_eq_sum_stirling (m k : ℕ) :
    m ^ k = ∑ j ∈ range (k + 1), Nat.stirlingSecond k j * m.descFactorial j :=
  Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m k
-- @endregion

/-! ### Counting up to symmetry -/

-- @region enumerative_combinatorics.burnside_double_count
-- @provenance independent
/-- **The double-counting step of Burnside's lemma.** Count the pairs `(g, x)` with `g • x = x`
in two ways: by `g` (the fixed points of each group element) or by `x` (the stabiliser of each
point). Both sums are the size of the same set. -/
theorem burnside_double_count {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    [DecidableEq X] :
    ∑ g : G, #(univ.filter fun x : X => g • x = x) =
      ∑ x : X, #(univ.filter fun g : G => g • x = x) := by
  simp only [card_filter]
  exact sum_comm
-- @endregion

-- @region enumerative_combinatorics.orbit_stabilizer
-- @provenance library
/-- **The orbit–stabiliser theorem**: `|orbit x| · |Stab x| = |G|`. Dividing the stabiliser sum
above by `|G|` therefore gives `Σ_x 1/|orbit x|`, which is the number of orbits, since each orbit
contributes `1`. This applies Mathlib's `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. -/
theorem orbit_stabilizer {G X : Type*} [Group G] [MulAction G X] [Fintype G] (x : X)
    [Fintype (MulAction.orbit G x)] [Fintype (MulAction.stabilizer G x)] :
    Fintype.card (MulAction.orbit G x) * Fintype.card (MulAction.stabilizer G x) =
      Fintype.card G :=
  MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
-- @endregion

-- @region enumerative_combinatorics.burnside
-- @provenance library
/-- **Burnside's lemma** (Cauchy–Frobenius): the number of orbits times `|G|` is the total number
of fixed points, `Σ_g |Fix g|`. This applies Mathlib's
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`. -/
theorem burnside {G X : Type*} [Group G] [MulAction G X] [Fintype G]
    [∀ g : G, Fintype (MulAction.fixedBy X g)] [Fintype (MulAction.orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (MulAction.fixedBy X g) =
      Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
-- @endregion

-- @region enumerative_combinatorics.rotate
-- @provenance definition
/-- A binary necklace with `n` beads is stored as a number `x < 2^n` (bead `i` = bit `i`).
Rotating the necklace by one place moves the top bit to the bottom:
`x ↦ (2x mod 2^n) + ⌊x / 2^(n-1)⌋`. `rotate n k` rotates `k` times. -/
def rotate (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => rotate n k ((2 * x) % 2 ^ n + x / 2 ^ (n - 1))
-- @endregion

-- @region enumerative_combinatorics.is_canonical
-- @provenance definition
/-- A colouring is the *canonical representative* of its rotation class if it is the smallest
number among its rotations. Each necklace has exactly one canonical representative. -/
def isCanonical (n x : ℕ) : Bool :=
  (List.range n).all fun k => x ≤ rotate n k x
-- @endregion

-- @region enumerative_combinatorics.necklaces_six
-- @provenance independent
/-- **There are 14 binary necklaces with 6 beads** (up to rotation): exactly 14 of the 64
colourings are canonical. Checked by `decide`. -/
theorem necklaces_six : ((List.range 64).filter (isCanonical 6)).length = 14 := by
  decide
-- @endregion

-- @region enumerative_combinatorics.necklace_fixed_counts
-- @provenance independent
/-- **The fixed-point counts in Burnside's lemma for necklaces.** Rotation by `k` places fixes
exactly `2^gcd(k, 6)` of the 64 colourings (a fixed colouring is periodic with period
`gcd(k, 6)`). So Burnside's lemma gives `(64 + 2 + 4 + 8 + 4 + 2) / 6 = 84 / 6 = 14` orbits,
agreeing with `necklaces_six`. Checked by `decide`. -/
theorem necklace_fixed_counts :
    (∀ k < 6, ((List.range 64).filter fun x => rotate 6 k x = x).length = 2 ^ Nat.gcd k 6) ∧
      (∑ k ∈ range 6, 2 ^ Nat.gcd k 6) / 6 = 14 := by
  decide
-- @endregion

end Lumenary.EnumerativeCombinatorics
