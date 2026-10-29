/-
The Lumenary — formal mathematics
Number theory: primitive roots, quadratic residues and quadratic reciprocity, arithmetic
functions and Möbius inversion, sums of two squares, and Pell's equation.

What is proved here and what Mathlib provides. Proved independently: every unit modulo 8 squares
to 1, so there is no primitive root modulo 8; 3 is a primitive root modulo 7; 2 is not a square
modulo 5; squares modulo 4 are 0 or 1, so no integer ≡ 3 (mod 4) is a sum of two squares; the
Brahmagupta–Fibonacci identity; the composition law for solutions of Pell's equation; and the
fundamental solution of `x² − 13y² = 1`. Cited from Mathlib: `(ℤ/pℤ)ˣ` is cyclic, Gauss's
`∑_{d ∣ n} φ(d) = n`, Euler's criterion, the supplementary laws for `−1` and `2`, quadratic
reciprocity, Fermat's two-squares theorem, Möbius inversion, and the existence and structure of
Pell solutions.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralDomain

namespace Lumenary.ElementaryNumberTheory

/-! ### Primitive roots -/

-- @region elementary_number_theory.units_cyclic
-- @provenance library
/-- For a prime `p`, the group `(ℤ/pℤ)ˣ` is cyclic: a primitive root exists. Mathlib proves
that every finite subgroup of the units of an integral domain is cyclic
(`isCyclic_of_subgroup_isDomain`), by the counting argument of the lesson. -/
theorem units_cyclic (p : ℕ) [Fact p.Prime] : IsCyclic (ZMod p)ˣ :=
  inferInstance
-- @endregion

-- @region elementary_number_theory.sum_totient
-- @provenance library
/-- Gauss's identity `∑_{d ∣ n} φ(d) = n`, the key to the cyclicity proof. Mathlib's
`Nat.sum_totient`. -/
theorem sum_totient (n : ℕ) : ∑ d ∈ n.divisors, Nat.totient d = n :=
  Nat.sum_totient n
-- @endregion

-- @region elementary_number_theory.three_primitive_root_mod_seven
-- @provenance independent
/-- `3` is a primitive root modulo `7`: its powers `3, 2, 6, 4, 5, 1` run through all six
non-zero residues, i.e. its order is `6`. `decide` checks `3⁶ = 1` and `3ᵐ ≠ 1` for `0 < m < 6`. -/
theorem three_primitive_root_mod_seven : orderOf (3 : ZMod 7) = 6 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
-- @endregion

-- @region elementary_number_theory.units_mod_eight_sq
-- @provenance independent
/-- Every unit modulo `8` squares to `1`: `1² = 1`, `3² = 9`, `5² = 25`, `7² = 49` are all `≡ 1`.
Checked by `decide` over the four units. -/
theorem units_mod_eight_sq : ∀ u : (ZMod 8)ˣ, u ^ 2 = 1 := by
  decide
-- @endregion

-- @region elementary_number_theory.no_primitive_root_mod_eight
-- @provenance independent
/-- **There is no primitive root modulo `8`.** `(ℤ/8ℤ)ˣ` has `φ(8) = 4` elements; a generator
would have order `4`, but every unit has order dividing `2` (`units_mod_eight_sq`). -/
theorem no_primitive_root_mod_eight : ¬ IsCyclic (ZMod 8)ˣ := by
  intro h
  obtain ⟨g, hg⟩ := h.exists_generator
  have hcard : Nat.card (ZMod 8)ˣ = 4 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hord : orderOf g = 4 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (units_mod_eight_sq g)
  rw [hord] at hdvd
  omega
-- @endregion

/-! ### Quadratic residues -/

-- @region elementary_number_theory.two_not_square_mod_five
-- @provenance independent
/-- `2` is a quadratic non-residue modulo `5`: the squares modulo `5` are `0, 1, 4`. -/
theorem two_not_square_mod_five : ¬ IsSquare (2 : ZMod 5) := by
  rintro ⟨r, hr⟩
  revert hr
  revert r
  decide
-- @endregion

-- @region elementary_number_theory.euler_criterion
-- @provenance library
/-- **Euler's criterion**: for `a ≢ 0 (mod p)`, `a` is a square modulo `p` iff
`a^((p − 1)/2) ≡ 1`. Mathlib's `ZMod.euler_criterion` (here `p / 2 = (p − 1)/2` for odd `p`). -/
theorem euler_criterion (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (p / 2) = 1 :=
  ZMod.euler_criterion p ha
-- @endregion

-- @region elementary_number_theory.neg_one_square_iff
-- @provenance library
/-- **First supplementary law**: `−1` is a square modulo a prime `p` iff `p ≢ 3 (mod 4)`.
Mathlib's `ZMod.exists_sq_eq_neg_one_iff`. -/
theorem neg_one_square_iff (p : ℕ) [Fact p.Prime] : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 :=
  ZMod.exists_sq_eq_neg_one_iff
-- @endregion

-- @region elementary_number_theory.two_square_iff
-- @provenance library
/-- **Second supplementary law**: for an odd prime `p`, `2` is a square modulo `p` iff
`p ≡ ±1 (mod 8)`. Mathlib's `ZMod.exists_sq_eq_two_iff`. -/
theorem two_square_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff hp
-- @endregion

-- @region elementary_number_theory.quadratic_reciprocity
-- @provenance library
/-- **The law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`(q/p)(p/q) = (−1)^(((p−1)/2)((q−1)/2))`. Mathlib's `legendreSym.quadratic_reciprocity`,
proved (like the lesson) via Gauss's lemma and a lattice-point count. -/
theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2)
    (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq
-- @endregion

/-! ### Arithmetic functions -/

-- @region elementary_number_theory.moebius_inversion
-- @provenance library
/-- **Möbius inversion**: `g(n) = ∑_{d ∣ n} f(d)` for all `n > 0` iff
`f(n) = ∑_{de = n} μ(d) g(e)` for all `n > 0`. Mathlib's
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`. -/
theorem moebius_inversion {f g : ℕ → ℤ} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.fst : ℤ) * g x.snd = f n :=
  ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
-- @endregion

/-! ### Sums of two squares -/

-- @region elementary_number_theory.sq_mod_four
-- @provenance independent
/-- Squares modulo `4` are `0` or `1`. -/
theorem sq_mod_four : ∀ x : ZMod 4, x ^ 2 = 0 ∨ x ^ 2 = 1 := by
  decide
-- @endregion

-- @region elementary_number_theory.not_sum_two_squares
-- @provenance independent
/-- No integer `≡ 3 (mod 4)` is a sum of two squares: modulo `4`, `a² + b²` is `0 + 0`, `0 + 1`,
`1 + 0` or `1 + 1`, never `3`. In particular no prime `p ≡ 3 (mod 4)` is a sum of two squares. -/
theorem not_sum_two_squares (a b : ℤ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  intro h
  have hcast : ((a ^ 2 + b ^ 2 : ℤ) : ZMod 4) = ((3 : ℤ) : ZMod 4) := by
    rw [ZMod.intCast_eq_intCast_iff']
    simpa using h
  push_cast at hcast
  rcases sq_mod_four (a : ZMod 4) with ha | ha <;> rcases sq_mod_four (b : ZMod 4) with hb | hb <;>
    rw [ha, hb] at hcast <;> revert hcast <;> decide
-- @endregion

-- @region elementary_number_theory.brahmagupta_fibonacci
-- @provenance independent
/-- **Brahmagupta–Fibonacci identity**: a product of sums of two squares is a sum of two squares,
`(a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²` — the multiplicativity of the norm on `ℤ[i]`. -/
theorem brahmagupta_fibonacci (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring
-- @endregion

-- @region elementary_number_theory.fermat_two_squares
-- @provenance library
/-- **Fermat's two-squares theorem**: a prime `p` with `p ≢ 3 (mod 4)` is a sum of two squares.
Mathlib's `Nat.Prime.sq_add_sq`, proved via the Gaussian integers as in the lesson. -/
theorem fermat_two_squares (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hp
-- @endregion

/-! ### Pell's equation -/

-- @region elementary_number_theory.pell_composition
-- @provenance independent
/-- **Composition of Pell solutions** (Brahmagupta's *bhāvanā*): if `x₁² − d y₁² = 1` and
`x₂² − d y₂² = 1`, then `(x₁x₂ + d y₁y₂)² − d (x₁y₂ + x₂y₁)² = 1`. It is the multiplicativity of
the norm `N(x + y√d) = x² − dy²`. -/
theorem pell_composition (d x₁ y₁ x₂ y₂ : ℤ) (h₁ : x₁ ^ 2 - d * y₁ ^ 2 = 1)
    (h₂ : x₂ ^ 2 - d * y₂ ^ 2 = 1) :
    (x₁ * x₂ + d * y₁ * y₂) ^ 2 - d * (x₁ * y₂ + x₂ * y₁) ^ 2 = 1 := by
  linear_combination (x₂ ^ 2 - d * y₂ ^ 2) * h₁ + h₂
-- @endregion

-- @region elementary_number_theory.pell_thirteen
-- @provenance independent
/-- The fundamental solution of `x² − 13y² = 1` is surprisingly large: `649² − 13 · 180² = 1`. -/
theorem pell_thirteen : (649 : ℤ) ^ 2 - 13 * 180 ^ 2 = 1 := by
  norm_num
-- @endregion

-- @region elementary_number_theory.pell_exists
-- @provenance library
/-- **Pell's equation has a non-trivial solution** for every positive non-square `d`.
Mathlib's `Pell.exists_of_not_isSquare`, proved by Dirichlet's approximation argument as in the
lesson. -/
theorem pell_exists {d : ℤ} (h₀ : 0 < d) (hd : ¬ IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare h₀ hd
-- @endregion

-- @region elementary_number_theory.pell_powers
-- @provenance library
/-- Every solution with `x > 0` and `y ≥ 0` is a power of the fundamental solution `ε`:
`x + y√d = εⁿ`. Mathlib's `Pell.IsFundamental.eq_pow_of_nonneg`, stated for its structure
`Pell.Solution₁ d` of solutions. -/
theorem pell_powers {d : ℤ} {ε : Pell.Solution₁ d} (hε : Pell.IsFundamental ε)
    {a : Pell.Solution₁ d} (hx : 0 < a.x) (hy : 0 ≤ a.y) : ∃ n : ℕ, a = ε ^ n :=
  hε.eq_pow_of_nonneg hx hy
-- @endregion

end Lumenary.ElementaryNumberTheory
