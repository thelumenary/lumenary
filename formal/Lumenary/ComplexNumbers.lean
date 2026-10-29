/-
The Lumenary — formal mathematics
Complex numbers: arithmetic with i² = −1, the modulus, polar form and De Moivre's theorem,
roots of unity, quadratics with negative discriminant, and why ℂ cannot be ordered.

Proved here (`@provenance independent`): the multiplication rule for `a + bi`; a division
example; the two-squares identity behind `|zw| = |z||w|`; `cis (α + β) = cis α · cis β` and
De Moivre's theorem `cis θ ^ n = cis (nθ)` by induction; that `cis (2πk/n)` is an `n`-th root of
unity on the unit circle; that the `n`-th roots of unity other than `1` have sum `0`; the
quadratic formula for negative discriminant; and that no "positive cone" on `ℂ` can make it an
ordered field.

From Mathlib (`@provenance library`): `Complex.I_sq`, `Complex.norm_mul`, `Complex.mul_conj`,
`Complex.exp_mul_I` (Euler's formula), `Complex.card_rootsOfUnity` (there are exactly `n`
of them) and the fundamental theorem of algebra, `Complex.exists_root`.

Notes: Mathlib builds `ℂ` as pairs of reals `⟨re, im⟩` and writes the modulus `|z|` as the norm
`‖z‖`. It has no `cis`; we define it below, and `cis_eq_exp` connects it to `exp (θ i)`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Lumenary.ComplexNumbers

open Complex

/-! ### Arithmetic -/

-- @region complex_numbers.i_sq
-- @provenance library
/-- The defining property of `i`: `i² = -1`. This applies Mathlib's `Complex.I_sq`; in Mathlib,
`I` is the pair `⟨0, 1⟩` and the equation is a computation with the multiplication rule for
pairs. -/
theorem i_sq : I ^ 2 = -1 := Complex.I_sq
-- @endregion

-- @region complex_numbers.mul_rule
-- @provenance independent
/-- **The multiplication rule.** `(a + bi)(c + di) = (ac − bd) + (ad + bc)i`: expand with the
distributive law and replace `i²` by `-1`. The `linear_combination` step says precisely that
the two sides differ by `bd (i² + 1)`, which is `0`. -/
theorem mul_rule (a b c d : ℝ) :
    ((a : ℂ) + b * I) * (c + d * I) = (a * c - b * d) + (a * d + b * c) * I := by
  linear_combination ((b : ℂ) * d) * I_sq
-- @endregion

-- @region complex_numbers.div_example
-- @provenance independent
/-- **Division by the conjugate trick.** `(3 + 4i)/(1 + 2i) = 11/5 − (2/5) i`, because
`(3 + 4i)(1 − 2i) = 11 − 2i` and `(1 + 2i)(1 − 2i) = 5`. Lean checks the equivalent statement
`3 + 4i = (11/5 − (2/5)i)(1 + 2i)`. -/
theorem div_example : (3 + 4 * I) / (1 + 2 * I) = 11 / 5 - 2 / 5 * I := by
  have h : (1 + 2 * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [div_eq_iff h]
  linear_combination (4 / 5 : ℂ) * I_sq
-- @endregion

-- @region complex_numbers.mul_conj
-- @provenance library
/-- `z · z̄ = |z|²`, a real number: this is why multiplying by the conjugate clears
denominators. Mathlib's `Complex.mul_conj` states it with `normSq z = a² + b²`. -/
theorem mul_conj (z : ℂ) : z * (starRingEnd ℂ) z = (normSq z : ℂ) := Complex.mul_conj z
-- @endregion

/-! ### The modulus is multiplicative -/

-- @region complex_numbers.two_squares_identity
-- @provenance independent
/-- **The two-squares identity** (Brahmagupta; Fibonacci's *Liber Quadratorum*):
`(a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²`. A product of two sums of two squares is again a
sum of two squares. It holds in every commutative ring; `ring` checks it. -/
theorem two_squares_identity {R : Type*} [CommRing R] (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring
-- @endregion

-- @region complex_numbers.norm_sq_mul
-- @provenance independent
/-- **`|zw|² = |z|² |w|²`.** With `z = a + bi` and `w = c + di`, `zw = (ac − bd) + (ad + bc)i`,
so this *is* the two-squares identity. (Mathlib: `Complex.normSq_mul`.) -/
theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w := by
  simp only [normSq_apply, mul_re, mul_im]
  ring
-- @endregion

-- @region complex_numbers.norm_mul
-- @provenance library
/-- **Moduli multiply:** `|zw| = |z| |w|` (Mathlib writes `‖z‖` for the modulus). This applies
Mathlib's `Complex.norm_mul`; it follows from `normSq_mul` by taking square roots. -/
theorem norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := Complex.norm_mul z w
-- @endregion

/-! ### Polar form and De Moivre's theorem -/

-- @region complex_numbers.cis
-- @provenance definition
/-- `cis θ = cos θ + i sin θ`, the point at angle `θ` on the unit circle. A number with modulus
`r` and argument `θ` is `r · cis θ`. (Mathlib has no `cis`; it uses `exp (θ * I)`, see
`cis_eq_exp`.) -/
noncomputable def cis (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * I
-- @endregion

-- @region complex_numbers.norm_cis
-- @provenance independent
/-- `cis θ` lies on the unit circle: `|cis θ| = √(cos² θ + sin² θ) = 1`. -/
theorem norm_cis (θ : ℝ) : ‖cis θ‖ = 1 := by
  rw [cis, Complex.norm_add_mul_I]
  simp [Real.cos_sq_add_sin_sq]
-- @endregion

-- @region complex_numbers.cis_add
-- @provenance independent
/-- **Multiplying adds angles:** `cis (α + β) = cis α · cis β`. Expand the right side with the
multiplication rule: its real part is `cos α cos β − sin α sin β = cos (α + β)` and its
imaginary part is `sin α cos β + cos α sin β = sin (α + β)` — the addition formulas of
trigonometry. -/
theorem cis_add (α β : ℝ) : cis (α + β) = cis α * cis β := by
  simp only [cis, Real.cos_add, Real.sin_add, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub]
  linear_combination (-(Real.sin α : ℂ) * Real.sin β) * I_sq
-- @endregion

-- @region complex_numbers.polar_mul
-- @provenance independent
/-- **Multiplication in polar form:** `(r cis α)(s cis β) = (rs) cis (α + β)`. Moduli multiply
and arguments add: a rotation combined with a scaling. -/
theorem polar_mul (r s α β : ℝ) :
    ((r : ℂ) * cis α) * ((s : ℂ) * cis β) = ((r * s : ℝ) : ℂ) * cis (α + β) := by
  rw [cis_add]
  push_cast
  ring
-- @endregion

-- @region complex_numbers.de_moivre
-- @provenance independent
/-- **De Moivre's theorem:** `(cos θ + i sin θ)ⁿ = cos nθ + i sin nθ` for every natural number
`n`. Induction on `n`: the case `0` is `1 = cis 0`, and
`cis θ ^ (k + 1) = cis θ ^ k · cis θ = cis (kθ) · cis θ = cis (kθ + θ)` by `cis_add`.
(Mathlib: `Complex.cos_add_sin_mul_I_pow`.) -/
theorem de_moivre (θ : ℝ) (n : ℕ) : cis θ ^ n = cis (n * θ) := by
  induction n with
  | zero => simp [cis]
  | succ k ih =>
    rw [pow_succ, ih, ← cis_add]
    congr 1
    push_cast
    ring
-- @endregion

-- @region complex_numbers.cis_eq_exp
-- @provenance library
/-- **Euler's formula** `e^{iθ} = cos θ + i sin θ`: our `cis θ` is Mathlib's `exp (θ * I)`.
This applies `Complex.exp_mul_I` and the fact that `cos` and `sin` of a real number are real. -/
theorem cis_eq_exp (θ : ℝ) : cis θ = Complex.exp (θ * I) := by
  rw [Complex.exp_mul_I, cis, Complex.ofReal_cos, Complex.ofReal_sin]
-- @endregion

/-! ### Roots of unity -/

-- @region complex_numbers.cis_root_of_unity
-- @provenance independent
/-- **`cis (2πk/n)` is an `n`-th root of unity.** By De Moivre,
`cis (2πk/n) ^ n = cis (2πk) = cos 2πk + i sin 2πk = 1`. Together with `norm_cis`, the `n`
numbers `cis (2πk/n)`, `k = 0, …, n − 1`, sit on the unit circle at equal angles `2π/n`:
the vertices of a regular `n`-gon. -/
theorem cis_root_of_unity (n k : ℕ) (hn : n ≠ 0) : cis (2 * Real.pi * k / n) ^ n = 1 := by
  rw [de_moivre]
  have h : (n : ℝ) * (2 * Real.pi * k / n) = k * (2 * Real.pi) := by
    field_simp
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    rw [show (k : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [h, cis, Real.cos_nat_mul_two_pi, hsin]
  simp
-- @endregion

-- @region complex_numbers.card_roots_of_unity
-- @provenance library
/-- **There are exactly `n` complex `n`-th roots of unity** (for `n ≥ 1`). This applies
Mathlib's `Complex.card_rootsOfUnity`; `rootsOfUnity n ℂ` is the group of units `ζ` with
`ζ ^ n = 1`. -/
theorem card_roots_of_unity (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n ℂ) = n :=
  Complex.card_rootsOfUnity n
-- @endregion

-- @region complex_numbers.sum_roots_of_unity
-- @provenance independent
/-- **The `n`-th roots of unity add up to `0`.** If `ω ^ n = 1` and `ω ≠ 1`, then
`1 + ω + ⋯ + ω^(n−1) = 0`: multiplying the sum by `ω − 1` telescopes to `ωⁿ − 1 = 0`
(Mathlib's `geom_sum_mul`), and `ω − 1 ≠ 0`. With `ω = cis (2π/n)` this says the vertices of a
regular `n`-gon centred at `0` balance at the centre. -/
theorem sum_roots_of_unity {ω : ℂ} {n : ℕ} (hω : ω ^ n = 1) (h1 : ω ≠ 1) :
    ∑ k ∈ Finset.range n, ω ^ k = 0 := by
  have h := geom_sum_mul ω n
  rw [hω, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
-- @endregion

/-! ### Quadratic equations -/

-- @region complex_numbers.quadratic_example
-- @provenance independent
/-- `z² + 2z + 5 = 0` has discriminant `4 − 20 = −16 < 0`, so no real roots — but
`z = −1 + 2i` is a complex root: `(−1 + 2i)² + 2(−1 + 2i) + 5 = 4 + 4i² = 0`. -/
theorem quadratic_example : (-1 + 2 * I) ^ 2 + 2 * (-1 + 2 * I) + 5 = 0 := by
  linear_combination (4 : ℂ) * I_sq
-- @endregion

-- @region complex_numbers.quadratic_formula_neg_disc
-- @provenance independent
/-- **The quadratic formula when `Δ = b² − 4ac < 0`.** With `s = √(4ac − b²)` (a real number),
`z = (−b + s i)/(2a)` solves `az² + bz + c = 0`. Proof: put `w = 2az = −b + si`; then
`4a(az² + bz + c) = w² + 2bw + 4ac = −b² + s² i² + 4ac = −b² − s² + 4ac = 0`. -/
theorem quadratic_formula_neg_disc (a b c : ℝ) (ha : a ≠ 0) (hΔ : b ^ 2 - 4 * a * c < 0)
    (z : ℂ) (hz : z = (-b + Real.sqrt (4 * a * c - b ^ 2) * I) / (2 * a)) :
    a * z ^ 2 + b * z + c = 0 := by
  set s := Real.sqrt (4 * a * c - b ^ 2) with hsdef
  have hs : s ^ 2 = 4 * a * c - b ^ 2 := Real.sq_sqrt (by linarith)
  have hs' : (s : ℂ) ^ 2 = 4 * a * c - b ^ 2 := by exact_mod_cast hs
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hw : 2 * (a : ℂ) * z = -b + s * I := by
    rw [hz]
    field_simp
  have h4 : 4 * (a : ℂ) * (a * z ^ 2 + b * z + c) = 0 := by
    linear_combination (2 * a * z + (-b + s * I) + 2 * b) * hw + (s : ℂ) ^ 2 * I_sq - hs'
  have h4a : (4 * (a : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) ha'
  exact (mul_eq_zero.mp h4).resolve_left h4a
-- @endregion

-- @region complex_numbers.fundamental_theorem_of_algebra
-- @provenance library
/-- **The fundamental theorem of algebra:** every non-constant polynomial with complex
coefficients has a complex root. This applies Mathlib's `Complex.exists_root`, whose proof
uses analysis (Liouville's theorem), well beyond this lesson. -/
theorem fundamental_theorem_of_algebra {f : Polynomial ℂ} (hf : 0 < f.degree) :
    ∃ z : ℂ, f.IsRoot z :=
  Complex.exists_root hf
-- @endregion

/-! ### ℂ cannot be ordered -/

-- @region complex_numbers.no_positive_cone
-- @provenance independent
/-- **ℂ cannot be made into an ordered field.** An ordering compatible with arithmetic is the
same as a set `P` of "positive" numbers closed under multiplication, such that every `z ≠ 0`
has `z ∈ P` or `-z ∈ P`, but never both. No such `P` exists in `ℂ`: whether `i ∈ P` or
`-i ∈ P`, the product of that number with itself is `i² = (-i)² = -1`, so `-1 ∈ P`; then
`1 = (-1)(-1) ∈ P` as well — but `1` and `-1` cannot both be positive. -/
theorem no_positive_cone (P : Set ℂ) (mul_mem : ∀ a b, a ∈ P → b ∈ P → a * b ∈ P)
    (total : ∀ z : ℂ, z ≠ 0 → z ∈ P ∨ -z ∈ P) (not_both : ∀ z : ℂ, z ∈ P → -z ∉ P) :
    False := by
  have hm1 : (-1 : ℂ) ∈ P := by
    rcases total I I_ne_zero with h | h
    · have := mul_mem _ _ h h
      rwa [← sq, I_sq] at this
    · have := mul_mem _ _ h h
      rwa [neg_mul_neg, ← sq, I_sq] at this
  have h1 : (1 : ℂ) ∈ P := by
    have := mul_mem _ _ hm1 hm1
    rwa [neg_mul_neg, one_mul] at this
  exact not_both 1 h1 hm1
-- @endregion

end Lumenary.ComplexNumbers
