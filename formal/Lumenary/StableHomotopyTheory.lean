/-
The Lumenary — formal mathematics
Stable homotopy theory: why stable groups are abelian, formal group laws and chromatic height,
Stiefel–Whitney numbers of projective spaces, and the Bernoulli numbers behind π₃ˢ and π₇ˢ.

What is proved here. Mathlib proves that the higher homotopy groups `π_{n+2}` are abelian
(Eckmann–Hilton), which is why the stable homotopy groups — colimits of them — are abelian too
(`homotopyGroup_mul_comm`). The rest formalises the *algebra* through which stable homotopy theory
is computed. (1) The additive and multiplicative formal group laws `x + y` and `x + y + xy`,
which govern ordinary cohomology and complex K-theory: we prove the formal group law axioms, the
formulas for their `n`-series, and that modulo a prime `p` the multiplicative `p`-series is `xᵖ`
(height 1) while the additive one is `0` (height ∞). (2) The binomial parities behind Thom's
cobordism computation: all Stiefel–Whitney numbers of `ℝPⁿ` vanish for `n` odd, while
`w_n[ℝPⁿ] ≠ 0` for `n` even. (3) `B₂/4 = 1/24` and `B₄/8 = −1/240`, the orders of the image of
the J-homomorphism in `π₃ˢ = ℤ/24` and `π₇ˢ = ℤ/240`. Not in Mathlib (as far as we know):
suspension, spectra, generalised cohomology theories, cobordism, K-theory, the Adams spectral
sequence, or any computation of a stable homotopy group.
-/
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bernoulli

namespace Lumenary.StableHomotopyTheory

/-! ### Homotopy groups in degrees ≥ 2 are abelian -/

-- @region stable_homotopy_theory.homotopy_group_mul_comm
-- @provenance library
/-- **Eckmann–Hilton.** For `n ≥ 0`, the homotopy group `π_{n+2}(X, x)` is abelian: two maps of the
cube `I^{n+2}` can be composed along two different coordinates, and the interchange law forces
both compositions to agree and commute. This is Mathlib's instance `HomotopyGroup.commGroup`.
Since the stable stem `πₖˢ = colim_n π_{n+k}(Sⁿ)` is a colimit of such groups, every stable
homotopy group is abelian — the first sign that stable homotopy theory is "linear". -/
theorem homotopyGroup_mul_comm {X : Type*} [TopologicalSpace X] (x : X) (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 2) X x) : a * b = b * a :=
  mul_comm a b
-- @endregion

/-! ### Formal group laws and height -/

section FormalGroupLaws

variable {A : Type*} [CommRing A]

-- @region stable_homotopy_theory.is_formal_group_law
-- @provenance definition
/-- The axioms of a (one-dimensional, commutative) **formal group law** `F`, stated as identities
in a commutative ring `A`: `F(x, 0) = x`, `F(x, y) = F(y, x)` and `F(F(x, y), z) = F(x, F(y, z))`.
A genuine formal group law is a power series in two variables; for the polynomial laws below,
holding in *every* commutative ring (for instance `A = ℤ[x, y, z]`) is the same as being a
formal group law over `ℤ`. A complex-oriented cohomology theory `E` has one: it records the first
Chern class of a tensor product of line bundles, `c₁(L ⊗ M) = F(c₁ L, c₁ M)`. -/
structure IsFormalGroupLaw (F : A → A → A) : Prop where
  zero_right : ∀ x, F x 0 = x
  comm : ∀ x y, F x y = F y x
  assoc : ∀ x y z, F (F x y) z = F x (F y z)
-- @endregion

-- @region stable_homotopy_theory.add_fgl
-- @provenance definition
/-- The **additive formal group law** `F(x, y) = x + y`: ordinary cohomology,
`c₁(L ⊗ M) = c₁(L) + c₁(M)`. -/
def addFGL (x y : A) : A := x + y
-- @endregion

-- @region stable_homotopy_theory.mul_fgl
-- @provenance definition
/-- The **multiplicative formal group law** `F(x, y) = x + y + xy`. Complex K-theory has this law
(up to sign and a unit, the Bott class): with `c₁(L) = L − 1`, `L ⊗ M − 1 = (L − 1) + (M − 1) +
(L − 1)(M − 1)`. -/
def mulFGL (x y : A) : A := x + y + x * y
-- @endregion

-- @region stable_homotopy_theory.is_formal_group_law_add
-- @provenance independent
/-- `x + y` is a formal group law: the axioms are the ring axioms for addition. -/
theorem isFormalGroupLaw_add : IsFormalGroupLaw (addFGL (A := A)) where
  zero_right x := by simp [addFGL]
  comm x y := by simp only [addFGL]; ring
  assoc x y z := by simp only [addFGL]; ring
-- @endregion

-- @region stable_homotopy_theory.is_formal_group_law_mul
-- @provenance independent
/-- `x + y + xy` is a formal group law. Associativity: both sides equal
`x + y + z + xy + xz + yz + xyz`. -/
theorem isFormalGroupLaw_mul : IsFormalGroupLaw (mulFGL (A := A)) where
  zero_right x := by simp [mulFGL]
  comm x y := by simp only [mulFGL]; ring
  assoc x y z := by simp only [mulFGL]; ring
-- @endregion

-- @region stable_homotopy_theory.one_add_mul_fgl
-- @provenance independent
/-- The multiplicative law is the multiplicative group in disguise: `1 + F(x, y) = (1 + x)(1 + y)`.
Over `ℚ` the logarithm `log(1 + x)` turns it into the additive law; over `ℤ/p` no such
isomorphism exists, which is what *height* measures. -/
theorem one_add_mulFGL (x y : A) : 1 + mulFGL x y = (1 + x) * (1 + y) := by
  simp only [mulFGL]
  ring
-- @endregion

-- @region stable_homotopy_theory.n_series
-- @provenance definition
/-- The **`n`-series** `[n]_F(x) = F(x, F(x, …, F(x, 0)))`, "`x` added to itself `n` times" with
the formal group law `F`. -/
def nSeries (F : A → A → A) : ℕ → A → A
  | 0, _ => 0
  | n + 1, x => F x (nSeries F n x)
-- @endregion

-- @region stable_homotopy_theory.add_n_series
-- @provenance independent
/-- For the additive law, `[n](x) = n x`. -/
theorem add_nSeries (n : ℕ) (x : A) : nSeries addFGL n x = n * x := by
  induction n with
  | zero => simp [nSeries]
  | succ n ih =>
    simp only [nSeries, addFGL, ih]
    push_cast
    ring
-- @endregion

-- @region stable_homotopy_theory.mul_n_series
-- @provenance independent
/-- For the multiplicative law, `1 + [n](x) = (1 + x)ⁿ`, by induction using `one_add_mulFGL`. -/
theorem mul_nSeries (n : ℕ) (x : A) : 1 + nSeries mulFGL n x = (1 + x) ^ n := by
  induction n with
  | zero => simp [nSeries]
  | succ n ih =>
    rw [nSeries, one_add_mulFGL, ih, pow_succ, mul_comm]
-- @endregion

end FormalGroupLaws

section Height

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

-- @region stable_homotopy_theory.mul_p_series_char_p
-- @provenance independent
/-- **The multiplicative formal group law has height 1 at every prime.** Over `𝔽_p`, its
`p`-series is `[p](X) = Xᵖ`: from `1 + [p](X) = (1 + X)ᵖ = 1 + Xᵖ` (the "freshman's dream" in
characteristic `p`, Mathlib's `add_pow_char`). In chromatic homotopy theory this is why complex
K-theory sits at chromatic height 1. -/
theorem mul_pSeries_charP : nSeries mulFGL p (X : (ZMod p)[X]) = X ^ p := by
  have h := mul_nSeries p (X : (ZMod p)[X])
  rw [add_pow_char, one_pow] at h
  exact add_left_cancel h
-- @endregion

-- @region stable_homotopy_theory.add_p_series_char_p
-- @provenance independent
/-- **The additive formal group law has infinite height.** Over `𝔽_p`, its `p`-series is
`[p](X) = pX = 0`. Ordinary mod-`p` cohomology sits at chromatic height ∞; the Morava K-theories
`K(n)` interpolate, with formal groups of height exactly `n`. -/
theorem add_pSeries_charP : nSeries addFGL p (X : (ZMod p)[X]) = 0 := by
  rw [add_nSeries]
  simp
-- @endregion

end Height

/-! ### Stiefel–Whitney numbers of real projective spaces -/

-- @region stable_homotopy_theory.rp_odd_sw_vanish
-- @provenance independent
/-- **Odd projective spaces bound.** The total Stiefel–Whitney class of `ℝPⁿ` is `(1 + a)ⁿ⁺¹`, so
`w_i(ℝPⁿ) = C(n+1, i) aⁱ`. If `n + 1 = 2m` is even, then `C(2m, i)` is even for every odd `i`:
from `i · C(2m, i) = 2m · C(2m − 1, i − 1)`. So only even-degree classes survive mod 2, every
Stiefel–Whitney number `w_I[ℝPⁿ]` of the odd degree `n` vanishes, and by the theorems of
Pontryagin and Thom `ℝPⁿ` is the boundary of a compact `(n+1)`-manifold. -/
theorem rp_odd_sw_vanish (m i : ℕ) (hi : Odd i) : 2 ∣ Nat.choose (2 * m) i := by
  obtain ⟨j, rfl⟩ := hi
  rcases m with _ | m
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact dvd_zero 2
  · -- `(2m + 2) · C(2m + 1, 2j) = C(2m + 2, 2j + 1) · (2j + 1)`
    have h := Nat.add_one_mul_choose_eq (2 * m + 1) (2 * j)
    have hdvd : 2 ∣ Nat.choose (2 * m + 1 + 1) (2 * j + 1) * (2 * j + 1) :=
      ⟨(m + 1) * Nat.choose (2 * m + 1) (2 * j), by rw [← h]; ring⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h2 | h2
    · simpa [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] using h2
    · omega
-- @endregion

-- @region stable_homotopy_theory.rp_even_top_sw
-- @provenance independent
/-- **Even projective spaces do not bound.** For `n = 2m`, the top Stiefel–Whitney class is
`w_n(ℝPⁿ) = C(n+1, n) aⁿ = (n+1) aⁿ`, and `n + 1` is odd, so the Stiefel–Whitney number
`w_n[ℝPⁿ]` is `1 ∈ 𝔽₂` (it is also the Euler characteristic mod 2). By Pontryagin's theorem,
`ℝP²ᵐ` is not the boundary of any compact manifold; `ℝP²` and `ℝP⁴` generate parts of Thom's
cobordism ring `𝔑_*`. -/
theorem rp_even_top_sw (m : ℕ) : ¬ 2 ∣ Nat.choose (2 * m + 1) (2 * m) := by
  rw [Nat.choose_succ_self_right]
  omega
-- @endregion

/-! ### Bernoulli numbers and the image of J -/

-- @region stable_homotopy_theory.image_of_j_orders
-- @provenance independent
/-- **Bernoulli numbers in the stable stems.** `B₂/4 = 1/24` and `B₄/8 = −1/240`. By Adams'
work on the J-homomorphism (completed by the proof of the Adams conjecture by Quillen, Sullivan
and Becker–Gottlieb), the image of `J : π_{4k−1}(SO) → π_{4k−1}ˢ` is cyclic of order the
denominator of `B_{2k}/4k`: here `24` and `240`, which are the whole groups `π₃ˢ = ℤ/24` and
`π₇ˢ = ℤ/240`. Lean checks the arithmetic, from Mathlib's `bernoulli_two` and `bernoulli'_four`;
the homotopy theory is cited. -/
theorem image_of_j_orders :
    bernoulli 2 / (2 * 2) = 1 / 24 ∧ bernoulli 4 / (2 * 4) = -1 / 240 := by
  refine ⟨?_, ?_⟩
  · rw [bernoulli_two]
    norm_num
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
    norm_num
-- @endregion

end Lumenary.StableHomotopyTheory
