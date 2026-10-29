/-
The Lumenary — formal mathematics
Arithmetic geometry and elliptic curves: the chord-and-tangent construction, the group of
points, torsion, point counts over finite fields, the reduction of Mordell–Weil to its weak
form, and Fermat's Last Theorem for small exponents.

Proved here (`@provenance independent`): the discriminant of a short Weierstrass equation;
the algebra behind the chord and tangent constructions (the third intersection point lies on
the curve), mirroring the Vieta argument of the lesson; that `P = (2, 3)` has order exactly 6
on `y² = x³ + 1`; Bachet's duplication of `(3, 5)` on `y² = x³ − 2`; and an exhaustive check of
the Hasse bound over `𝔽₅, 𝔽₇, 𝔽₁₁, 𝔽₁₃`.

From Mathlib (`@provenance library`): the addition formula lands on the curve
(`WeierstrassCurve.Affine.equation_add`); the points form an abelian group — associativity,
the hard part, is proved in Mathlib by embedding the points into the ideal class group of the
coordinate ring; the torsion subgroup over a number field is finite; Mordell–Weil follows from
its weak form by the descent theorem (`AddCommGroup.fg_of_descent'`) and the approximate
parallelogram law for the naïve height; and Fermat's Last Theorem for exponents 3 and 4.

Not formalised (and not in Mathlib at this version): the weak Mordell–Weil theorem
(`E(K)/2E(K)` finite), hence Mordell–Weil itself; Hasse's theorem in general; the Weil
conjectures; modularity and Fermat's Last Theorem in general; Birch and Swinnerton-Dyer.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField

namespace Lumenary.ArithmeticGeometry

open WeierstrassCurve

/-! ### Weierstrass equations and the chord-and-tangent construction -/

-- @region arithmetic_geometry.short_discriminant
-- @provenance independent
/-- For a short Weierstrass equation `y² = x³ + a₄x + a₆` (so `a₁ = a₂ = a₃ = 0`), Mathlib's
general discriminant `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` simplifies to
`Δ = −16(4a₄³ + 27a₆²)`. So the curve is smooth exactly when `4a³ + 27b² ≠ 0` (away from
characteristic 2). Proof: unfold `b₂, b₄, b₆, b₈` and compute. -/
theorem short_discriminant {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [Δ, b₂, b₄, b₆, b₈, h₁, h₂, h₃]
  ring
-- @endregion

-- @region arithmetic_geometry.chord_third_point
-- @provenance independent
/-- **The chord construction.** Let `P₁ = (x₁, y₁)` and `P₂ = (x₂, y₂)` lie on
`y² = x³ + ax + b` with `x₁ ≠ x₂`, and let `ℓ` be the slope of the chord, `y₂ − y₁ = ℓ(x₂ − x₁)`.
Then the point with `x₃ = ℓ² − x₁ − x₂` and `y₃ = ℓ(x₃ − x₁) + y₁` — the third intersection of
the chord with the curve — lies on the curve. (Its reflection `(x₃, −y₃)` is `P₁ + P₂`.)

Proof, as in the lesson: subtracting the two curve equations and cancelling `x₂ − x₁` expresses
`a` through the chord; the first equation expresses `b`; after substituting, the claim is a
polynomial identity — Vieta's formula `x₁ + x₂ + x₃ = ℓ²` in disguise. -/
theorem chord_third_point {F : Type*} [Field F] {a b x₁ y₁ x₂ y₂ ℓ : F}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b)
    (hx : x₁ ≠ x₂) (hℓ : y₂ - y₁ = ℓ * (x₂ - x₁)) :
    (ℓ * ((ℓ ^ 2 - x₁ - x₂) - x₁) + y₁) ^ 2 =
      (ℓ ^ 2 - x₁ - x₂) ^ 3 + a * (ℓ ^ 2 - x₁ - x₂) + b := by
  have hy₂ : y₂ = y₁ + ℓ * (x₂ - x₁) := by linear_combination hℓ
  -- `h₂ − h₁`, factorised: `(x₂ − x₁) · (ℓ(2y₁ + ℓ(x₂ − x₁)) − (x₂² + x₁x₂ + x₁² + a)) = 0`.
  have key : (x₂ - x₁) *
      (ℓ * (2 * y₁ + ℓ * (x₂ - x₁)) - (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 + a)) = 0 := by
    rw [hy₂] at h₂
    linear_combination h₂ - h₁
  have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have ha : a = ℓ * (2 * y₁ + ℓ * (x₂ - x₁)) - (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) := by
    have := (mul_eq_zero.mp key).resolve_left hne
    linear_combination -this
  have hb : b = y₁ ^ 2 - x₁ ^ 3 - a * x₁ := by linear_combination -h₁
  rw [hb, ha]
  ring
-- @endregion

-- @region arithmetic_geometry.tangent_third_point
-- @provenance independent
/-- **The tangent construction.** If `P₁ = (x₁, y₁)` lies on `y² = x³ + ax + b` and `ℓ` is the
slope of the tangent there, `2y₁ℓ = 3x₁² + a` (implicit differentiation), then the point with
`x₃ = ℓ² − 2x₁` and `y₃ = ℓ(x₃ − x₁) + y₁` lies on the curve; its reflection is `2P₁`.
The tangent meets the curve at `P₁` twice, so Vieta now reads `2x₁ + x₃ = ℓ²`. -/
theorem tangent_third_point {F : Type*} [Field F] {a b x₁ y₁ ℓ : F}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (hℓ : 2 * y₁ * ℓ = 3 * x₁ ^ 2 + a) :
    (ℓ * ((ℓ ^ 2 - 2 * x₁) - x₁) + y₁) ^ 2 =
      (ℓ ^ 2 - 2 * x₁) ^ 3 + a * (ℓ ^ 2 - 2 * x₁) + b := by
  have ha : a = 2 * y₁ * ℓ - 3 * x₁ ^ 2 := by linear_combination -hℓ
  have hb : b = y₁ ^ 2 - x₁ ^ 3 - a * x₁ := by linear_combination -h₁
  rw [hb, ha]
  ring
-- @endregion

-- @region arithmetic_geometry.sum_on_curve
-- @provenance library
/-- Mathlib's general version, for any Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over a field: unless `P₂ = −P₁`, the point
`(addX, addY)` built from the chord (or tangent) slope `W.slope` lies on the curve.
This applies `WeierstrassCurve.Affine.equation_add`. -/
theorem sum_on_curve {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x₁ x₂ y₁ y₂ : F} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    W.toAffine.Equation (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
      (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) :=
  Affine.equation_add h₁ h₂ hxy
-- @endregion

-- @region arithmetic_geometry.add_assoc_points
-- @provenance library
/-- The chord-and-tangent law is **associative**. This is the one genuinely hard group axiom;
Mathlib proves it (D. K. Angdinata and J. Xu) not by the classical page of algebra but by
showing that `P ↦ [ideal of P]` is an injective map into the ideal class group of the
coordinate ring `F[x, y]/(W)` that turns `+` into multiplication of ideal classes — so the
points inherit associativity from a group. This applies `add_assoc` for the instance
`AddCommGroup W.toAffine.Point`. -/
theorem add_assoc_points {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (P Q R : W.toAffine.Point) : P + Q + R = P + (Q + R) :=
  add_assoc P Q R
-- @endregion

-- @region arithmetic_geometry.two_torsion
-- @provenance library
/-- On a curve `y² + a₂… = x³ + …` with `a₁ = a₃ = 0` (for instance a short Weierstrass curve),
a point with `y = 0` is its own negative, so `P + P = 0`: the points of order 2 are the
roots of the cubic. This applies `WeierstrassCurve.Affine.Point.add_self_of_Y_eq`, since
`negY x 0 = −0 − a₁x − a₃ = 0`. -/
theorem two_torsion {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) {x : F} (h : W.toAffine.Nonsingular x 0) :
    (Affine.Point.some x 0 h + Affine.Point.some x 0 h : W.toAffine.Point) = 0 :=
  Affine.Point.add_self_of_Y_eq (by simp [Affine.negY, h₁, h₃])
-- @endregion

/-! ### Worked examples over `ℚ` -/

-- @region arithmetic_geometry.torsion_curve
-- @provenance definition
/-- The curve `y² = x³ + 1` over `ℚ`, with Weierstrass coefficients
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, 0, 1)`. Its discriminant is `−16 · 27 = −432`. -/
def torsionCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 1⟩
-- @endregion

-- @region arithmetic_geometry.torsion_point
-- @provenance definition
/-- The rational point `P = (2, 3)` on `y² = x³ + 1` (indeed `9 = 8 + 1`), as an element of the
group of points. The proof obligation is that `(2, 3)` is a nonsingular point of the curve. -/
noncomputable def torsionPoint : torsionCurve.toAffine.Point :=
  .some 2 3 (by
    rw [Affine.nonsingular_iff]
    norm_num [torsionCurve, Affine.Equation, Affine.evalEval_polynomial])
-- @endregion

-- @region arithmetic_geometry.torsion_order_six
-- @provenance independent
/-- `P = (2, 3)` has **order exactly 6** on `y² = x³ + 1`. Lean computes the multiples with
Mathlib's addition law, exactly as in the lesson's table:
`2P = (0, 1)`, `3P = (−1, 0)`, `4P = (0, −1)`, `5P = (2, −3) = −P`, `6P = 0`;
none of `P, …, 5P` is the point at infinity, so the order is 6. (Mazur's theorem says that
torsion orders over `ℚ` are at most 12; this is one of the possible groups, `ℤ/6`.) -/
theorem torsion_order_six : addOrderOf torsionPoint = 6 := by
  have n2 : torsionCurve.toAffine.Nonsingular 0 1 := by
    rw [Affine.nonsingular_iff]; norm_num [torsionCurve, Affine.Equation, Affine.evalEval_polynomial]
  have n3 : torsionCurve.toAffine.Nonsingular (-1) 0 := by
    rw [Affine.nonsingular_iff]; norm_num [torsionCurve, Affine.Equation, Affine.evalEval_polynomial]
  have n4 : torsionCurve.toAffine.Nonsingular 0 (-1) := by
    rw [Affine.nonsingular_iff]; norm_num [torsionCurve, Affine.Equation, Affine.evalEval_polynomial]
  have n5 : torsionCurve.toAffine.Nonsingular 2 (-3) := by
    rw [Affine.nonsingular_iff]; norm_num [torsionCurve, Affine.Equation, Affine.evalEval_polynomial]
  -- the tangent at `P` has slope `3·2²/(2·3) = 2`
  have h2 : (2 : ℕ) • torsionPoint = .some 0 1 n2 := by
    rw [two_nsmul, torsionPoint, Affine.Point.add_self_of_Y_ne (by
      simp [torsionCurve, Affine.negY]; norm_num)]
    simp [torsionCurve, Affine.addY, Affine.negY]
    norm_num
  -- chords: `(0, 1) + P`, `(−1, 0) + P`, `(0, −1) + P`
  have h3 : (3 : ℕ) • torsionPoint = .some (-1) 0 n3 := by
    rw [succ_nsmul, h2, torsionPoint, Affine.Point.add_of_X_ne (by norm_num)]
    simp [torsionCurve, Affine.addY, Affine.negY]
    norm_num
  have h4 : (4 : ℕ) • torsionPoint = .some 0 (-1) n4 := by
    rw [succ_nsmul, h3, torsionPoint, Affine.Point.add_of_X_ne (by norm_num)]
    simp [torsionCurve, Affine.addY, Affine.negY]
    norm_num
  have h5 : (5 : ℕ) • torsionPoint = .some 2 (-3) n5 := by
    rw [succ_nsmul, h4, torsionPoint, Affine.Point.add_of_X_ne (by norm_num)]
    simp [torsionCurve, Affine.addY, Affine.negY]
    norm_num
  -- `5P = −P`, so `6P = 0`
  have h6 : (6 : ℕ) • torsionPoint = 0 := by
    rw [succ_nsmul, h5, torsionPoint, Affine.Point.add_of_Y_eq rfl]
    simp [torsionCurve, Affine.negY]
  rw [addOrderOf_eq_iff (by norm_num)]
  refine ⟨h6, fun m hm hm0 => ?_⟩
  interval_cases m
  · rw [one_nsmul, torsionPoint]; exact Affine.Point.some_ne_zero _
  · rw [h2]; exact Affine.Point.some_ne_zero _
  · rw [h3]; exact Affine.Point.some_ne_zero _
  · rw [h4]; exact Affine.Point.some_ne_zero _
  · rw [h5]; exact Affine.Point.some_ne_zero _
-- @endregion

-- @region arithmetic_geometry.bachet_curve
-- @provenance definition
/-- Bachet's curve `y² = x³ − 2` over `ℚ`: coefficients `(0, 0, 0, 0, −2)`. -/
def bachetCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, -2⟩
-- @endregion

-- @region arithmetic_geometry.bachet_duplication
-- @provenance independent
/-- **Bachet's duplication (1621).** On `y² = x³ − 2`, doubling the point `(3, 5)` with the
tangent (slope `3·3²/(2·5) = 27/10`) gives `(129/100, −383/1000)`: a new rational solution from
an old one. (`(3, 5)` has infinite order — its double is not integral, so by the
Nagell–Lutz theorem it is not torsion — but that argument is not formalised here.) -/
theorem bachet_duplication :
    ∃ (h : bachetCurve.toAffine.Nonsingular 3 5)
      (h' : bachetCurve.toAffine.Nonsingular (129 / 100) (-383 / 1000)),
      Affine.Point.some 3 5 h + Affine.Point.some 3 5 h = Affine.Point.some _ _ h' := by
  have h : bachetCurve.toAffine.Nonsingular 3 5 := by
    rw [Affine.nonsingular_iff]; norm_num [bachetCurve, Affine.Equation, Affine.evalEval_polynomial]
  have h' : bachetCurve.toAffine.Nonsingular (129 / 100) (-383 / 1000) := by
    rw [Affine.nonsingular_iff]; norm_num [bachetCurve, Affine.Equation, Affine.evalEval_polynomial]
  refine ⟨h, h', ?_⟩
  rw [Affine.Point.add_self_of_Y_ne (by simp [bachetCurve, Affine.negY]; norm_num)]
  simp [bachetCurve, Affine.addY, Affine.negY]
  norm_num
-- @endregion

-- @region arithmetic_geometry.curve_37a
-- @provenance definition
/-- The curve `37a1`: `y² + y = x³ − x`, coefficients `(0, 0, 1, −1, 0)`. It has conductor 37
and rank 1, with `E(ℚ)` generated by `(0, 0)`; it is the first curve in Cremona's tables of
positive rank. -/
def curve37a : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩
-- @endregion

-- @region arithmetic_geometry.curve_37a_discriminant
-- @provenance independent
/-- The discriminant of `y² + y = x³ − x` is `37`, so the curve has good reduction at every
prime except 37. (Proof: unfold `Δ` in terms of `b₂, b₄, b₆, b₈` and compute.) -/
theorem curve_37a_discriminant : curve37a.Δ = 37 := by
  simp only [curve37a, Δ, b₂, b₄, b₆, b₈]
  norm_num
-- @endregion

/-! ### Counting points over finite fields -/

-- @region arithmetic_geometry.point_count
-- @provenance definition
/-- The number of points of `y² = x³ + ax + b` over `𝔽_p`, computed naively: for each `x` and `y`
in `{0, …, p − 1}`, test `y² ≡ x³ + ax + b (mod p)`, then add one for the point at infinity.
(Plain natural-number arithmetic, so that the kernel can evaluate it with `decide`.) -/
def pointCount (p a b : ℕ) : ℕ :=
  ((List.range p).map fun x =>
    ((List.range p).filter fun y => (y * y) % p = (x ^ 3 + a * x + b) % p).length).sum + 1
-- @endregion

-- @region arithmetic_geometry.hasse_small_primes
-- @provenance independent
/-- **The Hasse bound, checked exhaustively for small primes.** For `p ∈ {5, 7, 11, 13}` and
every `a, b ∈ 𝔽_p` with `4a³ + 27b² ≠ 0`, the curve `y² = x³ + ax + b` has
`(#E(𝔽_p) − (p + 1))² ≤ 4p`, i.e. `|#E(𝔽_p) − (p + 1)| ≤ 2√p`. The kernel evaluates all
`25 + 49 + 121 + 169` cases (`decide`). This is a finite verification, not Hasse's theorem,
which is not yet in Mathlib. -/
theorem hasse_small_primes : ∀ p ∈ [5, 7, 11, 13], ∀ a < p, ∀ b < p,
    (4 * a ^ 3 + 27 * b ^ 2) % p ≠ 0 → ((pointCount p a b : ℤ) - (p + 1)) ^ 2 ≤ 4 * p := by
  decide
-- @endregion

/-! ### Mordell–Weil: what Mathlib already proves -/

-- @region arithmetic_geometry.torsion_finite
-- @provenance library
/-- The torsion subgroup of `E(ℚ)` is finite, for every elliptic curve over `ℚ`. Mathlib proves
this (M. Stoll) for any field with the Northcott property, using the naïve height and its
approximate parallelogram law. This applies `WeierstrassCurve.Affine.finite_torsion`. -/
theorem torsion_finite (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Finite (AddCommGroup.torsion W.toAffine.Point) :=
  Affine.finite_torsion
-- @endregion

-- @region arithmetic_geometry.mordell_weil_of_weak
-- @provenance library
/-- **Mordell–Weil, minus the weak theorem.** For an elliptic curve over a number field `K`:
if `2E(K)` has finite index in `E(K)` (the *weak* Mordell–Weil theorem), then `E(K)` is a
finitely generated abelian group. This is the descent half of the classical proof, assembled
from Mathlib's descent theorem `AddCommGroup.fg_of_descent'`, the non-negativity of heights, the
approximate parallelogram law `WeierstrassCurve.Affine.approx_parallelogram_law`, and the
Northcott property of number fields. The weak theorem itself (finiteness of `E(K)/2E(K)`,
proved with the finiteness of class groups and unit theorems) is not yet in Mathlib. -/
theorem mordell_weil_of_weak {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (hweak : (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  obtain ⟨C, hC⟩ := Affine.approx_parallelogram_law (W := W.toAffine)
  exact AddCommGroup.fg_of_descent' hweak (fun P => by
    rw [Affine.Point.naiveHeight_eq_logHeight]; exact Height.logHeight_nonneg _) hC
-- @endregion

/-! ### Fermat's Last Theorem for small exponents -/

-- @region arithmetic_geometry.flt_three
-- @provenance library
/-- Fermat's Last Theorem for exponent 3: no positive integers satisfy `a³ + b³ = c³`
(Euler, with gaps later filled). This applies Mathlib's `fermatLastTheoremThree`. -/
theorem flt_three : FermatLastTheoremFor 3 := fermatLastTheoremThree
-- @endregion

-- @region arithmetic_geometry.flt_four
-- @provenance library
/-- Fermat's Last Theorem for exponent 4, by Fermat's method of infinite descent (in fact
`a⁴ + b⁴ = c²` has no positive solutions). This applies Mathlib's `fermatLastTheoremFour`.
The general case follows from the modularity of semistable elliptic curves (Wiles,
Taylor–Wiles, 1995) via Frey curves and Ribet's theorem; that proof is not in Mathlib, and a
collaborative project led by Kevin Buzzard to formalise it in Lean began in 2024. -/
theorem flt_four : FermatLastTheoremFor 4 := fermatLastTheoremFour
-- @endregion

end Lumenary.ArithmeticGeometry
