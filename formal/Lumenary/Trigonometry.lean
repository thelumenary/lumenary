/-
The Lumenary — formal mathematics
Trigonometry: degrees and radians, the Pythagorean identity, exact values, the addition
formulas, and the laws of cosines and sines.

Mathlib defines `Real.sin` and `Real.cos` by power series (through the complex exponential), not
by triangles, and measures angles in radians. Proved here (`@provenance independent`): exact
values such as `sin (π/3) = √3/2`, `1 + tan² θ = 1/cos² θ`, the addition formulas from the rule
`e^{i(α+β)} = e^{iα} e^{iβ}` (the lesson's rotation argument, in complex numbers), the double
angle formulas, the coordinate computation behind the law of cosines, and the fact that
`sin (α + β) = sin α + sin β` is *not* an identity. From Mathlib (`@provenance library`):
`Real.sin_sq_add_cos_sq`, `Real.sin_add`, and the laws of cosines and sines for triangles in
Euclidean space (`EuclideanGeometry.law_cos`, `EuclideanGeometry.law_sin`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

namespace Lumenary.Trigonometry

open Real
open scoped EuclideanGeometry

/-! ### Degrees and radians -/

-- @region trigonometry.deg
-- @provenance definition
/-- Convert degrees to radians: `x°` is `x · π / 180` radians. Mathlib's `Real.sin` always
expects radians, exactly like a calculator in radian mode. -/
noncomputable def deg (x : ℝ) : ℝ := x * π / 180
-- @endregion

-- @region trigonometry.sin_deg_thirty
-- @provenance independent
/-- `sin 30° = 1/2`. First `30° = π/6` radians (arithmetic), then Mathlib's exact value
`Real.sin_pi_div_six`. Note that `sin 30`, *without* the conversion, is the sine of 30 radians,
about `-0.988`. -/
theorem sin_deg_thirty : sin (deg 30) = 1 / 2 := by
  have h : deg 30 = π / 6 := by unfold deg; ring
  rw [h, sin_pi_div_six]
-- @endregion

/-! ### The Pythagorean identity and exact values -/

-- @region trigonometry.sin_sq_add_cos_sq
-- @provenance library
/-- **The Pythagorean identity** `sin² θ + cos² θ = 1`: the point `(cos θ, sin θ)` lies on the
unit circle. Applies Mathlib's `Real.sin_sq_add_cos_sq`. -/
theorem sin_sq_add_cos_sq (θ : ℝ) : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
-- @endregion

-- @region trigonometry.one_add_tan_sq
-- @provenance independent
/-- `1 + tan² θ = 1 / cos² θ` whenever `cos θ ≠ 0`: divide the Pythagorean identity by
`cos² θ`. -/
theorem one_add_tan_sq (θ : ℝ) (h : cos θ ≠ 0) : 1 + tan θ ^ 2 = 1 / cos θ ^ 2 := by
  rw [tan_eq_sin_div_cos, div_pow, eq_div_iff (pow_ne_zero 2 h), add_mul,
    div_mul_cancel₀ _ (pow_ne_zero 2 h)]
  linarith [Real.sin_sq_add_cos_sq θ]
-- @endregion

-- @region trigonometry.sin_pi_div_three
-- @provenance independent
/-- `sin 60° = √3/2`, from `cos 60° = 1/2` (Mathlib's `Real.cos_pi_div_three`), the
Pythagorean identity (so `sin² 60° = 3/4`) and the fact that `sin 60° > 0`. -/
theorem sin_pi_div_three : sin (π / 3) = √3 / 2 := by
  have hsq : sin (π / 3) ^ 2 = 3 / 4 := by
    have := Real.sin_sq_add_cos_sq (π / 3)
    rw [cos_pi_div_three] at this
    linarith
  have hpos : 0 < sin (π / 3) := by
    apply sin_pos_of_pos_of_lt_pi <;> linarith [pi_pos]
  have hroot : (√3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have hroot_pos : 0 < √3 / 2 := by positivity
  nlinarith [sq_nonneg (sin (π / 3) - √3 / 2), sq_nonneg (sin (π / 3) + √3 / 2)]
-- @endregion

/-! ### The addition formulas -/

-- @region trigonometry.addition_formulas
-- @provenance independent
/-- **The addition formulas**
`sin (α + β) = sin α cos β + cos α sin β` and `cos (α + β) = cos α cos β − sin α sin β`.
This is the lesson's rotation proof in the language of complex numbers: multiplying by
`e^{iθ} = cos θ + i sin θ` rotates the plane by `θ`, and rotating by `β` and then by `α` is
rotating by `α + β`: `e^{i(α+β)} = e^{iα} e^{iβ}` (Mathlib's `Complex.exp_add`). Expanding the
product and comparing imaginary and real parts gives the two formulas. -/
theorem addition_formulas (α β : ℝ) :
    sin (α + β) = sin α * cos β + cos α * sin β ∧
      cos (α + β) = cos α * cos β - sin α * sin β := by
  have key : Complex.exp (((α + β : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((α : ℂ) * Complex.I) * Complex.exp ((β : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin] at key
  have him := congrArg Complex.im key
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at him hre
  constructor <;> linarith
-- @endregion

-- @region trigonometry.sin_add_library
-- @provenance library
/-- The sine addition formula, straight from Mathlib (`Real.sin_add`). Compare
`addition_formulas`, which derives it from the exponential rule. -/
theorem sin_add_library (α β : ℝ) : sin (α + β) = sin α * cos β + cos α * sin β :=
  Real.sin_add α β
-- @endregion

-- @region trigonometry.sin_add_ne_add
-- @provenance independent
/-- **Sine does not distribute over addition.** "`sin (α + β) = sin α + sin β` for all `α, β`"
is false: with `α = β = π/2` the left side is `sin π = 0` and the right side is `1 + 1 = 2`. -/
theorem sin_add_ne_add : ¬ ∀ α β : ℝ, sin (α + β) = sin α + sin β := by
  intro h
  have h1 := h (π / 2) (π / 2)
  rw [add_halves, sin_pi, sin_pi_div_two] at h1
  norm_num at h1
-- @endregion

-- @region trigonometry.double_angle
-- @provenance independent
/-- **Double angle formulas** `sin 2θ = 2 sin θ cos θ` and `cos 2θ = 1 − 2 sin² θ`: put
`α = β = θ` in the addition formulas, then use `cos² θ = 1 − sin² θ`. -/
theorem double_angle (θ : ℝ) :
    sin (2 * θ) = 2 * sin θ * cos θ ∧ cos (2 * θ) = 1 - 2 * sin θ ^ 2 := by
  obtain ⟨hs, hc⟩ := addition_formulas θ θ
  rw [two_mul, hs, hc]
  constructor
  · ring
  · nlinarith [Real.sin_sq_add_cos_sq θ]
-- @endregion

/-! ### Triangles: the right-triangle definition and the laws of cosines and sines -/

-- @region trigonometry.sin_right_triangle
-- @provenance library
/-- **The power-series sine agrees with "opposite over hypotenuse".** In a right triangle with
the right angle at `B`, the sine of the angle at `C`, times the hypotenuse `AC`, is the side
`AB` opposite that angle. Applies Mathlib's
`EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two`. -/
theorem sin_right_triangle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {A B C : P} (h : ∠ A B C = π / 2) :
    sin (∠ B C A) * dist A C = dist A B :=
  EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two h
-- @endregion

-- @region trigonometry.law_of_cosines_coord
-- @provenance independent
/-- **The law of cosines, the coordinate computation.** Put the vertex `C` of the triangle at
the origin and `B = (a, 0)` on the positive x-axis. By the unit-circle definition of sine and
cosine, the vertex `A` at distance `b` from `C` and at angle `γ` is `A = (b cos γ, b sin γ)`.
By the distance formula, `c² = AB² = (b cos γ − a)² + (b sin γ)²`, and this simplifies to
`a² + b² − 2ab cos γ` using `sin² γ + cos² γ = 1`. -/
theorem law_of_cosines_coord (a b γ : ℝ) :
    (b * cos γ - a) ^ 2 + (b * sin γ) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cos γ := by
  have h := Real.sin_sq_add_cos_sq γ
  calc (b * cos γ - a) ^ 2 + (b * sin γ) ^ 2
      = b ^ 2 * (sin γ ^ 2 + cos γ ^ 2) + a ^ 2 - 2 * a * b * cos γ := by ring
    _ = a ^ 2 + b ^ 2 - 2 * a * b * cos γ := by rw [h]; ring
-- @endregion

-- @region trigonometry.law_cos
-- @provenance library
/-- **The law of cosines** for any three points of a Euclidean space (a plane, or space):
`AC² = AB² + CB² − 2 · AB · CB · cos ∠ABC`. Applies Mathlib's `EuclideanGeometry.law_cos`,
which is proved with vectors and the inner product. -/
theorem law_cos {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (A B C : P) :
    dist A C * dist A C =
      dist A B * dist A B + dist C B * dist C B - 2 * dist A B * dist C B * cos (∠ A B C) :=
  EuclideanGeometry.law_cos A B C
-- @endregion

-- @region trigonometry.law_sin
-- @provenance library
/-- **The law of sines** in the form `sin ∠ABC · BC = sin ∠CAB · CA`, that is,
`CA / sin B = BC / sin A` when the sines are non-zero. Applies Mathlib's
`EuclideanGeometry.law_sin`. -/
theorem law_sin {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (A B C : P) :
    sin (∠ A B C) * dist B C = sin (∠ C A B) * dist C A :=
  EuclideanGeometry.law_sin A B C
-- @endregion

end Lumenary.Trigonometry
