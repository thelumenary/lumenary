/-
The Lumenary — formal mathematics
Riemannian geometry: the algebra of curvature tensors (pair symmetry from the Bianchi
identity), the curvature tensor of constant curvature `k` with its sectional and Ricci
curvatures, Jacobi fields and conjugate points in constant curvature, the index-form computation
at the heart of the Bonnet–Myers theorem, semicircles as geodesics of the hyperbolic plane, and
the Riemannian distance of Euclidean space.

What is proved here and what Mathlib provides. Mathlib has Riemannian metrics on vector bundles,
the typeclass `IsRiemannianManifold` (the distance is the infimum of lengths of `C¹` paths), the
Riemannian distance `riemannianEDist` with its triangle inequality, and the theorem that an inner
product space with its canonical metric is a Riemannian manifold; we cite the last two. Mathlib
does not yet have the Levi-Civita connection, geodesics of a general metric, curvature tensors,
Gauss–Bonnet or the comparison theorems. The *independent* declarations below formalise the
pointwise algebra and one-variable analysis that the lesson's proofs reduce to: the symmetries of
algebraic curvature tensors, the model tensors of constant curvature, the solutions
`sin(√k t)/√k` of the Jacobi equation, the integral `∫₀ᴸ (V'² - kV²) = (L/2)((π/L)² - k)`, and the
geodesic equations for a semicircle in the upper half-plane.
-/
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Lumenary.RiemannianGeometry

open Real Manifold

/-! ### Algebraic curvature tensors -/

-- @region riemannian_geometry.pair_symmetry
-- @provenance independent
/-- **Pair symmetry of the curvature tensor.** Any function `R(x, y, z, w)` that is antisymmetric
in `x, y`, antisymmetric in `z, w`, and satisfies the first Bianchi identity
`R(x,y,z,w) + R(y,z,x,w) + R(z,x,y,w) = 0`, also satisfies `R(x,y,z,w) = R(z,w,x,y)`.
The proof adds four instances of the Bianchi identity (the "octahedron" argument); no linearity
is needed. -/
theorem pair_symmetry {E : Type*} (R : E → E → E → E → ℝ)
    (anti₁ : ∀ x y z w, R x y z w = -R y x z w)
    (anti₂ : ∀ x y z w, R x y z w = -R x y w z)
    (bianchi : ∀ x y z w, R x y z w + R y z x w + R z x y w = 0) (x y z w : E) :
    R x y z w = R z w x y := by
  have b1 := bianchi x y z w
  have b2 := bianchi y z w x
  have b3 := bianchi z w x y
  have b4 := bianchi w x y z
  linarith [anti₁ y z x w, anti₂ y z x w, anti₁ z x y w, anti₂ z x y w,
    anti₁ y z w x, anti₂ y z w x, anti₁ z w y x, anti₂ z w y x, anti₁ w y z x, anti₂ w y z x,
    anti₁ w x z y, anti₂ w x z y, anti₁ x z w y, anti₂ x z w y,
    anti₁ w x y z, anti₂ w x y z, anti₁ x y w z, anti₂ x y w z, anti₁ y w x z, anti₂ y w x z,
    anti₂ z w y x, anti₁ x z y w, anti₂ y x z w, anti₁ y x w z,
    anti₂ x w z y, anti₁ w y x z, anti₂ w x z y]
-- @endregion

section ConstantCurvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- @region riemannian_geometry.const_curv
-- @provenance definition
/-- **The curvature tensor of constant curvature `k`**:
`R(x, y, z, w) = k (⟨y, z⟩⟨x, w⟩ - ⟨x, z⟩⟨y, w⟩)`, i.e. `R(x, y)z = k(⟨y, z⟩x - ⟨x, z⟩y)` with the
convention `R(x,y,z,w) = ⟨R(x,y)z, w⟩`. It is the curvature tensor of the round sphere of radius
`1/√k` (`k > 0`), of Euclidean space (`k = 0`) and of hyperbolic space (`k < 0`). -/
def constCurv (k : ℝ) (x y z w : E) : ℝ :=
  k * (inner ℝ y z * inner ℝ x w - inner ℝ x z * inner ℝ y w)
-- @endregion

-- @region riemannian_geometry.const_curv_symmetries
-- @provenance independent
/-- The constant-curvature tensor has the symmetries of a curvature tensor: antisymmetry in
each pair, and the first Bianchi identity (the six terms cancel in pairs because the inner
product is symmetric). -/
theorem constCurv_symmetries (k : ℝ) (x y z w : E) :
    constCurv k x y z w = -constCurv k y x z w ∧
      constCurv k x y z w = -constCurv k x y w z ∧
      constCurv k x y z w + constCurv k y z x w + constCurv k z x y w = 0 := by
  simp only [constCurv]
  refine ⟨by ring, by ring, ?_⟩
  rw [real_inner_comm x y, real_inner_comm x z, real_inner_comm y z]
  ring
-- @endregion

-- @region riemannian_geometry.sectional_const_curv
-- @provenance independent
/-- **Its sectional curvature is `k`** for every plane: `R(x, y, y, x) = k (‖x‖²‖y‖² - ⟨x,y⟩²)`,
and the sectional curvature of the plane spanned by `x, y` is `R(x,y,y,x)` divided by
`‖x‖²‖y‖² - ⟨x,y⟩²` (the squared area of the parallelogram). -/
theorem sectional_constCurv (k : ℝ) (x y : E) :
    constCurv k x y y x = k * (‖x‖ ^ 2 * ‖y‖ ^ 2 - inner ℝ x y ^ 2) := by
  simp only [constCurv, real_inner_self_eq_norm_sq, real_inner_comm y x]
  ring
-- @endregion

end ConstantCurvature

-- @region riemannian_geometry.ricci_const_curv
-- @provenance independent
/-- **Ricci curvature in constant curvature `k`** on `ℝⁿ`: tracing over an orthonormal basis,
`Ric(y, z) = Σᵢ R(eᵢ, y, z, eᵢ) = (n - 1) k ⟨y, z⟩`. The key step is Parseval's identity
`Σᵢ ⟨eᵢ, z⟩⟨y, eᵢ⟩ = ⟨y, z⟩`. This is the hypothesis `Ric ≥ (n - 1)k` of the Bonnet–Myers
theorem, with equality for the round sphere. -/
theorem ricci_constCurv (n : ℕ) (k : ℝ) (y z : EuclideanSpace ℝ (Fin n)) :
    ∑ i, constCurv k (EuclideanSpace.basisFun (Fin n) ℝ i) y z
        (EuclideanSpace.basisFun (Fin n) ℝ i) = (n - 1) * k * inner ℝ y z := by
  have hpars : ∑ i, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) z *
      inner ℝ y (EuclideanSpace.basisFun (Fin n) ℝ i) = inner ℝ y z := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner y z]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ∀ i, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i) = (1 : ℝ) := fun i => by
    rw [real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i]
    norm_num
  simp only [constCurv, hnorm, mul_one]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hpars]
  simp
  ring
-- @endregion

/-! ### Jacobi fields and conjugate points -/

-- @region riemannian_geometry.jacobi_constant_curvature
-- @provenance independent
/-- **Jacobi fields in constant curvature `k > 0`.** Along a unit-speed geodesic, a normal Jacobi
field `J(t) E(t)` (with `E` parallel) satisfies `J'' + kJ = 0`. The solution with `J(0) = 0`,
`J'(0) = 1` is `J(t) = sin(√k t)/√k`: we check `J' = cos(√k t)`, `(cos(√k t))' = -k J(t)`, and
that `J` vanishes again at `t = π/√k` — the first **conjugate point**, where geodesics leaving a
point meet again (the antipode, on the sphere of radius `1/√k`). -/
theorem jacobi_constant_curvature {k : ℝ} (hk : 0 < k) :
    (∀ t, HasDerivAt (fun t => sin (√k * t) / √k) (cos (√k * t)) t) ∧
      (∀ t, HasDerivAt (fun t => cos (√k * t)) (-k * (sin (√k * t) / √k)) t) ∧
      sin (√k * 0) / √k = 0 ∧ sin (√k * (π / √k)) / √k = 0 ∧
      ∀ t, 0 < t → t < π / √k → 0 < sin (√k * t) / √k := by
  have hs : 0 < √k := Real.sqrt_pos.mpr hk
  have hsq : √k * √k = k := Real.mul_self_sqrt hk.le
  refine ⟨fun t => ?_, fun t => ?_, by simp, ?_, fun t ht ht' => ?_⟩
  · have h := ((hasDerivAt_id t).const_mul √k).sin.div_const √k
    simp only [id, mul_one] at h
    convert h using 1
    field_simp
  · have h := ((hasDerivAt_id t).const_mul √k).cos
    simp only [id, mul_one] at h
    convert h using 1
    calc -k * (sin (√k * t) / √k) = -(√k * √k) * (sin (√k * t) / √k) := by rw [hsq]
      _ = -sin (√k * t) * √k := by field_simp
  · rw [mul_div_cancel₀ π hs.ne', sin_pi, zero_div]
  · apply div_pos _ hs
    apply sin_pos_of_pos_of_lt_pi (mul_pos hs ht)
    calc √k * t < √k * (π / √k) := mul_lt_mul_of_pos_left ht' hs
      _ = π := mul_div_cancel₀ π hs.ne'
-- @endregion

/-! ### The index form in the proof of Bonnet–Myers -/

-- @region riemannian_geometry.myers_index_form
-- @provenance independent
/-- **The index-form integral in the Bonnet–Myers theorem.** For `V(t) = sin(πt/L)`,
`∫₀ᴸ (V'(t)² - k V(t)²) dt = (L/2)((π/L)² - k)`. Summed over `n - 1` parallel orthonormal fields
along a geodesic of length `L`, with `Ric ≥ (n-1)k`, this bounds the second variation of energy. -/
theorem myers_index_form {L : ℝ} (hL : 0 < L) (k : ℝ) :
    ∫ t in (0 : ℝ)..L, ((π / L) ^ 2 * cos (π / L * t) ^ 2 - k * sin (π / L * t) ^ 2) =
      L / 2 * ((π / L) ^ 2 - k) := by
  have hc : π / L ≠ 0 := div_ne_zero pi_ne_zero hL.ne'
  have hcos : ∫ t in (0 : ℝ)..L, cos (π / L * t) ^ 2 = L / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => cos x ^ 2) hc, mul_zero,
      div_mul_cancel₀ π hL.ne', integral_cos_sq]
    simp
    field_simp
  have hsin : ∫ t in (0 : ℝ)..L, sin (π / L * t) ^ 2 = L / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => sin x ^ 2) hc, mul_zero,
      div_mul_cancel₀ π hL.ne', integral_sin_sq]
    simp
    field_simp
  have hi1 : IntervalIntegrable (fun t => (π / L) ^ 2 * cos (π / L * t) ^ 2) MeasureTheory.volume
      0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable (fun t => k * sin (π / L * t) ^ 2) MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcos, hsin]
  ring
-- @endregion

-- @region riemannian_geometry.myers_index_negative
-- @provenance independent
/-- **The second variation is negative on long geodesics.** If `k > 0` and the geodesic is
longer than `π/√k`, the index-form integral is negative; so a geodesic of length `> π/√k` in a
manifold with `Ric ≥ (n-1)k > 0` is not minimising. Hence the diameter is at most `π/√k`. -/
theorem myers_index_negative {L k : ℝ} (hk : 0 < k) (hL : π / √k < L) :
    ∫ t in (0 : ℝ)..L, ((π / L) ^ 2 * cos (π / L * t) ^ 2 - k * sin (π / L * t) ^ 2) < 0 := by
  have hs : 0 < √k := Real.sqrt_pos.mpr hk
  have hL0 : 0 < L := lt_trans (div_pos pi_pos hs) hL
  rw [myers_index_form hL0 k]
  apply mul_neg_of_pos_of_neg (by positivity)
  have h1 : π / L < √k := by
    rw [div_lt_iff₀ hL0]
    rw [div_lt_iff₀ hs] at hL
    linarith
  have h2 : (π / L) ^ 2 < √k ^ 2 := by
    apply pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
  rw [Real.sq_sqrt hk.le] at h2
  linarith
-- @endregion

/-! ### A geodesic of the hyperbolic plane -/

-- @region riemannian_geometry.semicircle_geodesic
-- @provenance independent
/-- **Semicircles are geodesics of the hyperbolic plane.** In the upper half-plane with metric
`(dx² + dy²)/y²`, the geodesic equations are `x'' - (2/y) x'y' = 0` and
`y'' + (x'² - y'²)/y = 0`. The curve `x = tanh t = sinh t / cosh t`, `y = sech t = 1 / cosh t`
runs along the unit semicircle (`x² + y² = 1`) with hyperbolic speed `1`; we verify its
derivatives and both equations. -/
theorem semicircle_geodesic (t : ℝ) :
    HasDerivAt (fun t => sinh t / cosh t) (1 / cosh t ^ 2) t ∧
      HasDerivAt (fun t => 1 / cosh t ^ 2) (-2 * sinh t / cosh t ^ 3) t ∧
      HasDerivAt (fun t => 1 / cosh t) (-sinh t / cosh t ^ 2) t ∧
      HasDerivAt (fun t => -sinh t / cosh t ^ 2) ((sinh t ^ 2 - 1) / cosh t ^ 3) t ∧
      (sinh t / cosh t) ^ 2 + (1 / cosh t) ^ 2 = 1 ∧
      ((1 / cosh t ^ 2) ^ 2 + (-sinh t / cosh t ^ 2) ^ 2) / (1 / cosh t) ^ 2 = 1 ∧
      -2 * sinh t / cosh t ^ 3 - 2 / (1 / cosh t) * (1 / cosh t ^ 2) * (-sinh t / cosh t ^ 2) = 0 ∧
      (sinh t ^ 2 - 1) / cosh t ^ 3 +
        ((1 / cosh t ^ 2) ^ 2 - (-sinh t / cosh t ^ 2) ^ 2) / (1 / cosh t) = 0 := by
  have hc : cosh t ≠ 0 := (cosh_pos t).ne'
  have hid : cosh t ^ 2 = sinh t ^ 2 + 1 := cosh_sq t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert (hasDerivAt_sinh t).div (hasDerivAt_cosh t) hc using 1
    field_simp
    linear_combination -hid
  · convert ((hasDerivAt_cosh t).pow 2).inv (pow_ne_zero 2 hc) |>.const_mul 1 using 1
    · ext s; simp [div_eq_mul_inv]
    · simp only [Pi.pow_apply]
      field_simp
      ring
  · convert (hasDerivAt_cosh t).inv hc |>.const_mul 1 using 1
    · ext s; simp [div_eq_mul_inv]
    · field_simp
  · convert ((hasDerivAt_sinh t).neg).div ((hasDerivAt_cosh t).pow 2) (pow_ne_zero 2 hc) using 1
    simp only [Pi.pow_apply, Pi.neg_apply]
    field_simp
    norm_num
    linear_combination cosh t * hid
  · field_simp
    linear_combination -hid
  · field_simp
    linear_combination -hid
  · field_simp
    ring
  · field_simp
    ring
-- @endregion

/-! ### Riemannian distance -/

-- @region riemannian_geometry.euclidean_riemannian_distance
-- @provenance library
open Bundle in
/-- **In Euclidean space, the Riemannian distance is the usual distance**: the infimum of the
lengths of `C¹` paths from `x` to `y` equals `‖x - y‖`, attained by the straight segment. This is
Mathlib's instance `IsRiemannianManifold 𝓘(ℝ, F) F` for an inner product space `F`. -/
theorem euclidean_riemannian_distance {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x y : F) : edist x y = riemannianEDist (modelWithCornersSelf ℝ F) x y :=
  IsRiemannianManifold.out x y
-- @endregion

-- @region riemannian_geometry.riemannian_triangle
-- @provenance library
/-- The **triangle inequality** for the Riemannian distance (the infimum of lengths of `C¹`
paths) on any manifold whose tangent spaces carry a norm — in particular an inner product:
concatenating paths adds lengths. Mathlib's `riemannianEDist_triangle`. -/
theorem riemannian_triangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    (x y z : M) :
    riemannianEDist I x z ≤ riemannianEDist I x y + riemannianEDist I y z :=
  riemannianEDist_triangle
-- @endregion

end Lumenary.RiemannianGeometry
