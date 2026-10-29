/-
The Lumenary — Lean exercises: Commutative algebra (prime versus maximal, radicals).
Replace each `sorry` with a proof. Worked solutions are in `Lumenary/CommutativeAlgebra.lean`.
-/
import Lumenary.CommutativeAlgebra

namespace LumenaryExercises.CommutativeAlgebra

-- @region ex.commutative_algebra.zero_prime_not_maximal
-- @solution Lumenary.CommutativeAlgebra.zero_prime_not_maximal
/-- The zero ideal of `ℤ` is prime but not maximal.
Hint: `Ideal.isPrime_bot` gives primality. For non-maximality, show `⊥ < Ideal.span {2}`
(`bot_lt_iff_ne_bot`, `Ideal.span_singleton_eq_bot`), deduce `Ideal.span {2} = ⊤` from
maximality (`hmax.1.2`), and contradict `Ideal.span_singleton_eq_top` with `Int.isUnit_iff`. -/
theorem zero_prime_not_maximal : (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal := by
  sorry
-- @endregion

-- @region ex.commutative_algebra.x_sq_not_radical
-- @solution Lumenary.CommutativeAlgebra.x_sq_not_radical
/-- `x² ∈ (x²)` but `x ∉ (x²)` in `k[x]`.
Hint: `Ideal.mem_span_singleton` turns membership into divisibility, and
`Polynomial.X_pow_dvd_iff` turns `X ^ 2 ∣ p` into the vanishing of the coefficients of `p` in
degrees `0` and `1`. -/
theorem x_sq_not_radical (k : Type*) [Field k] :
    (Polynomial.X : Polynomial k) ^ 2 ∈ Ideal.span {Polynomial.X ^ 2} ∧
      (Polynomial.X : Polynomial k) ∉ Ideal.span {Polynomial.X ^ 2} := by
  sorry
-- @endregion

end LumenaryExercises.CommutativeAlgebra
