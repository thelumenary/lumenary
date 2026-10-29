/-
The Lumenary — formal mathematics
Algebraic structures: binary operations, monoids, groups, rings and fields, and the
homomorphisms between them.

Mathlib organises algebra as a hierarchy of type classes: `Monoid M`, `Group G`, `Ring R`,
`Field K`, with homomorphisms `M →* N` (monoids) and `R →+* S` (rings). Below, the uniqueness
of identities and inverses, the fact that a group homomorphism must send `1` to `1` and inverses
to inverses, and the theorem "`ZMod n` is a field exactly when `n` is prime" are proved from
basic facts, mirroring the lesson (`@provenance independent`). Some facts simply apply Mathlib
(`@provenance library`), and the monoid of functions under composition is built by hand
(`@provenance definition`) to show what a `Monoid` instance contains.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Lumenary.AlgebraicStructures

/-! ### Identities and inverses are unique -/

-- @region algebraic_structures.identity_unique
-- @provenance independent
/-- **An identity element is unique.** If `e` and `e'` are both two-sided identities for a
binary operation `op` on `S`, then `e = e'`. The proof is one line on paper: compute `op e e'`
in two ways — it is `e` because `e'` is an identity, and `e'` because `e` is one. No
associativity is needed. -/
theorem identity_unique {S : Type*} (op : S → S → S) {e e' : S}
    (he : ∀ a, op e a = a ∧ op a e = a) (he' : ∀ a, op e' a = a ∧ op a e' = a) : e = e' :=
  calc e = op e e' := ((he' e).2).symm
    _ = e' := (he e').1
-- @endregion

-- @region algebraic_structures.inverse_unique
-- @provenance independent
/-- **Inverses are unique.** In a monoid, if `b` is a left inverse of `a` (`b * a = 1`) and `c`
is a right inverse (`a * c = 1`), then `b = c`. In particular an element has at most one
two-sided inverse. Each step of the `calc` is one monoid axiom; the key step is associativity. -/
theorem inverse_unique {M : Type*} [Monoid M] {a b c : M} (hb : b * a = 1) (hc : a * c = 1) :
    b = c :=
  calc b = b * 1 := (mul_one b).symm
    _ = b * (a * c) := by rw [hc]
    _ = (b * a) * c := (mul_assoc b a c).symm
    _ = 1 * c := by rw [hb]
    _ = c := one_mul c
-- @endregion

-- @region algebraic_structures.inverse_unique_library
-- @provenance library
/-- The same fact, from Mathlib: `left_inv_eq_right_inv`. -/
theorem inverse_unique_library {M : Type*} [Monoid M] {a b c : M} (hb : b * a = 1)
    (hc : a * c = 1) : b = c :=
  left_inv_eq_right_inv hb hc
-- @endregion

/-! ### Examples and non-examples -/

-- @region algebraic_structures.nat_add_not_group
-- @provenance independent
/-- **`(ℕ, +)` is a monoid but not a group.** Not every natural number has an additive inverse:
there is no `b : ℕ` with `1 + b = 0`. (`omega` decides this linear fact about naturals.) -/
theorem nat_add_not_group : ¬ ∀ a : ℕ, ∃ b : ℕ, a + b = 0 := by
  intro h
  obtain ⟨b, hb⟩ := h 1
  omega
-- @endregion

-- @region algebraic_structures.odd_not_closed
-- @provenance independent
/-- **Closure can fail.** Addition is not a binary operation on the odd integers: `1` and `1`
are odd but `1 + 1 = 2` is not. -/
theorem odd_not_closed : ¬ ∀ a b : ℤ, Odd a → Odd b → Odd (a + b) := by
  intro h
  have h2 : Odd ((1 : ℤ) + 1) := h 1 1 odd_one odd_one
  rw [Int.odd_iff] at h2
  norm_num at h2
-- @endregion

-- @region algebraic_structures.endo_monoid
-- @provenance definition
/-- **The functions from a set to itself form a monoid under composition.** The product
`f * g` is `f ∘ g` ("`f` after `g`") and the identity element is the identity function `id` —
not `0` or `1`. All three axioms hold by `rfl`: composition is associative and `id` is neutral
*by definition*. (Mathlib's version is `Function.End α`.) -/
@[instance_reducible]
def endoMonoid (α : Type*) : Monoid (α → α) where
  mul f g := f ∘ g
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
-- @endregion

-- @region algebraic_structures.perm_not_comm
-- @provenance independent
/-- **The symmetric group `S₃` is not commutative.** The bijections of `{0, 1, 2}` form a group
under composition (`Equiv.Perm (Fin 3)`, with `σ * τ = σ ∘ τ`), and the two transpositions
`(0 1)` and `(1 2)` do not commute. `decide` checks the finite computation. -/
theorem perm_not_comm :
    ∃ σ τ : Equiv.Perm (Fin 3), σ * τ ≠ τ * σ :=
  ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
-- @endregion

-- @region algebraic_structures.matrix_zero_divisors
-- @provenance independent
/-- **A non-commutative ring with zero divisors.** The `2 × 2` integer matrices form a ring in
which two non-zero matrices can multiply to `0`, and in which the order of multiplication
matters. Here `A = !![0, 1; 0, 0]` and `B = !![1, 0; 0, 0]`: `A * B = 0` but `B * A = A ≠ 0`. -/
theorem matrix_zero_divisors :
    let A : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
    let B : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
    A ≠ 0 ∧ B ≠ 0 ∧ A * B = 0 ∧ B * A = A := by
  intro A B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [A] at this
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [B] at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_two]
-- @endregion

/-! ### Rings and fields -/

-- @region algebraic_structures.int_not_field
-- @provenance independent
/-- **`ℤ` is a ring but not a field:** `2 ≠ 0` has no multiplicative inverse in `ℤ`.
(`IsField R` is Mathlib's proposition "`R` is a field": `0 ≠ 1`, commutativity, and inverses
for non-zero elements.) The final step, "no integer `b` has `2b = 1`", is decided by `omega`. -/
theorem int_not_field : ¬ IsField ℤ := by
  intro h
  obtain ⟨b, hb⟩ := h.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
  omega
-- @endregion

-- @region algebraic_structures.rat_field
-- @provenance library
/-- **`ℚ` is a field.** Mathlib's `Field ℚ` instance (inverse `(a/b)⁻¹ = b/a`), turned into the
proposition `IsField ℚ` by `Field.toIsField`. -/
theorem rat_field : IsField ℚ := Field.toIsField ℚ
-- @endregion

-- @region algebraic_structures.zmod_is_field_iff
-- @provenance independent
/-- **`ℤ/nℤ` is a field if and only if `n` is prime.**
* If `n = p` is prime, Mathlib's instance `Field (ZMod p)` applies (it finds inverses with
  Bézout's identity).
* If `n = 0`, `ZMod 0` is `ℤ`, which is not a field; if `n = 1`, `ZMod 1` has only one
  element, and a field needs `0 ≠ 1`.
* If `n = m * b` with `2 ≤ m < n`, then `m` and `b` are non-zero in `ZMod n` but `m * b = 0`.
  If `m` had an inverse `c`, then `b = (c * m) * b = c * (m * b) = 0`, a contradiction. -/
theorem zmod_isField_iff (n : ℕ) : IsField (ZMod n) ↔ n.Prime := by
  constructor
  · intro h
    by_contra hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exact Int.not_isField h
      · exact not_isField_of_subsingleton (ZMod 1) h
    · simp only [Nat.prime_def_lt', not_and, not_forall, not_not] at hn
      obtain ⟨m, hm2, hmn, hdvd⟩ := hn hge
      obtain ⟨b, rfl⟩ := hdvd
      have hb1 : 1 < b := by
        by_contra hb
        interval_cases b <;> omega
      have hm0 : (m : ZMod (m * b)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      have hb0 : (b : ZMod (m * b)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        nlinarith
      have hprod : (m : ZMod (m * b)) * (b : ZMod (m * b)) = 0 := by
        rw [← Nat.cast_mul, ZMod.natCast_self]
      obtain ⟨c, hc⟩ := h.mul_inv_cancel hm0
      apply hb0
      calc (b : ZMod (m * b)) = (m * c) * b := by rw [hc, one_mul]
        _ = c * (m * b) := by ring
        _ = 0 := by rw [hprod, mul_zero]
  · intro hp
    have : Fact n.Prime := ⟨hp⟩
    exact Field.toIsField (ZMod n)
-- @endregion

/-! ### Homomorphisms -/

-- @region algebraic_structures.hom_map_one
-- @provenance independent
/-- **Between groups, preserving multiplication forces preserving the identity.** If
`f (a * b) = f a * f b` for all `a, b`, then `f 1 * f 1 = f (1 * 1) = f 1 = f 1 * 1`, and
cancelling `f 1` (possible in a group) leaves `f 1 = 1`. -/
theorem hom_map_one {G H : Type*} [Group G] [Group H] (f : G → H)
    (hf : ∀ a b, f (a * b) = f a * f b) : f 1 = 1 := by
  have h : f 1 * f 1 = f 1 * 1 :=
    calc f 1 * f 1 = f (1 * 1) := (hf 1 1).symm
      _ = f 1 := by rw [one_mul]
      _ = f 1 * 1 := (mul_one (f 1)).symm
  exact mul_left_cancel h
-- @endregion

-- @region algebraic_structures.hom_map_inv
-- @provenance independent
/-- **Group homomorphisms preserve inverses.** `f a⁻¹ * f a = f (a⁻¹ * a) = f 1 = 1`, and
likewise `f a * f a⁻¹ = 1`; by the uniqueness of inverses (`inverse_unique`), `f a⁻¹` must be
*the* inverse `(f a)⁻¹`. Mathlib's version is `map_inv`. -/
theorem hom_map_inv {G H : Type*} [Group G] [Group H] (f : G → H)
    (hf : ∀ a b, f (a * b) = f a * f b) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  have h1 : f a⁻¹ * f a = 1 := by rw [← hf, inv_mul_cancel, hom_map_one f hf]
  have h2 : f a * (f a)⁻¹ = 1 := mul_inv_cancel (f a)
  exact inverse_unique h1 h2
-- @endregion

-- @region algebraic_structures.mul_hom_not_one
-- @provenance independent
/-- **For monoids, preserving `1` must be required separately.** The zero map on `(ℤ, ×)`
preserves products (`0 = 0 * 0`) but sends `1` to `0 ≠ 1`. Cancellation, which made
`hom_map_one` work for groups, is not available in the monoid `(ℤ, ×)` (one cannot cancel `0`). -/
theorem mul_hom_not_one : ∃ f : ℤ → ℤ, (∀ a b, f (a * b) = f a * f b) ∧ f 1 ≠ 1 :=
  ⟨fun _ => 0, fun _ _ => by simp, by simp⟩
-- @endregion

-- @region algebraic_structures.reduce_mod
-- @provenance definition
/-- **Reduction modulo `n` is a ring homomorphism** `ℤ →+* ℤ/nℤ`: it preserves `+`, `×`, `0`
and `1`. This is Mathlib's `Int.castRingHom`, given a lesson name. -/
def reduceMod (n : ℕ) : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
-- @endregion

-- @region algebraic_structures.reduce_mod_eq_zero_iff
-- @provenance library
/-- The **kernel** of reduction mod `n` is the set of multiples of `n`: `a ↦ 0` exactly when
`n ∣ a`. This applies Mathlib's `ZMod.intCast_zmod_eq_zero_iff_dvd`. -/
theorem reduceMod_eq_zero_iff (n : ℕ) (a : ℤ) : reduceMod n a = 0 ↔ (n : ℤ) ∣ a :=
  ZMod.intCast_zmod_eq_zero_iff_dvd a n
-- @endregion

end Lumenary.AlgebraicStructures
