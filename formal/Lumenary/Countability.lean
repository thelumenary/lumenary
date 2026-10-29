/-
The Lumenary — formal mathematics
Countability and Cantor's diagonal argument: comparing infinite sets by bijections.

Proved here (`@provenance independent`): the even numbers are in bijection with `ℕ`; the zigzag
`0, −1, 1, −2, 2, …` is a bijection `ℕ → ℤ`; Cantor's pairing function
`π(m, n) = (0 + 1 + ⋯ + (m + n)) + n` is a bijection `ℕ × ℕ → ℕ`; Cantor's theorem (no surjection
from a set onto its power set); the diagonal argument for infinite 0–1 sequences and for decimal
digit sequences; and the existence of transcendental numbers, deduced Cantor's way from
countability (algebraic numbers) and uncountability (real numbers).

From Mathlib (`@provenance library`): `Countable ℚ` (via Mathlib's `Denumerable ℚ`),
`Function.cantor_surjective`, `Cardinal.not_countable_real`, `Set.countable_iUnion`, and
`Algebraic.countable`. Not formalised here: the step "two different decimal expansions, neither
ending in repeating 9s, name different real numbers", which the lesson proves by hand; the
uncountability of `ℝ` itself is cited from Mathlib, where it is proved via `#ℝ = 2 ^ ℵ₀`.
-/
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Countable

namespace Lumenary.Countability

open Function Finset

/-! ### A proper subset of the same size -/

-- @region countability.doubling
-- @provenance definition
/-- The bijection `n ↦ 2n` between `ℕ` and the even numbers, with inverse `m ↦ m / 2`. -/
def doubling : ℕ ≃ {m : ℕ // Even m} where
  toFun n := ⟨2 * n, even_two_mul n⟩
  invFun m := m.1 / 2
  left_inv n := by simp
  right_inv m := by
    obtain ⟨m, k, hk⟩ := m
    apply Subtype.ext
    simp only
    omega
-- @endregion

/-! ### The integers are countable -/

-- @region countability.zigzag
-- @provenance definition
/-- The zigzag enumeration of the integers: `0, −1, 1, −2, 2, −3, …`.
Even `n` goes to `n / 2`; odd `n` goes to `−(n + 1) / 2`. -/
def zigzag (n : ℕ) : ℤ :=
  if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) - 1
-- @endregion

-- @region countability.zigzag_bijective
-- @provenance independent
/-- **ℤ is countable**: the zigzag is a bijection `ℕ → ℤ`.
*Injective:* even inputs give values `≥ 0`, odd inputs give values `< 0`, and on each kind the
formula is one-to-one. *Surjective:* `z ≥ 0` is hit by `2z`, and `z < 0` by `−2z − 1`. -/
theorem zigzag_bijective : Bijective zigzag := by
  constructor
  · intro a b h
    unfold zigzag at h
    split_ifs at h <;> omega
  · intro z
    rcases le_or_gt 0 z with hz | hz
    · refine ⟨2 * z.toNat, ?_⟩
      unfold zigzag
      split_ifs <;> omega
    · refine ⟨(-2 * z - 1).toNat, ?_⟩
      unfold zigzag
      split_ifs <;> omega
-- @endregion

-- @region countability.rat_countable
-- @provenance library
/-- **ℚ is countable**: Mathlib's instance, which encodes a fraction in lowest terms by its
numerator and denominator (`Rat.instDenumerable`). -/
theorem rat_countable : Countable ℚ := inferInstance
-- @endregion

/-! ### Cantor's pairing function: `ℕ × ℕ` is countable -/

-- @region countability.tri
-- @provenance definition
/-- The triangular number `tri d = 0 + 1 + ⋯ + d = d(d + 1)/2`: the number of points on the
diagonals `0, 1, …, d − 1` of the grid `ℕ × ℕ` (diagonal `j` has `j + 1` points). -/
def tri (d : ℕ) : ℕ := ∑ i ∈ range (d + 1), i
-- @endregion

-- @region countability.cantor_pair
-- @provenance definition
/-- **Cantor's pairing function** `π(m, n) = tri (m + n) + n`: walk the grid diagonal by
diagonal; the point `(m, n)` lies on diagonal `m + n`, and is the `n`-th point along it. -/
def cantorPair (m n : ℕ) : ℕ := tri (m + n) + n
-- @endregion

-- @region countability.tri_succ
-- @provenance library
/-- Moving to the next diagonal adds `d + 1` points: `tri (d + 1) = tri d + (d + 1)`.
This is Mathlib's `Finset.sum_range_succ`. -/
theorem tri_succ (d : ℕ) : tri (d + 1) = tri d + (d + 1) := sum_range_succ _ _
-- @endregion

-- @region countability.tri_mono
-- @provenance independent
/-- Triangular numbers increase: `tri a ≤ tri (a + k)`. -/
theorem tri_mono (a k : ℕ) : tri a ≤ tri (a + k) := by
  induction k with
  | zero => exact le_refl _
  | succ k ih => rw [← Nat.add_assoc, tri_succ]; omega
-- @endregion

-- @region countability.cantor_pair_injective
-- @provenance independent
/-- **Cantor's pairing is injective.** The values on diagonal `d` are `tri d, …, tri d + d`, all
less than `tri (d + 1)`, where the next diagonal starts. So equal values force equal diagonals
`m + n = m' + n'`, then equal positions `n = n'`, then `m = m'`. -/
theorem cantorPair_injective {m n m' n' : ℕ} (h : cantorPair m n = cantorPair m' n') :
    m = m' ∧ n = n' := by
  unfold cantorPair at h
  have key : ∀ {d d' n : ℕ}, d < d' → n ≤ d → tri d + n < tri d' := by
    intro d d' n hlt hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 := tri_mono (d + 1) k
    rw [Nat.add_right_comm] at h1
    have h2 := tri_succ d
    omega
  rcases lt_trichotomy (m + n) (m' + n') with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (lt_of_lt_of_le (key hlt (by omega)) (by omega)))
  · rw [heq] at h
    omega
  · exact absurd h (Nat.ne_of_gt (lt_of_lt_of_le (key hgt (by omega)) (by omega)))
-- @endregion

-- @region countability.cantor_pair_surjective
-- @provenance independent
/-- **Cantor's pairing is surjective**, by induction on the value `k`: if `π(m, n) = k`, the next
value `k + 1` is the next point of the walk — one step up the same diagonal, `(m − 1, n + 1)`, or,
at the end of a diagonal (`m = 0`), the first point `(n + 1, 0)` of the next one. -/
theorem cantorPair_surjective (k : ℕ) : ∃ m n, cantorPair m n = k := by
  induction k with
  | zero => exact ⟨0, 0, rfl⟩
  | succ k ih =>
    obtain ⟨m, n, h⟩ := ih
    unfold cantorPair at h
    cases m with
    | zero =>
      refine ⟨n + 1, 0, ?_⟩
      unfold cantorPair
      rw [Nat.add_zero, tri_succ]
      rw [Nat.zero_add] at h
      omega
    | succ m =>
      refine ⟨m, n + 1, ?_⟩
      unfold cantorPair
      rw [show m + (n + 1) = m + 1 + n by omega]
      omega
-- @endregion

-- @region countability.nat_prod_equiv
-- @provenance independent
/-- Hence **`ℕ × ℕ` has the same cardinality as `ℕ`**: Cantor's pairing is a bijection.
(Mathlib has a different pairing function with the same property, `Nat.pairEquiv`.) -/
theorem nat_prod_equiv : Nonempty (ℕ × ℕ ≃ ℕ) := by
  refine ⟨Equiv.ofBijective (fun p => cantorPair p.1 p.2) ⟨?_, ?_⟩⟩
  · intro p q h
    obtain ⟨h1, h2⟩ := cantorPair_injective h
    exact Prod.ext h1 h2
  · intro k
    obtain ⟨m, n, h⟩ := cantorPair_surjective k
    exact ⟨(m, n), h⟩
-- @endregion

-- @region countability.countable_union
-- @provenance library
/-- **A countable union of countable sets is countable** (Mathlib's `Set.countable_iUnion`; its
proof uses the axiom of choice, which is part of Lean's logic, to pick an enumeration of each
set). -/
theorem countable_union {ι α : Type*} [Countable ι] (t : ι → Set α) (h : ∀ i, (t i).Countable) :
    (⋃ i, t i).Countable :=
  Set.countable_iUnion h
-- @endregion

/-! ### Cantor's theorem and the diagonal argument -/

-- @region countability.cantor
-- @provenance independent
/-- **Cantor's theorem**: no function `f : A → 𝒫(A)` is surjective. The *diagonal set*
`D = {a | a ∉ f a}` is missed: if `f a = D`, then `a ∈ D ↔ a ∉ f a ↔ a ∉ D`, which is impossible. -/
theorem cantor {α : Type*} (f : α → Set α) : ¬ Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf {x | x ∉ f x}
  have h : a ∈ f a ↔ a ∉ f a := by
    constructor
    · intro hin
      rw [ha] at hin
      exact hin
    · intro hout
      rw [ha]
      exact hout
  by_cases hin : a ∈ f a
  · exact h.mp hin hin
  · exact hin (h.mpr hin)
-- @endregion

-- @region countability.cantor_library
-- @provenance library
/-- Cantor's theorem from Mathlib: `Function.cantor_surjective`. -/
theorem cantor_library {α : Type*} (f : α → Set α) : ¬ Surjective f :=
  cantor_surjective f
-- @endregion

-- @region countability.diagonal
-- @provenance definition
/-- The **diagonal sequence** of a list `s₀, s₁, s₂, …` of infinite 0–1 sequences: its `n`-th
entry is the opposite of the `n`-th entry of `sₙ`. -/
def diagonal (s : ℕ → ℕ → Bool) : ℕ → Bool := fun n => !(s n n)
-- @endregion

-- @region countability.diagonal_ne
-- @provenance independent
/-- The diagonal sequence differs from the `n`-th sequence of the list — at position `n`. -/
theorem diagonal_ne (s : ℕ → ℕ → Bool) (n : ℕ) : diagonal s ≠ s n := by
  intro h
  have hn : diagonal s n = s n n := congrFun h n
  unfold diagonal at hn
  cases hs : s n n <;> simp [hs] at hn
-- @endregion

-- @region countability.sequences_uncountable
-- @provenance independent
/-- **The infinite 0–1 sequences cannot be listed**: no `s : ℕ → (ℕ → Bool)` is surjective,
because the diagonal sequence is never on the list. -/
theorem sequences_uncountable : ¬ ∃ s : ℕ → (ℕ → Bool), Surjective s := by
  rintro ⟨s, hs⟩
  obtain ⟨n, hn⟩ := hs (diagonal s)
  exact diagonal_ne s n hn.symm
-- @endregion

-- @region countability.decimal_diagonal
-- @provenance definition
/-- The careful **decimal diagonal**: from a list of digit sequences `rₙ = 0.rₙ₀ rₙ₁ rₙ₂…`, take
digit `5` in position `n` unless `rₙ` has a `5` there, in which case take `4`. -/
def decimalDiagonal (r : ℕ → ℕ → Fin 10) : ℕ → Fin 10 := fun n => if r n n = 5 then 4 else 5
-- @endregion

-- @region countability.decimal_diagonal_spec
-- @provenance independent
/-- The decimal diagonal (1) differs from the `n`-th expansion in the `n`-th digit, and (2) uses
only the digits `4` and `5` — never `0` or `9` — so it is the *only* decimal expansion of the
number it names (no `…4999…`/`…5000…` ambiguity). -/
theorem decimalDiagonal_spec (r : ℕ → ℕ → Fin 10) (n : ℕ) :
    decimalDiagonal r n ≠ r n n ∧ (decimalDiagonal r n = 4 ∨ decimalDiagonal r n = 5) := by
  unfold decimalDiagonal
  split_ifs with h
  · rw [h]
    exact ⟨by decide, Or.inl rfl⟩
  · exact ⟨fun h' => h h'.symm, Or.inr rfl⟩
-- @endregion

-- @region countability.real_uncountable
-- @provenance library
/-- **ℝ is uncountable**: Mathlib's `Cardinal.not_countable_real`. -/
theorem real_uncountable : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
-- @endregion

-- @region countability.exists_transcendental
-- @provenance independent
/-- **Transcendental numbers exist** — Cantor's 1874 argument. The real numbers that are roots of
non-zero integer polynomials (the algebraic numbers) form a countable set (`Algebraic.countable`),
but `ℝ` is uncountable, so some real number is not algebraic. The proof names no such number. -/
theorem exists_transcendental : ∃ x : ℝ, Transcendental ℤ x := by
  by_contra h
  push Not at h
  apply real_uncountable
  apply (Algebraic.countable ℤ ℝ).mono
  intro x _
  have hx := h x
  unfold Transcendental at hx
  exact not_not.mp hx
-- @endregion

end Lumenary.Countability
