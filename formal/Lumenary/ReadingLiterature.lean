/-
The Lumenary — formal mathematics
Reading the mathematical literature: reconstructing a published proof, step by step.

Zagier's "one-sentence proof" (American Mathematical Monthly, 1990) that every prime `p ≡ 1
(mod 4)` is a sum of two squares states its argument in a single sentence and leaves every
verification to the reader. This module reconstructs all the omitted steps and checks them:
the set `S = {(x, y, z) ∈ ℕ³ : x² + 4yz = p}` is finite; the boundary cases of Zagier's
piecewise map never occur when `p` is prime; the map sends `S` to `S` and is an involution;
its only fixed point is `(1, 1, (p - 1)/4)`; an involution of a finite set has as many fixed
points as the set has elements, modulo 2 (Mathlib's `Equiv.Perm.card_fixedPoints_modEq`, the
one cited ingredient); hence `|S|` is odd, the involution `(x, y, z) ↦ (x, z, y)` has a fixed
point, and `p = x² + (2y)²`. Everything is proved here (`independent`) except the parity
lemma and the library version of the theorem (`Nat.Prime.sq_add_sq`). Two small theorems about
conventions (division by zero, truncated subtraction) show why a reader must check a text's
conventions before its claims.
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Lumenary.ReadingLiterature

/-! ### The objects of Zagier's sentence -/

-- @region reading_literature.zagier_set
-- @provenance definition
/-- The finite set `S = {(x, y, z) : x² + 4yz = p}`, written as a filter of the box
`{0, …, p}³` so that its finiteness is evident. -/
def zagierSet (p : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (p + 1) ×ˢ Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
    fun t => t.1 ^ 2 + 4 * t.2.1 * t.2.2 = p
-- @endregion

-- @region reading_literature.zagier
-- @provenance definition
/-- Zagier's map, in his three cases:
`(x, y, z) ↦ (x + 2z, z, y - x - z)` if `x < y - z`;
`(2y - x, y, x - y + z)` if `y - z < x < 2y`; and `(x - 2y, x - y + z, y)` if `x > 2y`.
(The boundary cases `x = y - z` and `x = 2y` are assigned to the second and third branch;
they never occur for prime `p`.) -/
def zagier (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if t.1 + t.2.2 < t.2.1 then (t.1 + 2 * t.2.2, t.2.2, t.2.1 - t.1 - t.2.2)
  else if t.1 < 2 * t.2.1 then (2 * t.2.1 - t.1, t.2.1, t.1 + t.2.2 - t.2.1)
  else (t.1 - 2 * t.2.1, t.1 + t.2.2 - t.2.1, t.2.1)
-- @endregion

/-! ### Step 1: what membership in `S` implies when `p` is prime -/

-- @region reading_literature.mem_facts
-- @provenance independent
/-- **The omitted case analysis.** If `x² + 4yz = p` with `p` prime, then `x, y, z ≥ 1`, and
neither boundary case `x + z = y` nor `x = 2y` can occur: the first would make `p` a square,
`(x + 2z)²`, and the second would make `4 ∣ p`. This is where Zagier's sentence silently uses
that `p` is prime. -/
theorem mem_facts {p x y z : ℕ} (hp : p.Prime) (h : x ^ 2 + 4 * y * z = p) :
    1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x + z ≠ y ∧ x ≠ 2 * y := by
  have hp2 := hp.two_le
  -- `p` is not a perfect square
  have nsq : ∀ m : ℕ, m ^ 2 ≠ p := by
    intro m hm
    have hdvd : m ∣ p := ⟨m, by rw [← hm]; ring⟩
    rcases hp.eq_one_or_self_of_dvd m hdvd with h1 | h1
    · subst h1; omega
    · subst h1
      have : m * m = m * 1 := by rw [← sq, mul_one]; exact hm
      have hm0 : m ≠ 0 := by omega
      have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) this
      omega
  -- `4` does not divide `p`
  have n4 : ¬ 4 ∣ p := by
    intro h4
    have h2 : 2 ∣ p := Nat.dvd_trans ⟨2, rfl⟩ h4
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h1
    · omega
    · rw [← h1] at h4; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra hx
    have hx0 : x = 0 := by omega
    subst hx0
    exact n4 ⟨y * z, by rw [← h]; ring⟩
  · by_contra hy
    have hy0 : y = 0 := by omega
    subst hy0
    exact nsq x (by simpa using h)
  · by_contra hz
    have hz0 : z = 0 := by omega
    subst hz0
    exact nsq x (by simpa using h)
  · intro hxy
    subst hxy
    exact nsq (x + 2 * z) (by rw [← h]; ring)
  · intro hx
    subst hx
    exact n4 ⟨y * y + y * z, by rw [← h]; ring⟩
-- @endregion

-- @region reading_literature.mem_zagier_set
-- @provenance independent
/-- For prime `p`, membership in `S` is just the equation: the box bounds are automatic. -/
theorem mem_zagierSet {p : ℕ} (hp : p.Prime) (t : ℕ × ℕ × ℕ) :
    t ∈ zagierSet p ↔ t.1 ^ 2 + 4 * t.2.1 * t.2.2 = p := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    obtain ⟨hx, hy, hz, -, -⟩ := mem_facts hp h
    simp only [zagierSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨?_, ?_, ?_⟩, h⟩
    · nlinarith
    · nlinarith
    · nlinarith
-- @endregion

/-! ### Step 2: the map sends `S` to `S` and is an involution -/

-- @region reading_literature.zagier_of_lt
-- @provenance independent
/-- Zagier's map in its first case, `x + z < y`. -/
theorem zagier_of_lt {x y z : ℕ} (h : x + z < y) :
    zagier (x, y, z) = (x + 2 * z, z, y - x - z) := by
  simp [zagier, h]
-- @endregion

-- @region reading_literature.zagier_of_mid
-- @provenance independent
/-- Zagier's map in its second case, `y ≤ x + z` and `x < 2y`. -/
theorem zagier_of_mid {x y z : ℕ} (h1 : ¬ x + z < y) (h2 : x < 2 * y) :
    zagier (x, y, z) = (2 * y - x, y, x + z - y) := by
  simp [zagier, h1, h2]
-- @endregion

-- @region reading_literature.zagier_of_ge
-- @provenance independent
/-- Zagier's map in its third case, `y ≤ x + z` and `2y ≤ x`. -/
theorem zagier_of_ge {x y z : ℕ} (h1 : ¬ x + z < y) (h2 : ¬ x < 2 * y) :
    zagier (x, y, z) = (x - 2 * y, x + z - y, y) := by
  simp [zagier, h1, h2]
-- @endregion

-- @region reading_literature.zagier_mem
-- @provenance independent
/-- **The map preserves `x² + 4yz`.** In each case this is a polynomial identity, e.g.
`(x + 2z)² + 4z(y - x - z) = x² + 4yz`; the subtractions are legitimate by the case
conditions. -/
theorem zagier_mem {p : ℕ} (hp : p.Prime) {t : ℕ × ℕ × ℕ} (ht : t ∈ zagierSet p) :
    zagier t ∈ zagierSet p := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagierSet hp] at ht ⊢
  dsimp only at ht
  by_cases h1 : x + z < y
  · rw [zagier_of_lt h1]
    dsimp only
    obtain ⟨k, rfl⟩ : ∃ k, y = x + z + k := ⟨y - x - z, by omega⟩
    rw [show x + z + k - x - z = k by omega, ← ht]
    ring
  by_cases h2 : x < 2 * y
  · rw [zagier_of_mid h1 h2]
    dsimp only
    rw [← ht]
    zify [show x ≤ 2 * y by omega, show y ≤ x + z by omega]
    ring
  · rw [zagier_of_ge h1 h2]
    dsimp only
    rw [← ht]
    zify [show 2 * y ≤ x by omega, show y ≤ x + z by omega]
    ring
-- @endregion

-- @region reading_literature.zagier_zagier
-- @provenance independent
/-- **Zagier's map is an involution on `S`.** The first case is sent to the third, the third
to the first, and the second to itself; once the boundary cases are excluded (`mem_facts`),
each verification is linear arithmetic. -/
theorem zagier_zagier {p : ℕ} (hp : p.Prime) {t : ℕ × ℕ × ℕ} (ht : t ∈ zagierSet p) :
    zagier (zagier t) = t := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagierSet hp] at ht
  dsimp only at ht
  obtain ⟨hx, hy, hz, hb1, hb2⟩ := mem_facts hp ht
  by_cases h1 : x + z < y
  · rw [zagier_of_lt h1, zagier_of_ge]
    · simp only [Prod.mk.injEq, and_true]; omega
    all_goals omega
  by_cases h2 : x < 2 * y
  · rw [zagier_of_mid h1 h2, zagier_of_mid]
    · simp only [Prod.mk.injEq, true_and]; omega
    all_goals omega
  · rw [zagier_of_ge h1 h2, zagier_of_lt]
    · simp only [Prod.mk.injEq, true_and]; omega
    omega
-- @endregion

/-! ### Step 3: the unique fixed point -/

-- @region reading_literature.zagier_fixed_iff
-- @provenance independent
/-- **The fixed points.** A point of `S` is fixed by Zagier's map iff it is `(1, 1, k)` where
`p = 4k + 1`. (In the first and third cases a fixed point would need `z = 0` or `y = 0`; in the
second it needs `x = y`, so `p = x(x + 4z)`, and primality forces `x = 1`.) -/
theorem zagier_fixed_iff {p : ℕ} (hp : p.Prime) {t : ℕ × ℕ × ℕ} (ht : t ∈ zagierSet p) :
    zagier t = t ↔ t = (1, 1, p / 4) := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagierSet hp] at ht
  dsimp only at ht
  obtain ⟨hx, hy, hz, hb1, hb2⟩ := mem_facts hp ht
  constructor
  · intro hfix
    by_cases h1 : x + z < y
    · rw [zagier_of_lt h1] at hfix
      simp only [Prod.mk.injEq] at hfix; omega
    by_cases h2 : x < 2 * y
    · rw [zagier_of_mid h1 h2] at hfix
      simp only [Prod.mk.injEq] at hfix
      have hxy : x = y := by omega
      subst hxy
      have hdvd : x ∣ p := ⟨x + 4 * z, by rw [← ht]; ring⟩
      rcases hp.eq_one_or_self_of_dvd x hdvd with h1' | h1'
      · subst h1'
        simp only [Prod.mk.injEq, true_and]
        omega
      · -- `x = p` is impossible: then `p² ≤ x² + 4xz = p`
        have hle : p * p ≤ p := by
          calc p * p = x ^ 2 := by rw [h1']; ring
            _ ≤ x ^ 2 + 4 * x * z := Nat.le_add_right _ _
            _ = p := ht
        have := hp.two_le
        nlinarith
    · rw [zagier_of_ge h1 h2] at hfix
      simp only [Prod.mk.injEq] at hfix; omega
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [zagier_of_mid]
    · simp only [Prod.mk.injEq, true_and]; omega
    all_goals omega
-- @endregion

/-! ### Step 4: parity, twice -/

-- @region reading_literature.card_odd
-- @provenance independent
/-- **`|S|` is odd** when `p ≡ 1 (mod 4)`: Zagier's map is an involution of the finite set `S`
with exactly one fixed point, and the number of fixed points of an involution of a finite set
has the same parity as the set (`Equiv.Perm.card_fixedPoints_modEq` with `2¹`). -/
theorem card_odd {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    Fintype.card (zagierSet p) % 2 = 1 := by
  let f : Function.End (zagierSet p) := fun t => ⟨zagier t.1, zagier_mem hp t.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext t
    exact Subtype.ext (zagier_zagier hp t.2)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have t0mem : ((1, 1, p / 4) : ℕ × ℕ × ℕ) ∈ zagierSet p := by
    rw [mem_zagierSet hp]
    show 1 ^ 2 + 4 * 1 * (p / 4) = p
    norm_num
    omega
  have hone : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨_, t0mem⟩, ?_⟩, ?_⟩
    · exact Subtype.ext ((zagier_fixed_iff hp t0mem).2 rfl)
    · rintro ⟨⟨t, htm⟩, hfix⟩
      have h' : zagier t = t := congrArg Subtype.val hfix
      exact Subtype.ext (Subtype.ext ((zagier_fixed_iff hp htm).1 h'))
  rw [hone] at hmod
  exact hmod
-- @endregion

-- @region reading_literature.zagier_two_squares
-- @provenance independent
/-- **Fermat's two-squares theorem, by Zagier's proof, with every step reconstructed.** If `p` is
prime and `p ≡ 1 (mod 4)`, then `p = a² + b²`. Since `|S|` is odd, the involution
`(x, y, z) ↦ (x, z, y)` of `S` also has a fixed point `(x, y, y)`, and then
`p = x² + 4y² = x² + (2y)²`. -/
theorem zagier_two_squares {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have swap_mem : ∀ t ∈ zagierSet p, ((t.1, t.2.2, t.2.1) : ℕ × ℕ × ℕ) ∈ zagierSet p := by
    intro t ht
    rw [mem_zagierSet hp] at ht ⊢
    simp only
    rw [← ht]; ring
  let g : Function.End (zagierSet p) := fun t => ⟨(t.1.1, t.1.2.2, t.1.2.1), swap_mem _ t.2⟩
  have hg : g ^ 2 ^ 1 = 1 := by
    funext t
    exact Subtype.ext rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hg
  have hodd := card_odd hp h4
  have hpos : 0 < Fintype.card (Function.fixedPoints g) := by
    have : Fintype.card (Function.fixedPoints g) % 2 = 1 := by
      rw [← hodd]; exact hmod.symm
    omega
  obtain ⟨⟨⟨⟨x, y, z⟩, hmem⟩, hfix⟩⟩ := Fintype.card_pos_iff.1 hpos
  have hyz : z = y := by
    have := congrArg (fun t => t.1.2.1) hfix
    simpa [g] using this
  rw [mem_zagierSet hp] at hmem
  simp only at hmem
  subst hyz
  exact ⟨x, 2 * z, by rw [← hmem]; ring⟩
-- @endregion

-- @region reading_literature.sq_add_sq_library
-- @provenance library
/-- The same theorem as it appears in Mathlib (`Nat.Prime.sq_add_sq`), proved there through the
Gaussian integers — a different proof from a different literature. Note its hypothesis
`p % 4 ≠ 3`, which also covers `p = 2 = 1² + 1²`: the same theorem can be stated in slightly
different, non-equivalent ways, and a careful reader checks which one a source proves. -/
theorem sq_add_sq_library {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hp
-- @endregion

/-! ### Conventions matter -/

-- @region reading_literature.div_mul_cancel_needs_hypothesis
-- @provenance independent
/-- In Lean (as in much of the formal literature) `a / 0 = 0`, so the "identity"
`(a / b) · b = a` is false without the hypothesis `b ≠ 0`, which informal texts often leave
implicit. Counterexample: `a = 1, b = 0`. -/
theorem div_mul_cancel_needs_hypothesis : ¬ ∀ a b : ℚ, a / b * b = a := by
  intro h
  have := h 1 0
  norm_num at this
-- @endregion

-- @region reading_literature.nat_sub_add_needs_hypothesis
-- @provenance independent
/-- Subtraction of natural numbers is truncated (`3 - 5 = 0`), so `(a - b) + b = a` needs
`b ≤ a`. A text that works in `ℕ` and one that works in `ℤ` may write the same formula and mean
different things. -/
theorem nat_sub_add_needs_hypothesis : ¬ ∀ a b : ℕ, a - b + b = a := by
  intro h
  have := h 3 5
  omega
-- @endregion

end Lumenary.ReadingLiterature
