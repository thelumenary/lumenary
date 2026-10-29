/-
The Lumenary — formal mathematics
Formalising published mathematics: a worked example. Don Zagier's paper "A one-sentence proof
that every prime p ≡ 1 (mod 4) is a sum of two squares" (American Mathematical Monthly 97, 1990,
p. 144) consists of one sentence:

  "The involution on the finite set S = {(x, y, z) ∈ ℕ³ : x² + 4yz = p} defined by
     (x, y, z) ↦ (x + 2z, z, y − x − z)   if x < y − z,
                 (2y − x, y, x − y + z)   if y − z < x < 2y,
                 (x − 2y, x − y + z, y)   if x > 2y
   has exactly one fixed point, so |S| is odd and the involution defined by
   (x, y, z) ↦ (x, z, y) also has a fixed point."

What is formalised. The whole argument, split into the lemmas of the lesson's blueprint: `S` is
finite (as a `Finset` cut out of a box), the facts about elements of `S` that the sentence uses
silently (all coordinates positive, the boundary cases `x = y − z` and `x = 2y` never occur — this
is where primality enters), the piecewise map sends `S` to `S` and is an involution, its only fixed
point is `(1, 1, k)`, an involution of a finite set has as many fixed points as elements modulo 2
(proved here by induction), and hence the swap `(x, y, z) ↦ (x, z, y)` has a fixed point, giving
`p = x² + (2y)²`. We also compare our statement with Mathlib's `Nat.Prime.sq_add_sq` (proved there
by a different route, through the Gaussian integers) and show that primality cannot be dropped.
Mathlib's `Archive/ZagierTwoSquares.lean` (Jeremy Tan and Thomas Browning, 2023) contains another
formalisation of the same proof; this one was written independently, in a different style.
-/
import Mathlib.NumberTheory.SumTwoSquares

namespace Lumenary.FormalisingPublishedMathematics

open Finset

/-! ### Blueprint 1: the set `S` and the facts the sentence uses silently -/

-- @region formalising_published_mathematics.zagier_set
-- @provenance definition
/-- Zagier's set `S = {(x, y, z) ∈ ℕ³ : x² + 4yz = p}` for `p = 4k + 1`. The paper calls `S` "the
finite set" without comment; to make finiteness explicit we define `S` as a `Finset`, filtering
the box `{0, …, p}³`, and prove in `mem_zagierSet` that the box cuts nothing off. -/
def zagierSet (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (4 * k + 2)) ×ˢ (range (4 * k + 2)) ×ˢ (range (4 * k + 2))).filter
    (fun t => t.1 ^ 2 + 4 * t.2.1 * t.2.2 = 4 * k + 1)
-- @endregion

-- @region formalising_published_mathematics.zagier_facts
-- @provenance independent
/-- The facts that Zagier's sentence uses without stating them. If `p = 4k + 1` is prime and
`x² + 4yz = p`, then `x, y, z > 0`, and neither boundary case occurs: `x + z ≠ y` (otherwise
`p = (x + 2z)²` would be a square) and `x ≠ 2y` (otherwise `p = 4y(y + z)` would be even). -/
theorem zagier_facts {k x y z : ℕ} (hp : (4 * k + 1).Prime) (h : x ^ 2 + 4 * y * z = 4 * k + 1) :
    0 < x ∧ 0 < y ∧ 0 < z ∧ x + z ≠ y ∧ x ≠ 2 * y := by
  -- A prime is never a perfect square.
  have not_square : ∀ m : ℕ, m * m ≠ 4 * k + 1 := by
    intro m hm
    rw [← hm] at hp
    rcases Nat.prime_mul_iff.1 hp with ⟨hm1, rfl⟩ | ⟨hm1, rfl⟩ <;> exact Nat.not_prime_one hm1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `x = 0` would make `p = 4yz` divisible by 4.
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · have : 4 * (y * z) = 4 * k + 1 := by rw [← h]; ring
      omega
    · exact hx
  · rcases Nat.eq_zero_or_pos y with rfl | hy
    · exact absurd (by rw [← h]; ring) (not_square x)
    · exact hy
  · rcases Nat.eq_zero_or_pos z with rfl | hz
    · exact absurd (by rw [← h]; ring) (not_square x)
    · exact hz
  · intro hb
    subst hb
    exact not_square (x + 2 * z) (by rw [← h]; ring)
  · intro hb
    subst hb
    have : 4 * (y * y + y * z) = 4 * k + 1 := by rw [← h]; ring
    omega
-- @endregion

-- @region formalising_published_mathematics.mem_zagier_set
-- @provenance independent
/-- For prime `p = 4k + 1`, a triple lies in `zagierSet k` exactly when `x² + 4yz = p`: every
solution already lies in the box `{0, …, p}³`, because `x ≤ x²`, `y ≤ 4yz` and `z ≤ 4yz`. -/
theorem mem_zagierSet {k : ℕ} (hp : (4 * k + 1).Prime) {t : ℕ × ℕ × ℕ} :
    t ∈ zagierSet k ↔ t.1 ^ 2 + 4 * t.2.1 * t.2.2 = 4 * k + 1 := by
  obtain ⟨x, y, z⟩ := t
  simp only [zagierSet, mem_filter, mem_product, mem_range, and_iff_right_iff_imp]
  intro h
  obtain ⟨hx, hy, hz, -, -⟩ := zagier_facts hp h
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith
-- @endregion

/-! ### Blueprint 2: the piecewise map and its three cases -/

-- @region formalising_published_mathematics.zagier_map
-- @provenance definition
/-- Zagier's piecewise map, transcribed with the conditions in the paper's order. In `ℕ`,
subtraction is truncated (`2 - 5 = 0`), so the condition `x < y − z` is written `x + z < y`, and
`x − y + z` is written `x + z − y`; on `S` these agree with the integer formulas. -/
def zagierMap : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | (x, y, z) =>
    if x + z < y then (x + 2 * z, z, y - x - z)
    else if x < 2 * y then (2 * y - x, y, x + z - y)
    else (x - 2 * y, x + z - y, y)
-- @endregion

-- @region formalising_published_mathematics.zagier_map_eq_one
-- @provenance independent
/-- Case 1 preserves `x² + 4yz`: if `x + z < y` then
`(x + 2z)² + 4z(y − x − z) = x² + 4yz`. -/
theorem zagierMap_eq_one {x y z : ℕ} (h : x + z < y) :
    (x + 2 * z) ^ 2 + 4 * z * (y - x - z) = x ^ 2 + 4 * y * z := by
  obtain ⟨d, rfl⟩ : ∃ d, y = x + z + d := ⟨y - (x + z), by omega⟩
  rw [show x + z + d - x - z = d by omega]
  ring
-- @endregion

-- @region formalising_published_mathematics.zagier_map_eq_two
-- @provenance independent
/-- Case 2 preserves `x² + 4yz`: if `y ≤ x + z` and `x ≤ 2y` then
`(2y − x)² + 4y(x + z − y) = x² + 4yz`. Proved by passing to `ℤ`, where subtraction is honest. -/
theorem zagierMap_eq_two {x y z : ℕ} (h₁ : y ≤ x + z) (h₂ : x ≤ 2 * y) :
    (2 * y - x) ^ 2 + 4 * y * (x + z - y) = x ^ 2 + 4 * y * z := by
  zify [h₁, h₂]
  ring
-- @endregion

-- @region formalising_published_mathematics.zagier_map_eq_three
-- @provenance independent
/-- Case 3 preserves `x² + 4yz`: if `2y ≤ x` then `(x − 2y)² + 4(x + z − y)y = x² + 4yz`. -/
theorem zagierMap_eq_three {x y z : ℕ} (h : 2 * y ≤ x) :
    (x - 2 * y) ^ 2 + 4 * (x + z - y) * y = x ^ 2 + 4 * y * z := by
  have h' : y ≤ x + z := by omega
  zify [h, h']
  ring
-- @endregion

-- @region formalising_published_mathematics.zagier_map_maps_to
-- @provenance independent
/-- Zagier's map sends `S` into `S` (the word "on" in "the involution on the finite set `S`"). -/
theorem zagierMap_mapsTo {k : ℕ} (hp : (4 * k + 1).Prime) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ zagierSet k) : zagierMap t ∈ zagierSet k := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagierSet hp] at ht ⊢
  simp only at ht
  simp only [zagierMap]
  split_ifs with h₁ h₂
  · rw [← ht]; exact zagierMap_eq_one h₁
  · rw [← ht]; exact zagierMap_eq_two (by omega) h₂.le
  · rw [← ht]; exact zagierMap_eq_three (by omega)
-- @endregion

-- @region formalising_published_mathematics.zagier_map_involutive
-- @provenance independent
/-- Zagier's map is an involution on `S` ("easily checked" in the paper). Case 1 is sent to
case 3 and back, case 2 to itself. The proof uses `x, y, z > 0` and the absence of boundary
cases from `zagier_facts`; without them the map is not an involution. -/
theorem zagierMap_involutive {k : ℕ} (hp : (4 * k + 1).Prime) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ zagierSet k) : zagierMap (zagierMap t) = t := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagierSet hp] at ht
  simp only at ht
  obtain ⟨hx, hy, hz, hb₁, hb₂⟩ := zagier_facts hp ht
  by_cases h₁ : x + z < y
  · -- Case 1 lands in case 3.
    have e : zagierMap (x, y, z) = (x + 2 * z, z, y - x - z) := by simp [zagierMap, h₁]
    rw [e]
    simp only [zagierMap]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega
  · by_cases h₂ : x < 2 * y
    · -- Case 2 lands in case 2.
      have e : zagierMap (x, y, z) = (2 * y - x, y, x + z - y) := by simp [zagierMap, h₁, h₂]
      rw [e]
      simp only [zagierMap]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega
    · -- Case 3 lands in case 1.
      have e : zagierMap (x, y, z) = (x - 2 * y, x + z - y, y) := by simp [zagierMap, h₁, h₂]
      rw [e]
      simp only [zagierMap]
      rw [ite_eq_left (by omega)]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega
-- @endregion

/-! ### Blueprint 3: exactly one fixed point -/

-- @region formalising_published_mathematics.zagier_map_fixed_iff
-- @provenance independent
/-- On `S`, a triple is fixed by Zagier's map exactly when `x = y`. (Cases 1 and 3 have no
fixed points because they would force `z = 0` or `y = 0`.) -/
theorem zagierMap_fixed_iff {k x y z : ℕ} (hp : (4 * k + 1).Prime)
    (ht : x ^ 2 + 4 * y * z = 4 * k + 1) : zagierMap (x, y, z) = (x, y, z) ↔ x = y := by
  obtain ⟨hx, hy, hz, hb₁, hb₂⟩ := zagier_facts hp ht
  simp only [zagierMap]
  split_ifs with h₁ h₂ <;> rw [Prod.ext_iff, Prod.ext_iff] <;> dsimp only <;> omega
-- @endregion

-- @region formalising_published_mathematics.zagier_fixed_points
-- @provenance independent
/-- The unique fixed point. If `x = y` then `x(x + 4z) = p`; as `p` is prime and `x + 4z > 1`,
`x = 1`, and then `z = k`. So the fixed points of Zagier's map on `S` are exactly `{(1, 1, k)}`. -/
theorem zagier_fixed_points {k : ℕ} (hp : (4 * k + 1).Prime) :
    (zagierSet k).filter (fun t => zagierMap t = t) = {(1, 1, k)} := by
  ext ⟨x, y, z⟩
  simp only [mem_filter, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨ht, hfix⟩
    rw [mem_zagierSet hp] at ht
    simp only at ht
    have hxy : x = y := (zagierMap_fixed_iff hp ht).1 hfix
    subst hxy
    obtain ⟨hx, -, hz, -, -⟩ := zagier_facts hp ht
    -- `x` divides `p = x * (x + 4z)`, so `x = 1` or `x = p`.
    have hdvd : x ∣ 4 * k + 1 := ⟨x + 4 * z, by rw [← ht]; ring⟩
    rcases hp.eq_one_or_self_of_dvd x hdvd with rfl | hxp
    · refine ⟨rfl, rfl, ?_⟩
      norm_num at ht
      omega
    · -- `x = p` is impossible: then `p² ≤ x² + 4xz = p`.
      exfalso
      have : (4 * k + 1) * (4 * k + 1) ≤ 4 * k + 1 := by
        calc (4 * k + 1) * (4 * k + 1) = x ^ 2 := by rw [hxp]; ring
          _ ≤ x ^ 2 + 4 * x * z := Nat.le_add_right _ _
          _ = 4 * k + 1 := ht
      nlinarith
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨(mem_zagierSet hp).2 (by ring), ?_⟩
    rw [zagierMap_fixed_iff hp (by ring)]
-- @endregion

/-! ### Blueprint 4: involutions and parity -/

-- @region formalising_published_mathematics.card_mod_two_of_involution
-- @provenance independent
/-- **Parity lemma.** If `f` is an involution of a finite set `s`, then `s` and the set of fixed
points of `f` have the same parity. Proof by strong induction: remove a fixed point, or remove a
two-element orbit `{x, f x}`. (Mathlib has a more general version for any prime `p`:
`Equiv.Perm.card_fixedPoints_modEq`.) -/
theorem card_mod_two_of_involution {α : Type*} [DecidableEq α] (f : α → α) (s : Finset α)
    (hmaps : ∀ x ∈ s, f x ∈ s) (hinv : ∀ x ∈ s, f (f x) = x) :
    s.card % 2 = (s.filter (fun x => f x = x)).card % 2 := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    by_cases hfx : f x = x
    · -- Remove the fixed point `x`.
      have hmaps' : ∀ y ∈ s.erase x, f y ∈ s.erase x := by
        intro y hy
        rw [mem_erase] at hy ⊢
        refine ⟨fun hfy => hy.1 ?_, hmaps y hy.2⟩
        calc y = f (f y) := (hinv y hy.2).symm
          _ = x := by rw [hfy, hfx]
      have IH := ih (s.erase x) (erase_ssubset hx) hmaps'
        (fun y hy => hinv y (mem_of_mem_erase hy))
      have hfilter : (s.erase x).filter (fun y => f y = y) =
          (s.filter (fun y => f y = y)).erase x := by
        ext y
        simp only [mem_filter, mem_erase]
        tauto
      have h₁ := card_erase_add_one hx
      have hxF : x ∈ s.filter (fun y => f y = y) := mem_filter.2 ⟨hx, hfx⟩
      have h₂ := card_erase_add_one hxF
      rw [hfilter] at IH
      omega
    · -- Remove the two-element orbit `{x, f x}`.
      have hfxs : f x ∈ s.erase x := mem_erase.2 ⟨hfx, hmaps x hx⟩
      have hmaps' : ∀ y ∈ (s.erase x).erase (f x), f y ∈ (s.erase x).erase (f x) := by
        intro y hy
        simp only [mem_erase] at hy ⊢
        obtain ⟨hy₁, hy₂, hy₃⟩ := hy
        refine ⟨fun h => hy₂ ?_, fun h => hy₁ ?_, hmaps y hy₃⟩
        · calc y = f (f y) := (hinv y hy₃).symm
            _ = x := by rw [h, hinv x hx]
        · calc y = f (f y) := (hinv y hy₃).symm
            _ = f x := by rw [h]
      have IH := ih ((s.erase x).erase (f x))
        ((erase_ssubset hfxs).trans (erase_ssubset hx)) hmaps'
        (fun y hy => hinv y (mem_of_mem_erase (mem_of_mem_erase hy)))
      have hfilter : ((s.erase x).erase (f x)).filter (fun y => f y = y) =
          s.filter (fun y => f y = y) := by
        ext y
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨⟨-, -, hy⟩, hfy⟩
          exact ⟨hy, hfy⟩
        · rintro ⟨hy, hfy⟩
          refine ⟨⟨fun h => ?_, fun h => hfx (h ▸ hfy), hy⟩, hfy⟩
          -- `f x` is not fixed, since `f (f x) = x ≠ f x`.
          rw [h, hinv x hx] at hfy
          exact hfx hfy.symm
      have h₁ := card_erase_add_one hx
      have h₂ := card_erase_add_one hfxs
      rw [hfilter] at IH
      omega
-- @endregion

-- @region formalising_published_mathematics.card_zagier_set_odd
-- @provenance independent
/-- "So `|S|` is odd": Zagier's map is an involution of `S` with exactly one fixed point. -/
theorem card_zagierSet_odd {k : ℕ} (hp : (4 * k + 1).Prime) : (zagierSet k).card % 2 = 1 := by
  rw [card_mod_two_of_involution zagierMap (zagierSet k)
    (fun t ht => zagierMap_mapsTo hp ht) (fun t ht => zagierMap_involutive hp ht),
    zagier_fixed_points hp, card_singleton]
-- @endregion

/-! ### Blueprint 5: the second involution and the theorem -/

-- @region formalising_published_mathematics.swap_map
-- @provenance definition
/-- The "obvious" involution `(x, y, z) ↦ (x, z, y)` of `S`. -/
def swapMap : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | (x, y, z) => (x, z, y)
-- @endregion

-- @region formalising_published_mathematics.zagier_two_squares
-- @provenance independent
/-- **Fermat's two-squares theorem, by Zagier's argument.** If `p = 4k + 1` is prime then `p` is
a sum of two squares. The swap is an involution of `S`; since `|S|` is odd it has an odd number of
fixed points, hence at least one, `(x, y, y)`, and then `p = x² + 4y² = x² + (2y)²`. -/
theorem zagier_two_squares (k : ℕ) (hp : (4 * k + 1).Prime) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  have hmaps : ∀ t ∈ zagierSet k, swapMap t ∈ zagierSet k := by
    rintro ⟨x, y, z⟩ ht
    rw [mem_zagierSet hp] at ht ⊢
    simp only [swapMap] at ht ⊢
    rw [← ht]; ring
  have hinv : ∀ t ∈ zagierSet k, swapMap (swapMap t) = t := by
    rintro ⟨x, y, z⟩ -
    rfl
  have hpar := card_mod_two_of_involution swapMap (zagierSet k) hmaps hinv
  rw [card_zagierSet_odd hp] at hpar
  -- An odd number is not zero, so the swap has a fixed point.
  obtain ⟨⟨x, y, z⟩, ht⟩ : ((zagierSet k).filter (fun t => swapMap t = t)).Nonempty := by
    rw [← card_pos]
    omega
  rw [mem_filter, mem_zagierSet hp] at ht
  obtain ⟨ht, hfix⟩ := ht
  simp only [swapMap, Prod.mk.injEq] at hfix ht
  obtain ⟨-, hzy, -⟩ := hfix
  subst hzy
  exact ⟨x, 2 * z, by rw [← ht]; ring⟩
-- @endregion

/-! ### Checking the formal statement against the published one -/

-- @region formalising_published_mathematics.prime_one_mod_four
-- @provenance independent
/-- The published statement, in its usual form: every prime `p ≡ 1 (mod 4)` is a sum of two
squares. Deduced from `zagier_two_squares` with `k = p / 4`; this small step is the check that
"`p = 4k + 1`" and "`p ≡ 1 (mod 4)`" say the same thing. -/
theorem prime_one_mod_four {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have hk : 4 * (p / 4) + 1 = p := by omega
  rw [← hk] at hp ⊢
  exact zagier_two_squares (p / 4) hp
-- @endregion

-- @region formalising_published_mathematics.two_squares_library
-- @provenance library
/-- The same theorem from Mathlib: `Nat.Prime.sq_add_sq` proves that every prime `p` with
`p % 4 ≠ 3` is a sum of two squares (so it also covers `p = 2 = 1² + 1²`), by a different
proof through the unique factorisation of the Gaussian integers `ℤ[i]`. -/
theorem two_squares_library {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  haveI := Fact.mk hp
  Nat.Prime.sq_add_sq (by omega)
-- @endregion

-- @region formalising_published_mathematics.primality_needed
-- @provenance independent
/-- Where the hypothesis "prime" is used. For `21 = 4·5 + 1`, which is not prime, Zagier's map
has *two* fixed points in `S`, `(1, 1, 5)` and `(3, 3, 1)`, so the parity argument collapses — and
indeed `21` is not a sum of two squares. -/
theorem primality_needed :
    (1 ^ 2 + 4 * 1 * 5 = 21 ∧ zagierMap (1, 1, 5) = (1, 1, 5)) ∧
    (3 ^ 2 + 4 * 3 * 1 = 21 ∧ zagierMap (3, 3, 1) = (3, 3, 1)) ∧
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 21 := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨a, b, h⟩
  have ha : a < 5 := by nlinarith
  have hb : b < 5 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega
-- @endregion

end Lumenary.FormalisingPublishedMathematics
