/-
The Lumenary — formal mathematics
Formalising mathematics in Lean and Mathlib: sets and functions, quantifier reasoning, an
ε–N definition checked against Mathlib's, structures and type classes, Mathlib's algebraic
hierarchy, and the conventions (division by zero, truncated subtraction) that formal statements
force into the open.

What is proved here and what Mathlib provides. Most theorems are proved twice in spirit: once
*independently*, step by step as a mathematician would argue (and as the lesson's human proofs
do), and once by citing the Mathlib lemma that already exists (*library*). The independent
proofs show how quantifiers, set extensionality and algebraic laws are handled in Lean; the
library versions show how to find and reuse the hundreds of thousands of results already in
Mathlib. One theorem, `convergesTo_iff_tendsto`, checks that our home-made ε–N definition of
convergence agrees with Mathlib's filter-based one — the kind of check that makes a formal
library trustworthy.
-/
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring

namespace Lumenary.FormalProofLean

open Function Set Filter Topology

/-! ### Functions: injective and surjective composites -/

-- @region formal_proof_lean.injective_comp
-- @provenance independent
/-- **A composite of injections is injective**, proved as on paper: if `g (f x) = g (f y)`,
then `f x = f y` because `g` is injective, and then `x = y` because `f` is injective. -/
theorem injective_comp {α β γ : Type*} {f : α → β} {g : β → γ} (hg : Injective g)
    (hf : Injective f) : Injective (g ∘ f) := by
  intro x y h
  -- `h : (g ∘ f) x = (g ∘ f) y`, which is `g (f x) = g (f y)` by definition.
  apply hf
  apply hg
  exact h
-- @endregion

-- @region formal_proof_lean.injective_comp_library
-- @provenance library
/-- The same theorem, found in Mathlib: `Function.Injective.comp`. Its name follows Mathlib's
naming convention — the conclusion's shape, `Injective (g ∘ f)`, read as `Injective.comp` — and
it can be found by `exact?` or by searching the documentation. -/
theorem injective_comp_library {α β γ : Type*} {f : α → β} {g : β → γ} (hg : Injective g)
    (hf : Injective f) : Injective (g ∘ f) :=
  hg.comp hf
-- @endregion

-- @region formal_proof_lean.surjective_comp
-- @provenance independent
/-- **A composite of surjections is surjective.** Given `z`, choose `y` with `g y = z`, then
`x` with `f x = y`; then `g (f x) = z`. Each "choose" is the elimination of an `∃`. -/
theorem surjective_comp {α β γ : Type*} {f : α → β} {g : β → γ} (hg : Surjective g)
    (hf : Surjective f) : Surjective (g ∘ f) := by
  intro z
  obtain ⟨y, rfl⟩ := hg z
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, rfl⟩
-- @endregion

-- @region formal_proof_lean.injective_of_comp
-- @provenance independent
/-- If `g ∘ f` is injective then `f` is injective (but `g` need not be). -/
theorem injective_of_comp {α β γ : Type*} {f : α → β} {g : β → γ} (h : Injective (g ∘ f)) :
    Injective f := by
  intro x y hxy
  apply h
  show g (f x) = g (f y)
  rw [hxy]
-- @endregion

/-! ### Sets: images and preimages -/

-- @region formal_proof_lean.image_union
-- @provenance independent
/-- `f(s ∪ t) = f(s) ∪ f(t)`, by extensionality: show that an arbitrary `y` lies in the left
side exactly when it lies in the right side. (Mathlib: `Set.image_union`.) -/
theorem image_union {α β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩
-- @endregion

-- @region formal_proof_lean.image_inter_subset
-- @provenance independent
/-- `f(s ∩ t) ⊆ f(s) ∩ f(t)` always holds. -/
theorem image_inter_subset {α β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨hs, ht⟩, rfl⟩
  exact ⟨⟨x, hs, rfl⟩, ⟨x, ht, rfl⟩⟩
-- @endregion

-- @region formal_proof_lean.image_inter_ne
-- @provenance independent
/-- …but equality can fail. With the constant function `f = 0` on `ℕ`, `s = {0}` and `t = {1}`:
`f(s ∩ t) = f(∅) = ∅`, while `f(s) ∩ f(t) = {0}`. -/
theorem image_inter_ne :
    ∃ (f : ℕ → ℕ) (s t : Set ℕ), f '' (s ∩ t) ≠ f '' s ∩ f '' t := by
  refine ⟨fun _ => 0, {0}, {1}, ?_⟩
  intro h
  have h0 : (0 : ℕ) ∈ (fun _ : ℕ => (0 : ℕ)) '' {0} ∩ (fun _ : ℕ => (0 : ℕ)) '' {1} :=
    ⟨⟨0, rfl, rfl⟩, ⟨1, rfl, rfl⟩⟩
  rw [← h] at h0
  obtain ⟨x, ⟨hx0, hx1⟩, -⟩ := h0
  rw [mem_singleton_iff] at hx0 hx1
  omega
-- @endregion

-- @region formal_proof_lean.image_inter_of_injective
-- @provenance library
/-- For an *injective* `f`, equality does hold: Mathlib's `Set.image_inter`. The hypothesis
`Injective f` is exactly what the counterexample above lacks. -/
theorem image_inter_of_injective {α β : Type*} {f : α → β} (hf : Injective f) (s t : Set α) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  Set.image_inter hf
-- @endregion

-- @region formal_proof_lean.preimage_inter
-- @provenance independent
/-- Preimages behave perfectly: `f⁻¹(s ∩ t) = f⁻¹(s) ∩ f⁻¹(t)`. In Lean both sides unfold to the
same predicate `fun x => f x ∈ s ∧ f x ∈ t`, so the proof is `rfl`: true *by definition*. -/
theorem preimage_inter {α β : Type*} (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl
-- @endregion

/-! ### Quantifiers -/

-- @region formal_proof_lean.exists_forall_imp
-- @provenance independent
/-- `∃ x, ∀ y, P x y` implies `∀ y, ∃ x, P x y`: a single `x` that works for every `y` certainly
gives, for each `y`, some `x`. -/
theorem exists_forall_imp {α β : Type*} (P : α → β → Prop) :
    (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  rintro ⟨x, hx⟩ y
  exact ⟨x, hx y⟩
-- @endregion

-- @region formal_proof_lean.forall_exists_not_imp
-- @provenance independent
/-- The converse fails: every natural number has a larger one (`∀ n, ∃ m, n < m`), but no
natural number is larger than all of them (`∃ m, ∀ n, n < m` is false — take `n = m`). -/
theorem forall_exists_not_imp :
    ¬ ((∀ n : ℕ, ∃ m, n < m) → ∃ m : ℕ, ∀ n, n < m) := by
  intro h
  obtain ⟨m, hm⟩ := h (fun n => ⟨n + 1, Nat.lt_succ_self n⟩)
  exact lt_irrefl m (hm m)
-- @endregion

-- @region formal_proof_lean.converges_to
-- @provenance definition
/-- The ε–N definition of convergence of a real sequence, written exactly as in an analysis
course: for every `ε > 0` there is `N` such that `|aₙ − L| < ε` for all `n ≥ N`. -/
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- @endregion

-- @region formal_proof_lean.converges_one_div
-- @provenance independent
/-- `1/(n + 1) → 0`. Given `ε > 0`, the Archimedean property gives `N > 1/ε`; then for `n ≥ N`,
`1/(n + 1) < 1/N < ε`. -/
theorem converges_one_div : ConvergesTo (fun n => 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [sub_zero, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ hpos]
  rw [div_lt_iff₀ hε] at hN
  nlinarith
-- @endregion

-- @region formal_proof_lean.limit_unique
-- @provenance independent
/-- **Limits are unique.** If `a → L` and `a → M` with `L ≠ M`, take `ε = |L − M|/2`: for large
`n`, `|L − M| ≤ |aₙ − L| + |aₙ − M| < 2ε = |L − M|`, a contradiction. -/
theorem limit_unique {a : ℕ → ℝ} {L M : ℝ} (hL : ConvergesTo a L) (hM : ConvergesTo a M) :
    L = M := by
  by_contra hne
  have hε : 0 < |L - M| / 2 := by
    have : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨N₁, h₁⟩ := hL _ hε
  obtain ⟨N₂, h₂⟩ := hM _ hε
  have k₁ := h₁ (max N₁ N₂) (le_max_left _ _)
  have k₂ := h₂ (max N₁ N₂) (le_max_right _ _)
  have tri : |L - M| ≤ |a (max N₁ N₂) - L| + |a (max N₁ N₂) - M| := by
    calc |L - M| = |(a (max N₁ N₂) - M) - (a (max N₁ N₂) - L)| := by ring_nf
      _ ≤ |a (max N₁ N₂) - M| + |a (max N₁ N₂) - L| := abs_sub _ _
      _ = |a (max N₁ N₂) - L| + |a (max N₁ N₂) - M| := add_comm _ _
  linarith
-- @endregion

-- @region formal_proof_lean.converges_to_iff_tendsto
-- @provenance library
/-- **Does our definition mean what Mathlib means?** Mathlib defines convergence with filters:
`Tendsto a atTop (𝓝 L)`. Mathlib's `Metric.tendsto_atTop` unfolds it to the ε–N form with
`dist (a n) L`, and `Real.dist_eq` says `dist x y = |x − y|`. So the two definitions agree, and
every Mathlib theorem about `Tendsto` applies to `ConvergesTo`. -/
theorem convergesTo_iff_tendsto (a : ℕ → ℝ) (L : ℝ) :
    ConvergesTo a L ↔ Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  simp only [ConvergesTo, Real.dist_eq]
-- @endregion

/-! ### Structures and type classes -/

-- @region formal_proof_lean.my_monoid
-- @provenance definition
/-- A home-made **type class** for monoids: a type `M` with a multiplication and a unit, and the
three laws as fields. A *structure* bundles data and proofs; declaring it as a `class` lets Lean
find an instance automatically. (Mathlib's real `Monoid` is built the same way, from smaller
classes such as `Mul`, `One` and `Semigroup`.) -/
class MyMonoid (M : Type*) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
-- @endregion

-- @region formal_proof_lean.my_monoid_nat
-- @provenance definition
/-- An **instance**: the natural numbers under addition form a monoid with unit `0`. The laws
are discharged by core lemmas about `Nat`. -/
instance natAddMyMonoid : MyMonoid ℕ where
  mul := (· + ·)
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
-- @endregion

-- @region formal_proof_lean.my_monoid_one_unique
-- @provenance independent
/-- **The unit of a monoid is unique**, proved once for *every* instance of `MyMonoid`: if `e`
is a two-sided unit then `e = one`, because `e = e · one = one`. -/
theorem MyMonoid.one_unique {M : Type*} [MyMonoid M] (e : M)
    (he : ∀ a : M, MyMonoid.mul e a = a ∧ MyMonoid.mul a e = a) :
    e = MyMonoid.one :=
  calc e = MyMonoid.mul e MyMonoid.one := (MyMonoid.mul_one e).symm
    _ = MyMonoid.one := (he MyMonoid.one).1
-- @endregion

-- @region formal_proof_lean.zero_unique_nat
-- @provenance independent
/-- Using the generic theorem at the instance for `ℕ`: a number `e` with `e + a = a` and
`a + e = a` for all `a` must be `0`. Lean finds `natAddMyMonoid` by instance search. -/
theorem zero_unique_nat (e : ℕ) (he : ∀ a : ℕ, e + a = a ∧ a + e = a) : e = 0 :=
  MyMonoid.one_unique e he
-- @endregion

/-! ### Mathlib's algebraic hierarchy -/

-- @region formal_proof_lean.inv_unique
-- @provenance independent
/-- In any Mathlib `Monoid`, a left inverse and a right inverse of the same element agree:
`b = b (a c) = (b a) c = c`. -/
theorem inv_unique {M : Type*} [Monoid M] {a b c : M} (hb : b * a = 1) (hc : a * c = 1) :
    b = c :=
  calc b = b * (a * c) := by rw [hc, mul_one]
    _ = b * a * c := (mul_assoc b a c).symm
    _ = c := by rw [hb, one_mul]
-- @endregion

-- @region formal_proof_lean.comm_of_sq_eq_one
-- @provenance independent
/-- **A group in which every element squares to `1` is commutative.** From `x x = 1` we get
`x⁻¹ = x` for every `x`, so `a b = (a b)⁻¹ = b⁻¹ a⁻¹ = b a`. This works in *every* `Group`,
because the proof uses only the group laws (Mathlib lemmas `inv_eq_of_mul_eq_one_right` and
`mul_inv_rev`). -/
theorem comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h x)
  calc a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv a, hinv b]
-- @endregion

-- @region formal_proof_lean.add_sq_comm_ring
-- @provenance independent
/-- In every commutative ring, `(a + b)² = a² + 2ab + b²`. The `ring` tactic decides such
identities by normalising both sides; the theorem then holds in `ℤ`, `ℚ`, `ℝ`, `ℤ/nℤ`,
polynomial rings, … at once. -/
theorem add_sq_comm_ring {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
-- @endregion

/-! ### Conventions that formalisation makes visible -/

-- @region formal_proof_lean.div_zero_convention
-- @provenance library
/-- In Lean and Mathlib, `x / 0 = 0` (`div_zero`). This is a convention making division a total
function; it does not change any theorem about division by non-zero numbers. -/
theorem div_zero_convention (x : ℝ) : x / 0 = 0 :=
  div_zero x
-- @endregion

-- @region formal_proof_lean.div_mul_cancel_of_ne
-- @provenance library
/-- The familiar cancellation law carries its hypothesis explicitly: if `b ≠ 0` then
`a / b · b = a` (`div_mul_cancel₀`). -/
theorem div_mul_cancel_of_ne (a : ℝ) {b : ℝ} (hb : b ≠ 0) : a / b * b = a :=
  div_mul_cancel₀ a hb
-- @endregion

-- @region formal_proof_lean.div_mul_cancel_needs_hyp
-- @provenance independent
/-- Without the hypothesis the law is false: `1 / 0 · 0 = 0 ≠ 1`. So the convention `x / 0 = 0`
cannot be used to "prove" anything false about real division. -/
theorem div_mul_cancel_needs_hyp : ¬ ∀ a b : ℝ, a / b * b = a := by
  intro h
  have := h 1 0
  norm_num at this
-- @endregion

-- @region formal_proof_lean.nat_sub_truncates
-- @provenance independent
/-- Subtraction on `ℕ` is **truncated**: `2 − 3 = 0`, because there is no natural number
`−1`. -/
theorem nat_sub_truncates : (2 : ℕ) - 3 = 0 := by
  decide
-- @endregion

-- @region formal_proof_lean.nat_sub_add_cancel
-- @provenance library
/-- So `(a − b) + b = a` needs the hypothesis `b ≤ a` (`Nat.sub_add_cancel`); for `a = 2`,
`b = 3` the left side is `3`. -/
theorem nat_sub_add_cancel {a b : ℕ} (h : b ≤ a) : a - b + b = a :=
  Nat.sub_add_cancel h
-- @endregion

end Lumenary.FormalProofLean
