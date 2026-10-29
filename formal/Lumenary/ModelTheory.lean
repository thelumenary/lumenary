/-
The Lumenary — formal mathematics
Model theory: elementary equivalence, ultraproducts and Łoś's theorem, compactness, quantifier
elimination for dense linear orders, and the Ax–Grothendieck theorem.

What is proved here and what Mathlib provides. Proved here (`independent`): the key lemma of
quantifier elimination for dense linear orders without endpoints (eliminating one `∃x` from a
conjunction of strict bounds); that `(ℚ, ≤)` and `(ℝ, ≤)` are not isomorphic as first-order
structures; and that the ultrapower `ℕ^ℕ/U` by a non-principal ultrafilter contains a
"nonstandard" element above every standard number. Applied from Mathlib (`library`): Łoś's
theorem (`FirstOrder.Language.Ultraproduct.sentence_realize`), the compactness theorem (which
Mathlib proves *with* ultraproducts), `ℵ₀`-categoricity and completeness of the theory of dense
linear orders (hence `ℚ ≡ ℝ`), Cantor's back-and-forth theorem, the Lefschetz principle for
algebraically closed fields, and the Ax–Grothendieck theorem (which Mathlib proves by the
model-theoretic route this lesson describes). Quantifier elimination for dense linear orders
and for algebraically closed fields is not (yet) in Mathlib as a theorem about formulas; only
its key step for dense orders is formalised below.
-/
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.FieldTheory.AxGrothendieck
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.Real.Cardinality

namespace Lumenary.ModelTheory

open FirstOrder FirstOrder.Language

universe u v w

/-! ### Quantifier elimination for dense linear orders: the key step -/

-- @region model_theory.dlo_elim_core
-- @provenance independent
/-- **The key lemma of quantifier elimination for DLO.** In a nonempty dense linear order
without endpoints, a point `x` strictly above every element of the finite set `L` and strictly
below every element of the finite set `U` exists **if and only if** every element of `L` is
below every element of `U`. So the formula `∃x (⋀ aᵢ < x ∧ ⋀ x < bⱼ)` is equivalent to the
quantifier-free formula `⋀ᵢⱼ aᵢ < bⱼ`.

The proof follows the lesson: if both sets are nonempty, density gives a point between
`max L < min U`; if one is empty, "no endpoints" gives a point beyond the other; if both are
empty, nonemptiness gives any point. -/
theorem dlo_elim_core {α : Type*} [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [Nonempty α] (L U : Finset α) :
    (∃ x, (∀ a ∈ L, a < x) ∧ ∀ b ∈ U, x < b) ↔ ∀ a ∈ L, ∀ b ∈ U, a < b := by
  constructor
  · rintro ⟨x, hL, hU⟩ a ha b hb
    exact (hL a ha).trans (hU b hb)
  · intro h
    rcases L.eq_empty_or_nonempty with rfl | hL
    · rcases U.eq_empty_or_nonempty with rfl | hU
      · -- no constraints at all: any point will do
        obtain ⟨x⟩ := ‹Nonempty α›
        exact ⟨x, by simp, by simp⟩
      · -- only upper bounds: go below the least of them (no least element)
        obtain ⟨x, hx⟩ := exists_lt (U.min' hU)
        exact ⟨x, by simp, fun b hb => hx.trans_le (U.min'_le b hb)⟩
    · rcases U.eq_empty_or_nonempty with rfl | hU
      · -- only lower bounds: go above the greatest of them (no greatest element)
        obtain ⟨x, hx⟩ := exists_gt (L.max' hL)
        exact ⟨x, fun a ha => (L.le_max' a ha).trans_lt hx, by simp⟩
      · -- both: `max L < min U` by hypothesis, and density puts a point in between
        have hlt : L.max' hL < U.min' hU := h _ (L.max'_mem hL) _ (U.min'_mem hU)
        obtain ⟨x, hx₁, hx₂⟩ := exists_between hlt
        exact ⟨x, fun a ha => (L.le_max' a ha).trans_lt hx₁,
          fun b hb => hx₂.trans_le (U.min'_le b hb)⟩
-- @endregion

-- @region model_theory.dlo_elim_core_fails_discrete
-- @provenance independent
/-- **Density is needed.** In the integers (a linear order without endpoints, but *not* dense)
the elimination of `model_theory.dlo_elim_core` fails: `0 < 1` holds, yet nothing lies strictly
between `0` and `1`. So `∃x (0 < x ∧ x < 1)` is not equivalent to `0 < 1` in `(ℤ, <)`. -/
theorem dlo_elim_core_fails_discrete :
    (∀ a ∈ ({0} : Finset ℤ), ∀ b ∈ ({1} : Finset ℤ), a < b) ∧
      ¬ ∃ x : ℤ, (∀ a ∈ ({0} : Finset ℤ), a < x) ∧ ∀ b ∈ ({1} : Finset ℤ), x < b := by
  refine ⟨by simp, ?_⟩
  rintro ⟨x, h0, h1⟩
  have hx0 : 0 < x := h0 0 (by simp)
  have hx1 : x < 1 := h1 1 (by simp)
  omega
-- @endregion

/-! ### Elementarily equivalent but not isomorphic: `(ℚ, ≤)` and `(ℝ, ≤)` -/

-- @region model_theory.rat_elem_equiv_real
-- @provenance library
/-- **`(ℚ, ≤) ≡ (ℝ, ≤)`**: the rationals and the reals satisfy exactly the same first-order
sentences in the language `{≤}`. Both are models of the theory `dlo` of dense linear orders
without endpoints, and `dlo` is complete (Mathlib's `FirstOrder.Language.dlo_isComplete`, proved
by the Łoś–Vaught test from `ℵ₀`-categoricity); in a complete theory every sentence is decided,
so each model satisfies `φ` iff `dlo ⊨ φ` (`Theory.IsComplete.realize_sentence_iff`). -/
theorem rat_elem_equiv_real :
    letI := orderStructure ℚ
    letI := orderStructure ℝ
    ℚ ≅[Language.order] ℝ := by
  let := orderStructure ℚ
  let := orderStructure ℝ
  have : Language.order.OrderedStructure ℚ := ⟨fun _ => Iff.rfl⟩
  have : Language.order.OrderedStructure ℝ := ⟨fun _ => Iff.rfl⟩
  rw [elementarilyEquivalent_iff]
  intro φ
  rw [dlo_isComplete.realize_sentence_iff φ ℚ, dlo_isComplete.realize_sentence_iff φ ℝ]
-- @endregion

-- @region model_theory.rat_not_equiv_real
-- @provenance independent
/-- **…but not isomorphic.** There is no isomorphism of `{≤}`-structures between `ℚ` and `ℝ`:
an isomorphism is in particular a bijection, which would make `ℝ` countable, contradicting
Cantor's theorem (`Cardinal.not_countable_real`). Elementary equivalence is much weaker than
isomorphism: first-order logic cannot express "countable" or "complete". -/
theorem rat_not_equiv_real :
    letI := orderStructure ℚ
    letI := orderStructure ℝ
    ¬ Nonempty (ℚ ≃[Language.order] ℝ) := by
  let := orderStructure ℚ
  let := orderStructure ℝ
  rintro ⟨e⟩
  -- `e⁻¹ : ℝ → ℚ` is injective and `ℚ` is countable, so `ℝ` would be countable.
  have hinj : Function.Injective e.symm := e.symm.injective
  have : Countable ℝ := hinj.countable
  exact Cardinal.not_countable_real Set.countable_univ
-- @endregion

-- @region model_theory.cantor_back_and_forth
-- @provenance library
/-- **Cantor's theorem (back and forth).** Any two countable, nonempty, dense linear orders
without endpoints are order-isomorphic. This applies Mathlib's `Order.iso_of_countable_dense`,
whose proof is the back-and-forth construction of the lesson. -/
theorem cantor_back_and_forth (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β]
    [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]
    [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) :=
  Order.iso_of_countable_dense α β
-- @endregion

-- @region model_theory.dlo_aleph0_categorical
-- @provenance library
/-- **`DLO` is `ℵ₀`-categorical**: all countably infinite models of the theory of dense linear
orders without endpoints are isomorphic as first-order structures. This applies Mathlib's
`FirstOrder.Language.aleph0_categorical_dlo` (proved there via Fraïssé limits, a model-theoretic
packaging of back and forth). -/
theorem dlo_aleph0_categorical : Cardinal.Categorical.{0, 0, w} Cardinal.aleph0 Language.order.dlo :=
  aleph0_categorical_dlo
-- @endregion

/-! ### Ultraproducts, Łoś and compactness -/

-- @region model_theory.los
-- @provenance library
/-- **Łoś's theorem.** For nonempty structures `M a` (indexed by `a : α`) and an ultrafilter `U`
on `α`, a sentence holds in the ultraproduct `∏ M a / U` if and only if the set of indices `a` at which
it holds in `M a` belongs to `U`. This applies Mathlib's
`FirstOrder.Language.Ultraproduct.sentence_realize`, proved by induction on formulas exactly as
in the lesson. -/
theorem los {L : Language.{u, v}} {α : Type*} (M : α → Type*) (U : Ultrafilter α)
    [∀ a, L.Structure (M a)] [∀ a, Nonempty (M a)] (φ : L.Sentence) :
    (U : Filter α).Product M ⊨ φ ↔ ∀ᶠ a in (U : Filter α), M a ⊨ φ :=
  Ultraproduct.sentence_realize φ
-- @endregion

-- @region model_theory.compactness
-- @provenance library
/-- **The compactness theorem.** A first-order theory has a model if and only if every finite
subset of it has a model. This applies Mathlib's `Theory.isSatisfiable_iff_isFinitelySatisfiable`,
whose proof is the lesson's second proof: take an ultraproduct of models of the finite subsets,
indexed by the finite subsets, along an ultrafilter extending the "eventually" filter, and apply
Łoś's theorem. -/
theorem compactness {L : Language.{u, v}} (T : L.Theory) :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  Theory.isSatisfiable_iff_isFinitelySatisfiable
-- @endregion

-- @region model_theory.nonstandard_natural
-- @provenance independent
/-- **A nonstandard natural number.** Let `U` be a non-principal ultrafilter on `ℕ` (Mathlib's
`hyperfilter ℕ`). In the ultrapower `ℕ^ℕ/U`, the class of the identity sequence `(0, 1, 2, …)`
is strictly greater than (the class of) every constant sequence `n`. Indeed, by the definition of
the order on the ultrapower (`Filter.Germ.coe_lt`, the atomic case of Łoś) we need
`{i | n < i} ∈ U`; this set is cofinite, and a non-principal ultrafilter contains every cofinite
set (`Filter.hyperfilter_le_cofinite`). By Łoś, `ℕ^ℕ/U` satisfies the same sentences as `ℕ`,
yet it has an element above all the standard ones. -/
theorem nonstandard_natural (n : ℕ) :
    (↑(fun _ : ℕ => n) : (Filter.hyperfilter ℕ : Filter ℕ).Germ ℕ) < ↑(id : ℕ → ℕ) := by
  rw [Filter.Germ.coe_lt]
  have h : ∀ᶠ i in (Filter.cofinite : Filter ℕ), n < i := by
    rw [Nat.cofinite_eq_atTop]
    exact Filter.eventually_gt_atTop n
  exact Filter.hyperfilter_le_cofinite h
-- @endregion

-- @region model_theory.nonstandard_ne_standard
-- @provenance independent
/-- The nonstandard element `[id]` of `ℕ^ℕ/U` is different from every standard element `[n]`:
a direct consequence of `nonstandard_natural`. So the diagonal embedding `ℕ → ℕ^ℕ/U`, which is
elementary by Łoś's theorem, is not surjective. -/
theorem nonstandard_ne_standard (n : ℕ) :
    (↑(fun _ : ℕ => n) : (Filter.hyperfilter ℕ : Filter ℕ).Germ ℕ) ≠ ↑(id : ℕ → ℕ) :=
  (nonstandard_natural n).ne
-- @endregion

/-! ### Algebraically closed fields -/

-- @region model_theory.lefschetz
-- @provenance library
/-- **The Lefschetz principle.** A first-order sentence in the language of rings follows from
the theory `ACF₀` of algebraically closed fields of characteristic `0` if and only if it follows
from `ACF_p` for infinitely many primes `p`. This applies Mathlib's
`FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize`, proved from compactness and
the completeness of each `ACF_p`. -/
theorem lefschetz (φ : Language.ring.Sentence) :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite {p : Nat.Primes | Theory.ACF p ⊨ᵇ φ} :=
  Field.ACF_zero_realize_iff_infinite_ACF_prime_realize
-- @endregion

-- @region model_theory.ax_grothendieck
-- @provenance library
/-- **The Ax–Grothendieck theorem.** If `K` is an algebraically closed field and `ι` is finite,
every injective polynomial map `K^ι → K^ι` is surjective. This applies Mathlib's
`ax_grothendieck_univ`, which is proved by the model-theoretic argument of the lesson: the
statement for polynomials of bounded degree is a first-order sentence; it holds in the
algebraic closure of each finite field (a union of finite fields, where injective implies
surjective by counting); so it holds in every algebraically closed field by the Lefschetz
principle and completeness of `ACF_p`. -/
theorem ax_grothendieck {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι]
    (p : ι → MvPolynomial ι K) :
    Function.Injective (fun v i => MvPolynomial.eval v (p i)) →
      Function.Surjective (fun v i => MvPolynomial.eval v (p i)) :=
  ax_grothendieck_univ p
-- @endregion

end Lumenary.ModelTheory
