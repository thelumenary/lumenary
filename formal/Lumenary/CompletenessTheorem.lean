/-
The Lumenary — formal mathematics
Completeness, compactness and Löwenheim–Skolem.

Mathlib has first-order syntax and semantics (`FirstOrder.Language`, `Theory`, `⊨`) and proves the
**compactness theorem** semantically, with ultraproducts and Łoś's theorem; it proves the
**Löwenheim–Skolem** theorems, Cantor's theorem that dense linear orders without endpoints are
`ℵ₀`-categorical, and the **Łoś–Vaught test**. It does not (at this version) contain a formal
proof calculus `⊢` for first-order logic, so Gödel's completeness theorem itself — "every
consistent theory has a model" — is *not* formalised here.

What we do formalise:
* the **Lindenbaum lemma**, the combinatorial heart of the Henkin proof, for any finitary notion
  of consistency (`lindenbaum`), and the fact that a maximal consistent set decides every
  sentence (`maximal_mem_or_neg_mem`) — both proved here with Zorn's lemma, as in the lesson;
* their instance for semantic satisfiability, which is finitary by compactness: every
  satisfiable theory extends to a maximal satisfiable (hence complete) theory;
* the classic application of compactness: a theory with arbitrarily large finite models has an
  infinite model, so "the universe is finite" is not expressible by any first-order theory.
-/
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Order
import Mathlib.Order.Zorn

namespace Lumenary.CompletenessTheorem

universe u v w

open FirstOrder FirstOrder.Language Cardinal

/-! ### Lindenbaum's lemma, for any finitary notion of consistency -/

-- @region completeness_theorem.finitary
-- @provenance definition
/-- A notion of consistency `Con` on sets of sentences is **finitary** if a set is consistent
exactly when each of its finite subsets is. Consistency in the sense of proofs is finitary,
because a derivation of a contradiction uses only finitely many hypotheses. -/
def Finitary {S : Type u} (Con : Set S → Prop) : Prop :=
  ∀ Γ : Set S, Con Γ ↔ ∀ Δ : Finset S, (Δ : Set S) ⊆ Γ → Con Δ
-- @endregion

-- @region completeness_theorem.lindenbaum
-- @provenance independent
/-- **Lindenbaum's lemma.** For a finitary notion of consistency, every consistent set `Γ` is
contained in a *maximal* consistent set. Zorn's lemma, applied to consistent supersets of `Γ`
ordered by `⊆`: the union of a non-empty chain is consistent, because each finite subset of the
union already lies in a single member of the chain. (For a countable language one can avoid
Zorn by listing the sentences `φ₀, φ₁, …` and adding each one if consistency allows.) -/
theorem lindenbaum {S : Type u} (Con : Set S → Prop) (hfin : Finitary Con) (Γ : Set S)
    (hΓ : Con Γ) : ∃ Δ, Γ ⊆ Δ ∧ Maximal Con Δ := by
  have chains : ∀ c ⊆ {Θ | Con Θ}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {Θ | Con Θ}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain hne
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    show Con (⋃₀ c)
    rw [hfin]
    intro Δ hΔ
    rw [Set.sUnion_eq_biUnion] at hΔ
    obtain ⟨t, htc, hΔt⟩ :=
      DirectedOn.exists_mem_subset_of_finset_subset_biUnion (f := id) hne hchain.directedOn hΔ
    exact (hfin t).mp (hc htc) Δ hΔt
  obtain ⟨Δ, hΓΔ, hmax⟩ := zorn_subset_nonempty {Θ | Con Θ} chains Γ hΓ
  exact ⟨Δ, hΓΔ, hmax⟩
-- @endregion

-- @region completeness_theorem.maximal_mem_or_neg_mem
-- @provenance independent
/-- **A maximal consistent set decides every sentence**, provided consistency *splits*: whenever
`Γ` is consistent, so is `Γ ∪ {φ}` or `Γ ∪ {¬φ}`. (For provability this holds because
`Γ ∪ {φ} ⊢ ⊥` and `Γ ∪ {¬φ} ⊢ ⊥` together give `Γ ⊢ ⊥`.) By maximality, whichever of the two
enlarged sets is consistent is `Γ` itself. -/
theorem maximal_mem_or_neg_mem {S : Type u} (Con : Set S → Prop) (neg : S → S)
    (hsplit : ∀ Γ φ, Con Γ → Con (insert φ Γ) ∨ Con (insert (neg φ) Γ))
    {Δ : Set S} (hΔ : Maximal Con Δ) (φ : S) : φ ∈ Δ ∨ neg φ ∈ Δ := by
  rcases hsplit Δ φ hΔ.prop with h | h
  · exact Or.inl (hΔ.mem_of_prop_insert h)
  · exact Or.inr (hΔ.mem_of_prop_insert h)
-- @endregion

/-! ### Compactness, and what follows from it -/

-- @region completeness_theorem.compactness
-- @provenance library
/-- **The compactness theorem:** a first-order theory has a model if and only if every finite
subset of it has a model. Mathlib proves this with an ultraproduct of models of the finite
subsets (Łoś's theorem). This applies `Theory.isSatisfiable_iff_isFinitelySatisfiable`. -/
theorem compactness {L : Language.{u, v}} (T : L.Theory) :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  Theory.isSatisfiable_iff_isFinitelySatisfiable
-- @endregion

-- @region completeness_theorem.satisfiable_finitary
-- @provenance library
/-- **Satisfiability is finitary** — this is just the compactness theorem
(`Theory.isSatisfiable_iff_isFinitelySatisfiable`), restated in the vocabulary of `Finitary`. -/
theorem satisfiable_finitary (L : Language.{u, v}) :
    Finitary (fun T : L.Theory => T.IsSatisfiable) := by
  intro T
  show Theory.IsSatisfiable T ↔
    ∀ Δ : Finset L.Sentence, (Δ : L.Theory) ⊆ T → Theory.IsSatisfiable (Δ : L.Theory)
  exact compactness T
-- @endregion

-- @region completeness_theorem.satisfiable_split
-- @provenance independent
/-- **Satisfiability splits:** if `T` has a model `M`, then `M` makes `φ` true or false, so
`T ∪ {φ}` or `T ∪ {¬φ}` has a model. -/
theorem satisfiable_split {L : Language.{u, v}} (T : L.Theory) (φ : L.Sentence)
    (hT : T.IsSatisfiable) : (insert φ T).IsSatisfiable ∨ (insert φ.not T).IsSatisfiable := by
  obtain ⟨M⟩ := hT
  by_cases hφ : M ⊨ φ
  · left
    have : M ⊨ insert φ T := Theory.model_insert_iff.mpr ⟨hφ, M.is_model⟩
    exact Theory.Model.isSatisfiable M
  · right
    have hnot : M ⊨ φ.not := (Sentence.realize_not M).mpr hφ
    have : M ⊨ insert φ.not T := Theory.model_insert_iff.mpr ⟨hnot, M.is_model⟩
    exact Theory.Model.isSatisfiable M
-- @endregion

-- @region completeness_theorem.exists_maximal_extension
-- @provenance independent
/-- **Every satisfiable theory extends to a maximal satisfiable theory**, which contains each
sentence or its negation (so it is complete). This is the Lindenbaum step of the Henkin proof,
with satisfiability in place of consistency: `lindenbaum` + `satisfiable_finitary` +
`maximal_mem_or_neg_mem`. (Semantically there is a shortcut — the complete theory of one model,
`completeTheory.isMaximal` — but in the Henkin proof no model is available yet.) -/
theorem exists_maximal_extension {L : Language.{u, v}} (T : L.Theory) (hT : T.IsSatisfiable) :
    ∃ T' : L.Theory, T ⊆ T' ∧ T'.IsMaximal := by
  obtain ⟨T', hTT', hmax⟩ := lindenbaum _ (satisfiable_finitary L) T hT
  refine ⟨T', hTT', hmax.prop, fun φ => ?_⟩
  exact maximal_mem_or_neg_mem (fun T : L.Theory => T.IsSatisfiable) (fun ψ => ψ.not)
    (fun Γ ψ h => satisfiable_split Γ ψ h) hmax φ
-- @endregion

-- @region completeness_theorem.exists_infinite_model
-- @provenance independent
/-- **A theory with arbitrarily large finite models has an infinite model.** Add to `T` the
sentences `σₖ` = "there are at least `k` elements" for all `k`. Any finite part of
`T ∪ {σₖ | k ∈ ℕ}` lies in `T ∪ {σₖ | k < n}` for some `n`, which a large enough model of `T`
satisfies; so by compactness the whole set has a model — a model of `T` that is infinite.
(In Lean: the theories `T ∪ {σₖ | k < n}` form a directed family whose union is
`T ∪ infiniteTheory`, and `isSatisfiable_directed_union_iff` is compactness for such a family.) -/
theorem exists_infinite_model {L : Language.{u, v}} (T : L.Theory)
    (h : ∀ n : ℕ, ∃ M : Theory.ModelType.{u, v, w} T, (n : Cardinal) ≤ #M) :
    ∃ M : Theory.ModelType.{u, v, max u v} T, Infinite M := by
  -- The theories `T ∪ {σₖ | k < n}`.
  let Tn : ℕ → L.Theory := fun n => T ∪ Sentence.cardGe L '' Set.Iio n
  have hdir : Directed (· ⊆ ·) Tn := by
    intro m n
    refine ⟨max m n, ?_, ?_⟩
    · exact Set.union_subset_union_right T
        (Set.image_mono (Set.Iio_subset_Iio (le_max_left m n)))
    · exact Set.union_subset_union_right T
        (Set.image_mono (Set.Iio_subset_Iio (le_max_right m n)))
  have hunion : (⋃ n, Tn n) = T ∪ L.infiniteTheory := by
    ext φ
    simp only [Tn, Set.mem_iUnion, Set.mem_union, Set.mem_image, Set.mem_Iio,
      Language.infiniteTheory, Set.mem_range]
    constructor
    · rintro ⟨n, hφ | ⟨k, -, hk⟩⟩
      · exact Or.inl hφ
      · exact Or.inr ⟨k, hk⟩
    · rintro (hφ | ⟨k, hk⟩)
      · exact ⟨0, Or.inl hφ⟩
      · exact ⟨k + 1, Or.inr ⟨k, Nat.lt_succ_self k, hk⟩⟩
  -- Each `T ∪ {σₖ | k < n}` is satisfied by a model of `T` with at least `n` elements.
  have heach : ∀ n, (Tn n).IsSatisfiable := by
    intro n
    obtain ⟨M, hM⟩ := h n
    have hcard : M ⊨ Sentence.cardGe L '' Set.Iio n := by
      rw [Theory.model_iff]
      rintro φ ⟨k, hk, rfl⟩
      rw [Sentence.realize_cardGe]
      exact le_trans (Nat.cast_le.mpr (le_of_lt (Set.mem_Iio.mp hk))) hM
    have : M ⊨ Tn n := Theory.model_union_iff.mpr ⟨M.is_model, hcard⟩
    exact Theory.Model.isSatisfiable M
  -- Compactness for the directed family.
  have hsat : (T ∪ L.infiniteTheory).IsSatisfiable := by
    rw [← hunion]
    exact (Theory.isSatisfiable_directed_union_iff hdir).mpr heach
  obtain ⟨N⟩ := hsat
  have hinf : Infinite N :=
    (model_infiniteTheory_iff L).mp (Theory.Model.mono N.is_model Set.subset_union_right)
  exact ⟨N.subtheoryModel Set.subset_union_left, hinf⟩
-- @endregion

-- @region completeness_theorem.finiteness_not_axiomatizable
-- @provenance independent
/-- **Finiteness is not first-order.** No set of sentences in the language of pure equality has
exactly the finite non-empty sets as its models. If `T` did, `Fin (n + 1)` would be a model of
`T` for each `n`, so `T` would have arbitrarily large finite models — and therefore an infinite
model (`exists_infinite_model`), which is not finite. -/
theorem finiteness_not_axiomatizable :
    ¬ ∃ T : Language.empty.Theory,
      ∀ (M : Type) [Language.empty.Structure M] [Nonempty M], M ⊨ T ↔ Finite M := by
  rintro ⟨T, hT⟩
  have large : ∀ n : ℕ, ∃ M : Theory.ModelType.{0, 0, 0} T, (n : Cardinal) ≤ #M := by
    intro n
    -- A set is a structure for the empty language in exactly one way.
    let _ : Language.empty.Structure (Fin (n + 1)) := Language.emptyStructure
    have : Fin (n + 1) ⊨ T := (hT (Fin (n + 1))).mpr inferInstance
    refine ⟨Theory.ModelType.of T (Fin (n + 1)), ?_⟩
    show (n : Cardinal) ≤ #(Fin (n + 1))
    rw [Cardinal.mk_fin]
    exact Nat.cast_le.mpr (Nat.le_succ n)
  obtain ⟨M, hM⟩ := exists_infinite_model T large
  have hfin : Finite M := (hT M).mp M.is_model
  exact not_finite M
-- @endregion

-- @region completeness_theorem.lowenheim_skolem
-- @provenance library
/-- **The Löwenheim–Skolem theorem**, upward and downward at once: if a theory `T` has an infinite
model, then it has a model of every infinite cardinality `κ` at least the number of symbols of
the language. For a countable language: models of *every* infinite size. This applies Mathlib's
`Theory.exists_model_card_eq`. -/
theorem lowenheim_skolem {L : Language.{u, v}} (T : L.Theory)
    (h : ∃ M : Theory.ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : Theory.ModelType.{u, v, w} T, #N = κ :=
  Theory.exists_model_card_eq h κ h1 h2
-- @endregion

-- @region completeness_theorem.models_iff_finset_models
-- @provenance library
/-- **Compactness for consequence:** `T ⊨ φ` exactly when some *finite* `T₀ ⊆ T` already has
`T₀ ⊨ φ`. This applies Mathlib's `Theory.models_iff_finset_models`. -/
theorem models_iff_finset_models {L : Language.{u, v}} {T : L.Theory} {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ ∃ T₀ : Finset L.Sentence, (T₀ : L.Theory) ⊆ T ∧ (T₀ : L.Theory) ⊨ᵇ φ :=
  Theory.models_iff_finset_models
-- @endregion

-- @region completeness_theorem.dlo_categorical
-- @provenance library
/-- **Cantor's back-and-forth theorem:** any two countable dense linear orders without endpoints
are isomorphic — the theory `dlo` is `ℵ₀`-categorical. This applies Mathlib's
`aleph0_categorical_dlo`. -/
theorem dlo_categorical : (ℵ₀).Categorical Language.order.dlo :=
  aleph0_categorical_dlo
-- @endregion

-- @region completeness_theorem.dlo_complete
-- @provenance library
/-- **The Łoś–Vaught test at work:** `dlo` has no finite models and is `ℵ₀`-categorical, so it is
complete — every sentence about orders is decided by the axioms of dense linear orders without
endpoints. In particular `(ℚ, <)` and `(ℝ, <)` satisfy exactly the same first-order sentences.
This applies Mathlib's `dlo_isComplete`. -/
theorem dlo_complete : Language.order.dlo.IsComplete :=
  dlo_isComplete
-- @endregion

end Lumenary.CompletenessTheorem
