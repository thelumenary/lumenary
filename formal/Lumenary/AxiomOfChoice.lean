/-
The Lumenary — formal mathematics
The axiom of choice: equivalent forms, Zorn's lemma at work, and Diaconescu's theorem.

Lean's logic *includes* a choice principle, the axiom `Classical.choice`, so in Lean the axiom of
choice is a theorem. To study it rather than just use it, we state two forms of it as
propositions — "every family of non-empty types has a choice function" and "every surjection has
a right inverse" — and prove them equivalent (`@provenance independent`). `#print axioms` shows
that these two proofs do not use `Classical.choice`: they really are implications between
principles.

Also proved here: every non-zero commutative ring has a maximal ideal, by Zorn's lemma
(Mathlib's `zorn_le_nonempty₀`) exactly as in the lesson; and **Diaconescu's theorem**: a choice
operator on sets of propositions, together with extensionality, yields the law of excluded
middle. (Core Lean's `Classical.em` is proved by this very argument.)

From Mathlib (`@provenance library`): choice functions from `Classical.choice`, right inverses
of surjections (`Function.surjInv`), the well-ordering theorem (`WellOrderingRel`), maximal ideals
(`Ideal.exists_maximal`) and bases of vector spaces (`Module.Basis.ofVectorSpace`).

Not formalised: the equivalence of choice with Zorn's lemma and the well-ordering theorem over
ZF, and independence results (Gödel, Cohen), which need a formal theory of models of set theory.
-/
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.SetTheory.Cardinal.Order

namespace Lumenary.AxiomOfChoice

universe u v

/-! ### Two forms of the axiom of choice, and their equivalence -/

-- @region axiom_of_choice.choice_functions
-- @provenance definition
/-- **The axiom of choice, as a proposition.** Every family `X i` (`i : ι`) of non-empty types has
a choice function `c` with `c i : X i` for every `i`. -/
def ChoiceFunctions : Prop :=
  ∀ (ι : Type u) (X : ι → Type u), (∀ i, Nonempty (X i)) → Nonempty (∀ i, X i)
-- @endregion

-- @region axiom_of_choice.surjections_split
-- @provenance definition
/-- **Every surjection splits:** for every surjective `p : α → β` there is a map `s : β → α` with
`p (s b) = b` for all `b` (a *section*, or right inverse, of `p`). -/
def SurjectionsSplit : Prop :=
  ∀ (α β : Type u) (p : α → β), Function.Surjective p → ∃ s : β → α, ∀ b, p (s b) = b
-- @endregion

-- @region axiom_of_choice.split_of_choice
-- @provenance independent
/-- **Choice ⇒ every surjection splits.** For each `b` the fibre `{a // p a = b}` is non-empty
because `p` is surjective; a choice function on the family of fibres is a section of `p`. -/
theorem split_of_choice : ChoiceFunctions.{u} → SurjectionsSplit.{u} := by
  intro hc α β p hp
  have hfib : ∀ b, Nonempty {a // p a = b} := fun b =>
    let ⟨a, ha⟩ := hp b
    ⟨⟨a, ha⟩⟩
  obtain ⟨c⟩ := hc β (fun b => {a // p a = b}) hfib
  exact ⟨fun b => (c b).1, fun b => (c b).2⟩
-- @endregion

-- @region axiom_of_choice.choice_of_split
-- @provenance independent
/-- **Every surjection splits ⇒ choice.** The projection from the disjoint union `Σ i, X i` onto
`ι` is surjective, because every `X i` is non-empty. A section `s` picks for each `i` a point
`s i` of the union lying over `i` — that is, an element of `X i`. -/
theorem choice_of_split : SurjectionsSplit.{u} → ChoiceFunctions.{u} := by
  intro hs ι X hX
  have hp : Function.Surjective (Sigma.fst : (Σ i, X i) → ι) := fun i =>
    let ⟨x⟩ := hX i
    ⟨⟨i, x⟩, rfl⟩
  obtain ⟨s, hs'⟩ := hs (Σ i, X i) ι Sigma.fst hp
  -- `(s i).2 : X (s i).1`, and `(s i).1 = i`: transport along that equation.
  exact ⟨fun i => hs' i ▸ (s i).2⟩
-- @endregion

-- @region axiom_of_choice.choice_holds
-- @provenance library
/-- **In Lean, choice is a theorem**, because Lean's logic includes the axiom `Classical.choice`
(from a proof that a type is non-empty, produce an element of it). -/
theorem choice_holds : ChoiceFunctions.{u} :=
  fun _ _ hX => ⟨fun i => Classical.choice (hX i)⟩
-- @endregion

-- @region axiom_of_choice.surj_inv
-- @provenance library
/-- Mathlib's version of "every surjection splits": `Function.surjInv` is a right inverse of any
surjection (`Function.rightInverse_surjInv`); it is built with `Classical.choose`. -/
theorem surj_inv {α : Type u} {β : Type v} {p : α → β} (hp : Function.Surjective p) :
    ∀ b, p (Function.surjInv hp b) = b :=
  Function.rightInverse_surjInv hp
-- @endregion

/-! ### The well-ordering theorem and Zorn's lemma at work -/

-- @region axiom_of_choice.well_ordering
-- @provenance library
/-- **The well-ordering theorem:** every type carries a well-order. Mathlib's `WellOrderingRel`
pulls back the well-order of the cardinals along an injection chosen with `Classical.choice`. -/
theorem well_ordering (α : Type u) : ∃ r : α → α → Prop, IsWellOrder α r :=
  ⟨WellOrderingRel, WellOrderingRel.isWellOrder⟩
-- @endregion

-- @region axiom_of_choice.exists_maximal_ideal
-- @provenance independent
/-- **Every non-zero commutative ring has a maximal ideal**, by Zorn's lemma as in the lesson.
Order the proper ideals by inclusion. A non-empty chain `c` has the upper bound `⋃ c` (in Lean,
`sSup c`), which is proper: if `1 ∈ sSup c` then `1` lies in a single member of the chain,
which would then be the whole ring. Zorn gives a maximal proper ideal. -/
theorem exists_maximal_ideal (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ M : Ideal R, M.IsMaximal := by
  let S : Set (Ideal R) := {I | I ≠ ⊤}
  have hbot : (⊥ : Ideal R) ∈ S := bot_ne_top
  have chains : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    intro htop
    have h1 : (1 : R) ∈ sSup c := by rw [htop]; exact Submodule.mem_top
    obtain ⟨I, hIc, h1I⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).mp h1
    exact hcS hIc ((Ideal.eq_top_iff_one I).mpr h1I)
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ S chains ⊥ hbot
  refine ⟨M, Ideal.isMaximal_def.mpr ⟨hM.prop, fun I hMI => ?_⟩⟩
  by_contra hI
  exact hMI.ne (hM.eq_of_le hI hMI.le)
-- @endregion

-- @region axiom_of_choice.exists_maximal_ideal_library
-- @provenance library
/-- The same theorem from Mathlib: `Ideal.exists_maximal` (Krull's theorem), proved there with
Zorn's lemma as well. -/
theorem exists_maximal_ideal_library (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ M : Ideal R, M.IsMaximal :=
  Ideal.exists_maximal R
-- @endregion

-- @region axiom_of_choice.exists_basis
-- @provenance library
/-- **Every vector space has a basis.** Mathlib's `Module.Basis.ofVectorSpace` extends the empty
linearly independent set to a maximal one using Zorn's lemma. This holds over any division
ring `K`, for spaces of any dimension. -/
theorem exists_basis (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V] :
    ∃ s : Set V, Nonempty (Module.Basis s K V) :=
  ⟨Module.Basis.ofVectorSpaceIndex K V, ⟨Module.Basis.ofVectorSpace K V⟩⟩
-- @endregion

/-! ### Diaconescu's theorem: choice implies excluded middle -/

-- @region axiom_of_choice.diaconescu
-- @provenance independent
/-- **Diaconescu's theorem.** Suppose `ε` chooses, from every non-empty collection `P` of
propositions, a member `ε P` of it. Then every proposition `p` is true or false.
Let `U = {x | x = True ∨ p}` and `V = {x | x = False ∨ p}`, both non-empty.
* If `ε U = True` and `ε V = False`, then `p` is false: if `p` held, `U` and `V` would be the
  same collection (extensionality: `funext`, `propext`), so `ε U = ε V`, i.e. `True = False`.
* Otherwise one of the choices came from the `∨ p` half, and `p` is true.
No excluded middle is used anywhere in the proof. -/
theorem diaconescu (ε : (Prop → Prop) → Prop) (hε : ∀ P : Prop → Prop, (∃ x, P x) → P (ε P))
    (p : Prop) : p ∨ ¬p := by
  let U : Prop → Prop := fun x => x = True ∨ p
  let V : Prop → Prop := fun x => x = False ∨ p
  have hU : U (ε U) := hε U ⟨True, Or.inl rfl⟩
  have hV : V (ε V) := hε V ⟨False, Or.inl rfl⟩
  -- If `p` holds, `U` and `V` are the same collection, so `ε` picks the same member.
  have same : p → ε U = ε V := fun hp =>
    congrArg ε (funext fun x => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩)
  rcases hU with hu | hp
  · rcases hV with hv | hp
    · right
      intro hp
      have htf : True = False := by
        have h := same hp
        rw [hu, hv] at h
        exact h
      exact Eq.mp htf True.intro
    · exact Or.inl hp
  · exact Or.inl hp
-- @endregion

-- @region axiom_of_choice.em_library
-- @provenance library
/-- Core Lean's **law of excluded middle**, `Classical.em`, is not an axiom: it is proved from
`Classical.choice`, `propext` and `funext` by Diaconescu's argument. -/
theorem em_library (p : Prop) : p ∨ ¬p :=
  Classical.em p
-- @endregion

end Lumenary.AxiomOfChoice
