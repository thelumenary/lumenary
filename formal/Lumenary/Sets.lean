/-
The Lumenary — formal mathematics
Sets: sets as predicates, the basic operations, and their first laws.

We build sets from scratch in core Lean 4: a set of `α`s is a property of `α`s, and `x ∈ A`
means "`x` has property `A`". This is the same representation Mathlib uses for its `Set`
(Mathlib analogue: `Set`, `Set.ext`, `Set.inter_subset_left`, …). Nothing here was checked
against Mathlib; the names are chosen to match so learners can move on to it later.

Convention: most theorems are stated with notation (`∈ ⊆ ∪ ∩ ᶜ ∅`) and proved by unfolding
what membership means, step by step.
-/

namespace Lumenary.Sets

universe u v

-- @region sets.set
-- @provenance definition
/-- A set of elements of `α` is a yes/no property of elements of `α`:
`A x` is the statement "`x` belongs to `A`". -/
def Set (α : Type u) : Type u := α → Prop
-- @endregion

variable {α : Type u} {β : Type v}

-- @region sets.inst_membership
-- @provenance definition
/-- `x ∈ A` means that `x` has the property `A`. -/
instance instMembership : Membership α (Set α) := ⟨fun A x => A x⟩
-- @endregion

-- @region sets.set_of
-- @provenance definition
/-- `setOf p` is the set of all `x` with property `p`. We write it `{x | p x}` (notation below). -/
def setOf (p : α → Prop) : Set α := p
-- @endregion

/-- Set-builder notation: `{x | p x}` is `setOf (fun x => p x)`. -/
scoped syntax "{" ident " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident => $p)

-- @region sets.mem_set_of
-- @provenance independent
/-- Belonging to `{x | p x}` means having property `p` — true by definition. -/
theorem mem_setOf (p : α → Prop) (a : α) : a ∈ {x | p x} ↔ p a := Iff.rfl
-- @endregion

-- @region sets.subset
-- @provenance definition
/-- `A ⊆ B` ("`A` is a subset of `B`"): every member of `A` is a member of `B`.
(Mathlib states this with a strict-implicit `∀ ⦃x⦄`; we keep `x` explicit for readability.) -/
def Subset (A B : Set α) : Prop := ∀ x, x ∈ A → x ∈ B
-- @endregion

-- @region sets.inst_has_subset
-- @provenance definition
/-- Lets us write `A ⊆ B` for `Subset A B`. -/
instance instHasSubset : HasSubset (Set α) := ⟨Subset⟩
-- @endregion

-- @region sets.union
-- @provenance definition
/-- The union `A ∪ B`: everything in `A` *or* in `B` (or both). -/
def union (A B : Set α) : Set α := {x | x ∈ A ∨ x ∈ B}
-- @endregion

-- @region sets.inst_union
-- @provenance definition
/-- Lets us write `A ∪ B`. -/
instance instUnion : Union (Set α) := ⟨union⟩
-- @endregion

-- @region sets.inter
-- @provenance definition
/-- The intersection `A ∩ B`: everything in `A` *and* in `B`. -/
def inter (A B : Set α) : Set α := {x | x ∈ A ∧ x ∈ B}
-- @endregion

-- @region sets.inst_inter
-- @provenance definition
/-- Lets us write `A ∩ B`. -/
instance instInter : Inter (Set α) := ⟨inter⟩
-- @endregion

-- @region sets.compl
-- @provenance definition
/-- The complement `Aᶜ`: everything (of type `α`) that is *not* in `A`. -/
def compl (A : Set α) : Set α := {x | x ∉ A}
-- @endregion

/-- `Aᶜ` is notation for `compl A` (Mathlib uses the same symbol). -/
scoped postfix:max "ᶜ" => compl

-- @region sets.empty
-- @provenance definition
/-- The empty set: nothing belongs to it. (The underscore in `_x` says the name is unused.) -/
def empty : Set α := {_x | False}
-- @endregion

-- @region sets.inst_empty_collection
-- @provenance definition
/-- Lets us write `∅` for the empty set. -/
instance instEmptyCollection : EmptyCollection (Set α) := ⟨empty⟩
-- @endregion

-- @region sets.univ
-- @provenance definition
/-- The universal set: everything of type `α` belongs to it. -/
def univ : Set α := {_x | True}
-- @endregion

-- @region sets.prod
-- @provenance definition
/-- The Cartesian product `A ×ˢ B`: all pairs `(a, b)` with `a ∈ A` and `b ∈ B`. -/
def prod (A : Set α) (B : Set β) : Set (α × β) := {p | p.1 ∈ A ∧ p.2 ∈ B}
-- @endregion

/-- `A ×ˢ B` is notation for `prod A B` (the same symbol Mathlib uses). -/
scoped infixr:82 " ×ˢ " => prod

/-! ### Unfolding membership

Each of these says what membership in a constructed set *means*. They are all true by
definition (`Iff.rfl`), but naming them makes later proofs easier to read. -/

-- @region sets.mem_union
-- @provenance independent
/-- `x ∈ A ∪ B` means `x ∈ A ∨ x ∈ B`. -/
theorem mem_union (x : α) (A B : Set α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl
-- @endregion

-- @region sets.mem_inter
-- @provenance independent
/-- `x ∈ A ∩ B` means `x ∈ A ∧ x ∈ B`. -/
theorem mem_inter (x : α) (A B : Set α) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl
-- @endregion

-- @region sets.mem_compl
-- @provenance independent
/-- `x ∈ Aᶜ` means `x ∉ A`. -/
theorem mem_compl (x : α) (A : Set α) : x ∈ Aᶜ ↔ x ∉ A := Iff.rfl
-- @endregion

/-! ### Equality and inclusion -/

-- @region sets.ext
-- @provenance independent
/-- **Extensionality.** Two sets are equal when they have exactly the same members.
This is where sets differ from lists: order and repetition are invisible.
The proof uses function extensionality and propositional extensionality, so the axiom
report lists `propext` and `Quot.sound` (from which `funext` is derived). -/
theorem ext {A B : Set α} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  funext fun x => propext (h x)
-- @endregion

-- @region sets.subset_refl
-- @provenance independent
/-- Every set is a subset of itself. -/
theorem subset_refl (A : Set α) : A ⊆ A := by
  intro x hx
  exact hx
-- @endregion

-- @region sets.subset_trans
-- @provenance independent
/-- Inclusion is transitive: if `A ⊆ B` and `B ⊆ C` then `A ⊆ C`. -/
theorem subset_trans {A B C : Set α} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hxA
  have hxB : x ∈ B := hAB x hxA
  exact hBC x hxB
-- @endregion

-- @region sets.empty_subset
-- @provenance independent
/-- The empty set is a subset of every set: there is no member of `∅` that could fail to be
in `A`. (Logicians say the statement is *vacuously* true.) -/
theorem empty_subset (A : Set α) : ∅ ⊆ A := by
  intro x hx
  -- `hx : x ∈ ∅` is a proof of `False`, and from `False` anything follows.
  exact False.elim hx
-- @endregion

-- @region sets.subset_univ
-- @provenance independent
/-- Every set is a subset of the universal set. -/
theorem subset_univ (A : Set α) : A ⊆ univ := by
  intro x _
  -- `x ∈ univ` is just `True`.
  trivial
-- @endregion

-- @region sets.inter_subset_left
-- @provenance independent
/-- `A ∩ B ⊆ A`: whatever is in both sets is, in particular, in the first one. -/
theorem inter_subset_left (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  -- `hx : x ∈ A ∧ x ∈ B`; keep the left half.
  exact hx.1
-- @endregion

-- @region sets.inter_subset_right
-- @provenance independent
/-- `A ∩ B ⊆ B`: whatever is in both sets is, in particular, in the second one. -/
theorem inter_subset_right (A B : Set α) : A ∩ B ⊆ B := by
  intro x hx
  -- `hx : x ∈ A ∧ x ∈ B`; keep the right half.
  exact hx.2
-- @endregion

-- @region sets.subset_union_left
-- @provenance independent
/-- `A ⊆ A ∪ B`: anything in `A` is in `A` or in `B`. -/
theorem subset_union_left (A B : Set α) : A ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx
-- @endregion

/-! ### Algebra of sets -/

-- @region sets.union_comm
-- @provenance independent
/-- Union is commutative: `A ∪ B = B ∪ A`. -/
theorem union_comm (A B : Set α) : A ∪ B = B ∪ A := by
  apply ext
  intro x
  constructor
  · intro h
    -- `h : x ∈ A ∨ x ∈ B`, and "or" can be swapped.
    exact Or.symm h
  · intro h
    exact Or.symm h
-- @endregion

-- @region sets.inter_comm
-- @provenance independent
/-- Intersection is commutative: `A ∩ B = B ∩ A`. -/
theorem inter_comm (A B : Set α) : A ∩ B = B ∩ A := by
  apply ext
  intro x
  constructor
  · intro h
    -- `h : x ∈ A ∧ x ∈ B`, and "and" can be swapped.
    exact And.symm h
  · intro h
    exact And.symm h
-- @endregion

-- @region sets.inter_union_distrib
-- @provenance independent
/-- Intersection distributes over union: `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
(Mathlib analogue: `Set.inter_union_distrib_left`.) -/
theorem inter_union_distrib (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ext
  intro x
  constructor
  · -- If `x ∈ A` and `x` is in `B` or `C`, look at which one.
    intro ⟨hA, hBC⟩
    cases hBC with
    | inl hB => exact Or.inl ⟨hA, hB⟩
    | inr hC => exact Or.inr ⟨hA, hC⟩
  · -- Either way round, `x ∈ A`, and `x` is in `B` or in `C`.
    intro h
    cases h with
    | inl hAB => exact ⟨hAB.1, Or.inl hAB.2⟩
    | inr hAC => exact ⟨hAC.1, Or.inr hAC.2⟩
-- @endregion

-- @region sets.compl_union
-- @provenance independent
/-- **De Morgan's law** for unions: `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`.
Not being in `A ∪ B` means being in neither set. This proof is constructive: it does not
use the law of excluded middle. -/
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply ext
  intro x
  constructor
  · intro h
    -- `h : ¬ (x ∈ A ∨ x ∈ B)`. If `x` were in `A`, it would be in `A ∪ B`; same for `B`.
    exact ⟨fun hA => h (Or.inl hA), fun hB => h (Or.inr hB)⟩
  · intro ⟨hnA, hnB⟩ hAB
    -- `x` is in `A` or in `B`, and both cases contradict what we know.
    cases hAB with
    | inl hA => exact hnA hA
    | inr hB => exact hnB hB
-- @endregion

-- @region sets.compl_inter
-- @provenance independent
/-- **De Morgan's law** for intersections: `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`.
The direction `(A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ` needs **classical logic**: knowing only that `x` is not in
both sets, we must still decide *which* set it misses. We use excluded middle
(`Classical.em`), so the axiom report for this theorem includes `Classical.choice`. -/
theorem compl_inter (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  apply ext
  intro x
  constructor
  · intro h
    -- `h : ¬ (x ∈ A ∧ x ∈ B)`. Either `x ∈ A` or not (excluded middle).
    cases Classical.em (x ∈ A) with
    | inl hA =>
      -- Then `x` cannot also be in `B`.
      exact Or.inr (fun hB => h ⟨hA, hB⟩)
    | inr hnA => exact Or.inl hnA
  · intro h ⟨hA, hB⟩
    cases h with
    | inl hnA => exact hnA hA
    | inr hnB => exact hnB hB
-- @endregion

/-! ### Products -/

-- @region sets.mem_prod
-- @provenance independent
/-- A pair `(a, b)` is in `A ×ˢ B` exactly when `a ∈ A` and `b ∈ B`. True by definition. -/
theorem mem_prod (a : α) (b : β) (A : Set α) (B : Set β) :
    (a, b) ∈ A ×ˢ B ↔ a ∈ A ∧ b ∈ B :=
  Iff.rfl
-- @endregion

end Lumenary.Sets
