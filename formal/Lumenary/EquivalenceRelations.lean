/-
The Lumenary — formal mathematics
Relations, equivalence relations and partitions.

A relation on a type `α` is a function `R : α → α → Prop`: `R a b` is the statement "a is
related to b". In set theory a relation is a set of ordered pairs; a yes-or-no question about
pairs carries exactly the same information. Subsets of `α` are represented the same way, as
predicates `α → Prop` (core Lean has no `Set` type; Mathlib's `Set α` is defined to be exactly
`α → Prop`). Core Lean provides the structure `Equivalence R` with fields `refl`, `symm` and
`trans`; everything else here is proved from scratch, with core Lean only.

What is formalised: the three properties and examples and non-examples of each; why symmetry and
transitivity do not imply reflexivity; that two equivalence classes are equal or disjoint; that
the classes form a partition and that every partition comes from exactly one equivalence relation
(both round trips); and that "same remainder on division by n" has exactly n classes. Mathlib's
general versions: `Setoid`, `Quotient`, `Setoid.IsPartition`, `Setoid.classes` and `Int.ModEq`.
-/

namespace Lumenary.EquivalenceRelations

/-! ### The three properties -/

-- @region equivalence_relations.reflexive
-- @provenance definition
/-- A relation is **reflexive** if every element is related to itself: `a R a` for all `a`. -/
def Reflexive {α : Type} (R : α → α → Prop) : Prop := ∀ a, R a a
-- @endregion

-- @region equivalence_relations.symmetric
-- @provenance definition
/-- A relation is **symmetric** if `a R b` always implies `b R a`. -/
def Symmetric {α : Type} (R : α → α → Prop) : Prop := ∀ a b, R a b → R b a
-- @endregion

-- @region equivalence_relations.transitive
-- @provenance definition
/-- A relation is **transitive** if `a R b` and `b R c` always imply `a R c`. -/
def Transitive {α : Type} (R : α → α → Prop) : Prop := ∀ a b c, R a b → R b c → R a c
-- @endregion

-- @region equivalence_relations.equivalence_iff
-- @provenance independent
/-- Core Lean's `Equivalence R` is exactly our definition: reflexive, symmetric and transitive. -/
theorem equivalence_iff {α : Type} (R : α → α → Prop) :
    Equivalence R ↔ Reflexive R ∧ Symmetric R ∧ Transitive R := by
  constructor
  · intro h
    exact ⟨h.refl, fun _ _ hab => h.symm hab, fun _ _ _ hab hbc => h.trans hab hbc⟩
  · intro ⟨hr, hs, ht⟩
    exact ⟨hr, fun {a b} hab => hs a b hab, fun {a b c} hab hbc => ht a b c hab hbc⟩
-- @endregion

/-! ### Examples and non-examples -/

-- @region equivalence_relations.table_rel
-- @provenance definition
/-- A relation on the three-element set `{0, 1, 2}`, given as a list of ordered pairs:
`{(0,0), (1,1), (2,2), (0,1), (1,0)}`. `a` is related to `b` when the list contains `(a, b)`. -/
def tableRel (a b : Fin 3) : Prop :=
  [(0, 0), (1, 1), (2, 2), (0, 1), (1, 0)].contains (a, b) = true
-- @endregion

-- @region equivalence_relations.table_example
-- @provenance independent
/-- `tableRel` is an equivalence relation (its classes are `{0, 1}` and `{2}`). Lean checks all
three properties by running through every case: `3` cases for reflexivity, `9` for symmetry and
`27` for transitivity. On a finite set, checking every case *is* a proof. -/
theorem table_example : Reflexive tableRel ∧ Symmetric tableRel ∧ Transitive tableRel := by
  unfold Reflexive Symmetric Transitive tableRel
  decide
-- @endregion

-- @region equivalence_relations.lt_not_symmetric
-- @provenance independent
/-- "Is less than" is not symmetric. One counterexample suffices: `0 < 1` but not `1 < 0`. -/
theorem lt_not_symmetric : ¬ Symmetric (fun a b : Int => a < b) := by
  intro h
  have h10 : (1 : Int) < 0 := h 0 1 (by decide)
  exact absurd h10 (by decide)
-- @endregion

-- @region equivalence_relations.lt_transitive
-- @provenance independent
/-- "Is less than" is transitive: from `a < b` and `b < c` we get `a < c`. -/
theorem lt_transitive : Transitive (fun a b : Int => a < b) := by
  intro a b c hab hbc
  omega
-- @endregion

-- @region equivalence_relations.near
-- @provenance definition
/-- "Differ by at most 1": `a` and `b` are *near* if `|a − b| ≤ 1`. -/
def Near (a b : Int) : Prop := a - b ≤ 1 ∧ b - a ≤ 1
-- @endregion

-- @region equivalence_relations.near_reflexive_symmetric
-- @provenance independent
/-- "Differ by at most 1" is reflexive and symmetric … -/
theorem near_reflexive_symmetric : Reflexive Near ∧ Symmetric Near := by
  constructor
  · intro a
    show a - a ≤ 1 ∧ a - a ≤ 1
    omega
  · intro a b ⟨h1, h2⟩
    exact ⟨h2, h1⟩
-- @endregion

-- @region equivalence_relations.near_not_transitive
-- @provenance independent
/-- … but not transitive: `0` is near `1` and `1` is near `2`, yet `0` is not near `2`.
So "differ by at most 1" is **not** an equivalence relation. -/
theorem near_not_transitive : ¬ Transitive Near := by
  intro h
  have h02 : Near 0 2 := h 0 1 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  exact absurd h02.2 (by decide)
-- @endregion

/-! ### Symmetry and transitivity do not give reflexivity -/

-- @region equivalence_relations.symm_trans_not_refl
-- @provenance independent
/-- A tempting false "proof": from `a R b`, symmetry gives `b R a`, and transitivity gives `a R a`.
The flaw is the first step — there may be no `b` with `a R b` at all. Here is a relation on the
natural numbers that is symmetric and transitive but not reflexive: `a R b` means `a = 0 ∧ b = 0`.
The number `1` is related to nothing, not even to itself. -/
theorem symm_trans_not_refl :
    ∃ R : Nat → Nat → Prop, Symmetric R ∧ Transitive R ∧ ¬ Reflexive R := by
  refine ⟨fun a b => a = 0 ∧ b = 0, ?_, ?_, ?_⟩
  · intro a b ⟨ha, hb⟩
    exact ⟨hb, ha⟩
  · intro a b c ⟨ha, _⟩ ⟨_, hc⟩
    exact ⟨ha, hc⟩
  · intro h
    exact absurd (h 1).1 (by decide)
-- @endregion

-- @region equivalence_relations.refl_of_symm_trans
-- @provenance independent
/-- The tempting argument *does* work when every element is related to **something**:
pick `b` with `a R b`; symmetry gives `b R a`; transitivity gives `a R a`. -/
theorem refl_of_symm_trans {α : Type} (R : α → α → Prop) (hs : Symmetric R) (ht : Transitive R)
    (hsome : ∀ a, ∃ b, R a b) : Reflexive R := by
  intro a
  obtain ⟨b, hab⟩ := hsome a
  exact ht a b a hab (hs a b hab)
-- @endregion

/-! ### Equivalence classes -/

-- @region equivalence_relations.cls
-- @provenance definition
/-- The **equivalence class** of `a`: the set `[a] = {x | x R a}`, represented as a predicate.
`cls R a x` says "x belongs to the class of a". -/
def cls {α : Type} (R : α → α → Prop) (a : α) : α → Prop := fun x => R x a
-- @endregion

-- @region equivalence_relations.mem_cls_self
-- @provenance independent
/-- Every element belongs to its own class (by reflexivity), so classes are never empty. -/
theorem mem_cls_self {α : Type} {R : α → α → Prop} (h : Equivalence R) (a : α) : cls R a a :=
  h.refl a
-- @endregion

-- @region equivalence_relations.cls_eq_of_rel
-- @provenance independent
/-- If `a R b` then `[a] = [b]`. If `x R a`, then `x R b` by transitivity; if `x R b`, then
`b R a` (symmetry) and transitivity give `x R a`. Two sets with the same members are equal
(`funext` and `propext` express this in Lean). -/
theorem cls_eq_of_rel {α : Type} {R : α → α → Prop} (h : Equivalence R) {a b : α} (hab : R a b) :
    cls R a = cls R b := by
  funext x
  apply propext
  constructor
  · intro hxa
    exact h.trans hxa hab
  · intro hxb
    exact h.trans hxb (h.symm hab)
-- @endregion

-- @region equivalence_relations.cls_eq_iff
-- @provenance independent
/-- `[a] = [b]` exactly when `a R b`. (For "only if": `a ∈ [a] = [b]`, so `a R b`.) -/
theorem cls_eq_iff {α : Type} {R : α → α → Prop} (h : Equivalence R) (a b : α) :
    cls R a = cls R b ↔ R a b := by
  constructor
  · intro e
    have ha : cls R a a := mem_cls_self h a
    rw [e] at ha
    exact ha
  · exact cls_eq_of_rel h
-- @endregion

-- @region equivalence_relations.cls_eq_or_disjoint
-- @provenance independent
/-- **Two equivalence classes are either equal or disjoint.** Either `a R b`, and then
`[a] = [b]`; or not, and then no `x` can lie in both — otherwise `a R x` (symmetry) and `x R b`
would give `a R b` (transitivity). The case split uses the law of excluded middle. -/
theorem cls_eq_or_disjoint {α : Type} {R : α → α → Prop} (h : Equivalence R) (a b : α) :
    cls R a = cls R b ∨ ∀ x, ¬ (cls R a x ∧ cls R b x) := by
  cases Classical.em (R a b) with
  | inl hab => exact Or.inl (cls_eq_of_rel h hab)
  | inr hnot =>
    right
    intro x ⟨hxa, hxb⟩
    exact hnot (h.trans (h.symm hxa) hxb)
-- @endregion

/-! ### Partitions -/

-- @region equivalence_relations.is_partition
-- @provenance definition
/-- A family `P` of subsets of `α` is a **partition** of `α` if every block is non-empty, every
element lies in some block, and two blocks that share an element are equal (equivalently:
different blocks are disjoint). Here a subset is a predicate `B : α → Prop`, and `P B` says
"`B` is one of the blocks". -/
structure IsPartition {α : Type} (P : (α → Prop) → Prop) : Prop where
  nonempty : ∀ B, P B → ∃ x, B x
  covers : ∀ x, ∃ B, P B ∧ B x
  disjoint : ∀ B C, P B → P C → (∃ x, B x ∧ C x) → B = C
-- @endregion

-- @region equivalence_relations.classes
-- @provenance definition
/-- The family of all equivalence classes of `R`: `B` belongs to it when `B = [a]` for some `a`. -/
def classes {α : Type} (R : α → α → Prop) : (α → Prop) → Prop := fun B => ∃ a, B = cls R a
-- @endregion

-- @region equivalence_relations.classes_partition
-- @provenance independent
/-- **The equivalence classes of an equivalence relation form a partition.** Classes are non-empty
and cover everything because `a ∈ [a]`; two classes sharing an element `x` are equal because
`x R a` and `x R b` give `a R b`, so `[a] = [b]`. -/
theorem classes_partition {α : Type} {R : α → α → Prop} (h : Equivalence R) :
    IsPartition (classes R) where
  nonempty := by
    intro B ⟨a, hB⟩
    exact ⟨a, hB ▸ mem_cls_self h a⟩
  covers := fun x => ⟨cls R x, ⟨x, rfl⟩, mem_cls_self h x⟩
  disjoint := by
    intro B C ⟨a, hB⟩ ⟨b, hC⟩ ⟨x, hxB, hxC⟩
    rw [hB] at hxB
    rw [hC] at hxC
    rw [hB, hC]
    exact cls_eq_of_rel h (h.trans (h.symm hxB) hxC)
-- @endregion

-- @region equivalence_relations.same_block
-- @provenance definition
/-- The relation defined by a partition: `a` and `b` are related when they lie in the same block. -/
def SameBlock {α : Type} (P : (α → Prop) → Prop) (a b : α) : Prop := ∃ B, P B ∧ B a ∧ B b
-- @endregion

-- @region equivalence_relations.same_block_equivalence
-- @provenance independent
/-- **"Lie in the same block" is an equivalence relation.** Reflexive: every element lies in
some block. Symmetric: obvious. Transitive: if `a, b ∈ B` and `b, c ∈ C`, then `B` and `C` share
`b`, so `B = C`, and `a, c` lie in the same block. -/
theorem same_block_equivalence {α : Type} {P : (α → Prop) → Prop} (hP : IsPartition P) :
    Equivalence (SameBlock P) where
  refl := by
    intro a
    obtain ⟨B, hB, ha⟩ := hP.covers a
    exact ⟨B, hB, ha, ha⟩
  symm := by
    intro a b ⟨B, hB, ha, hb⟩
    exact ⟨B, hB, hb, ha⟩
  trans := by
    intro a b c ⟨B, hB, ha, hb⟩ ⟨C, hC, hb', hc⟩
    have hBC : B = C := hP.disjoint B C hB hC ⟨b, hb, hb'⟩
    rw [← hBC] at hc
    exact ⟨B, hB, ha, hc⟩
-- @endregion

-- @region equivalence_relations.same_block_classes
-- @provenance independent
/-- Round trip 1: start with an equivalence relation `R`, form its classes, and ask "same class?".
You get `R` back: `a` and `b` lie in a common class exactly when `a R b`. -/
theorem same_block_classes {α : Type} {R : α → α → Prop} (h : Equivalence R) (a b : α) :
    SameBlock (classes R) a b ↔ R a b := by
  constructor
  · intro ⟨B, ⟨c, hB⟩, ha, hb⟩
    rw [hB] at ha hb
    exact h.trans ha (h.symm hb)
  · intro hab
    exact ⟨cls R b, ⟨b, rfl⟩, hab, mem_cls_self h b⟩
-- @endregion

-- @region equivalence_relations.classes_same_block
-- @provenance independent
/-- Round trip 2: start with a partition `P`, form the relation "same block", and take its
classes. You get exactly the blocks of `P` back. Together with round trip 1 this says that
equivalence relations and partitions are two descriptions of the same thing, and that each
partition comes from exactly one equivalence relation. -/
theorem classes_same_block {α : Type} {P : (α → Prop) → Prop} (hP : IsPartition P)
    (B : α → Prop) : classes (SameBlock P) B ↔ P B := by
  constructor
  · intro ⟨a, hB⟩
    obtain ⟨C, hC, haC⟩ := hP.covers a
    -- The class of `a` is the block `C` containing `a`.
    have hcls : cls (SameBlock P) a = C := by
      funext x
      apply propext
      constructor
      · intro ⟨D, hD, hxD, haD⟩
        have hDC : D = C := hP.disjoint D C hD hC ⟨a, haD, haC⟩
        rw [← hDC]
        exact hxD
      · intro hxC
        exact ⟨C, hC, hxC, haC⟩
    rw [hB, hcls]
    exact hC
  · intro hB
    obtain ⟨a, haB⟩ := hP.nonempty B hB
    refine ⟨a, ?_⟩
    funext x
    apply propext
    constructor
    · intro hxB
      exact ⟨B, hB, hxB, haB⟩
    · intro ⟨D, hD, hxD, haD⟩
      have hDB : D = B := hP.disjoint D B hD hB ⟨a, haD, haB⟩
      rw [← hDB]
      exact hxD
-- @endregion

/-! ### "Same output" and "same remainder" -/

-- @region equivalence_relations.same_output_equivalence
-- @provenance independent
/-- For any function `f`, "has the same output under `f`" is an equivalence relation. "Same
remainder", "same colour", "same birth month" and "same last digit" are all of this kind. -/
theorem same_output_equivalence {α β : Type} (f : α → β) :
    Equivalence (fun a b => f a = f b) where
  refl := fun _ => rfl
  symm := fun hab => hab.symm
  trans := fun hab hbc => hab.trans hbc
-- @endregion

-- @region equivalence_relations.same_remainder
-- @provenance definition
/-- `a` and `b` have the **same remainder** on division by `n`. (Lean's `%` on `Int` gives the
remainder between `0` and `n − 1` for `n > 0`, also for negative `a`: `-1 % 3 = 2`.) -/
def SameRemainder (n a b : Int) : Prop := a % n = b % n
-- @endregion

-- @region equivalence_relations.same_remainder_equivalence
-- @provenance independent
/-- "Same remainder on division by `n`" is an equivalence relation: it is "same output" for the
function `a ↦ a % n`. -/
theorem same_remainder_equivalence (n : Int) : Equivalence (SameRemainder n) :=
  same_output_equivalence (fun a => a % n)
-- @endregion

-- @region equivalence_relations.remainder_examples
-- @provenance independent
/-- Examples, checked by calculation: `17` and `2` have the same remainder on division by `3`;
so do `-1` and `5` (remainder `2`); but `4` and `6` do not. -/
theorem remainder_examples :
    SameRemainder 3 17 2 ∧ SameRemainder 3 (-1) 5 ∧ ¬ SameRemainder 3 4 6 := by
  unfold SameRemainder
  decide
-- @endregion

-- @region equivalence_relations.exactly_n_classes
-- @provenance independent
/-- **"Same remainder on division by `n`" has exactly `n` classes** (for `n > 0`): every integer
`a` is related to exactly one of `0, 1, …, n − 1`, namely its remainder `r = a % n`. So the
classes are `[0], [1], …, [n − 1]`, and these are all different. -/
theorem exactly_n_classes (n : Int) (hn : 0 < n) (a : Int) :
    ∃ r, 0 ≤ r ∧ r < n ∧ SameRemainder n a r ∧
      ∀ s, 0 ≤ s → s < n → SameRemainder n a s → s = r := by
  refine ⟨a % n, Int.emod_nonneg a (by omega), Int.emod_lt_of_pos a hn, ?_, ?_⟩
  · -- `a % n` has the same remainder as `a`: taking the remainder twice changes nothing.
    show a % n = a % n % n
    exact (Int.emod_emod_of_dvd a (Int.dvd_refl n)).symm
  · intro s hs0 hsn hsame
    -- A number between `0` and `n - 1` is its own remainder.
    have hss : s % n = s := Int.emod_eq_of_lt hs0 hsn
    show s = a % n
    rw [hsame, hss]
-- @endregion

end Lumenary.EquivalenceRelations
