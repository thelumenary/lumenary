/-
The Lumenary — formal mathematics
Russell's paradox and why sets need axioms.

Proved here (`@provenance independent`): the heart of the paradox is a theorem of pure logic —
for *any* relation `E` on *any* collection, nothing `r` satisfies `x E r ↔ ¬ (x E x)` for all `x`.
From it: there is no such barber; naive comprehension ("every property defines a set") is
inconsistent; in Mathlib's model of ZFC (`ZFSet`), the separation axiom produces, inside any set
`A`, a Russell set `{x ∈ A | x ∉ x}` that is *not* an element of `A`, so no set contains every set;
and Cantor's theorem is the same diagonal argument. The key logical step, `¬ (p ↔ ¬ p)`, is
constructive: no law of excluded middle is used.

From Mathlib (`@provenance library`): `iff_not_self` (core Lean) and `ZFSet.mem_irrefl` (no set is
a member of itself — a consequence of the axiom of foundation, which our proofs never use).
In Lean's own type theory `x ∈ x` cannot even be written for `x : Set α`: a set of elements of
type `α` has type `Set α`, not `α`. That is a descendant of Russell's own remedy, the theory of
types.
-/
import Mathlib.SetTheory.ZFC.Basic

namespace Lumenary.RussellParadox

/-! ### The logical core -/

-- @region russell_paradox.iff_not_self
-- @provenance independent
/-- **No statement is equivalent to its own negation.** If `p ↔ ¬p`, then assuming `p` gives `¬p`,
so `p` is refuted; but then `¬p` gives `p`. This proof is constructive. -/
theorem not_iff_not_self (p : Prop) : ¬ (p ↔ ¬ p) := by
  intro h
  have hnp : ¬ p := fun hp => h.mp hp hp
  exact hnp (h.mpr hnp)
-- @endregion

-- @region russell_paradox.iff_not_self_library
-- @provenance library
/-- The same fact in core Lean: `iff_not_self`. -/
theorem not_iff_not_self_library (p : Prop) : ¬ (p ↔ ¬ p) := iff_not_self
-- @endregion

-- @region russell_paradox.no_russell_relation
-- @provenance independent
/-- **Russell's theorem, in pure logic.** For any relation `E` on any type, there is no `r` whose
"members" are exactly the things that are not members of themselves: taking `x = r` would give
`r E r ↔ ¬ (r E r)`. -/
theorem no_russell_relation {α : Type*} (E : α → α → Prop) :
    ¬ ∃ r, ∀ x, E x r ↔ ¬ E x x := by
  rintro ⟨r, hr⟩
  exact not_iff_not_self (E r r) (hr r)
-- @endregion

-- @region russell_paradox.no_barber
-- @provenance independent
/-- **The barber.** In no village is there a barber who shaves exactly those villagers who do not
shave themselves. This is `no_russell_relation` for the relation "`y` shaves `x`". The barber is not
a paradox: it simply proves that such a barber does not exist. -/
theorem no_barber {Person : Type*} (shaves : Person → Person → Prop) :
    ¬ ∃ b, ∀ p, shaves b p ↔ ¬ shaves p p :=
  no_russell_relation (fun x y => shaves y x)
-- @endregion

-- @region russell_paradox.naive_comprehension_inconsistent
-- @provenance independent
/-- **Naive comprehension is inconsistent.** Suppose a membership relation `mem` had the property
that every predicate `P` is the membership predicate of some "set" `s`. Applying this to
`P x := ¬ mem x x` produces a Russell set, which `no_russell_relation` forbids. -/
theorem naive_comprehension_inconsistent {α : Type*} (mem : α → α → Prop)
    (comprehension : ∀ P : α → Prop, ∃ s, ∀ x, mem x s ↔ P x) : False :=
  no_russell_relation mem (comprehension fun x => ¬ mem x x)
-- @endregion

/-! ### Separation in ZFC -/

-- @region russell_paradox.russell_sep_not_mem
-- @provenance independent
/-- **Separation blocks the paradox.** In Mathlib's model of ZFC, for every set `A` the Russell
set *inside `A`*, `R = {x ∈ A | x ∉ x}` (built with the separation axiom `ZFSet.sep`), is not an
element of `A`. If it were, then `R ∈ R ↔ (R ∈ A ∧ R ∉ R) ↔ R ∉ R`. Only `ZFSet.mem_sep` is used —
not the axiom of foundation. -/
theorem russell_sep_not_mem (A : ZFSet) : ZFSet.sep (fun x => x ∉ x) A ∉ A := by
  intro hA
  -- `h : R ∈ R ↔ R ∈ A ∧ R ∉ R`, where `R` is the Russell set inside `A`.
  have h := ZFSet.mem_sep (p := fun x => x ∉ x) (x := A) (y := ZFSet.sep (fun x => x ∉ x) A)
  exact not_iff_not_self _ ⟨fun hRR => (h.mp hRR).2, fun hRR => h.mpr ⟨hA, hRR⟩⟩
-- @endregion

-- @region russell_paradox.no_universal_set
-- @provenance independent
/-- **There is no set of all sets.** If `U` contained every set, it would contain its own Russell
set `{x ∈ U | x ∉ x}`, contradicting `russell_sep_not_mem`. -/
theorem no_universal_set : ¬ ∃ U : ZFSet, ∀ x, x ∈ U := by
  rintro ⟨U, hU⟩
  exact russell_sep_not_mem U (hU _)
-- @endregion

-- @region russell_paradox.mem_irrefl
-- @provenance library
/-- In ZFC no set is a member of itself — Mathlib's `ZFSet.mem_irrefl`, which comes from the axiom
of foundation (Mathlib proves that membership of `ZFSet`s is well-founded). The paradox is *not*
avoided this way: `russell_sep_not_mem` never used this fact. -/
theorem mem_irrefl (x : ZFSet) : x ∉ x := ZFSet.mem_irrefl x
-- @endregion

-- @region russell_paradox.russell_sep_eq_self
-- @provenance independent
/-- With foundation, the Russell set inside `A` is `A` itself: every element `x` of `A` satisfies
`x ∉ x`. So `russell_sep_not_mem` then says simply `A ∉ A`. -/
theorem russell_sep_eq_self (A : ZFSet) : ZFSet.sep (fun x => x ∉ x) A = A := by
  ext x
  rw [ZFSet.mem_sep]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_irrefl x⟩⟩
-- @endregion

/-! ### The same argument as Cantor's -/

-- @region russell_paradox.cantor_of_russell
-- @provenance independent
/-- **Cantor's theorem is Russell's argument in disguise.** For `f : α → Set α`, read `x ∈ f y` as
"`x` is a member of `y`". A surjective `f` would hit the diagonal set `{x | x ∉ f x}` at some `r`,
and that `r` would be a Russell element for this relation. -/
theorem cantor_of_russell {α : Type*} (f : α → Set α) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨r, hr⟩ := hf {x | x ∉ f x}
  apply no_russell_relation (fun x y => x ∈ f y)
  refine ⟨r, fun x => ?_⟩
  rw [hr]
  rfl
-- @endregion

/-! ### Types: a universe one level up -/

-- @region russell_paradox.typed_universe
-- @provenance independent
/-- **In type theory a "set of everything" is harmless.** For each type `α` there is a set
containing every element of `α` — `Set.univ` — but it has type `Set α`, so it is not itself an
element of `α`, and the question "is it a member of itself?" cannot be asked. -/
theorem typed_universe (α : Type*) : ∃ U : Set α, ∀ x : α, x ∈ U :=
  ⟨Set.univ, fun _ => trivial⟩
-- @endregion

end Lumenary.RussellParadox
