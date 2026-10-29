/-
The Lumenary — formal mathematics
First-order logic: signatures, terms and formulas, structures and satisfaction, a natural
deduction system, the soundness theorem, and invariance of truth under isomorphism.

This file builds a small but complete first-order logic from scratch, so that every definition
of the lesson can be read in Lean:
* syntax (`Signature`, `Term`, `Formula`), with variables written as de Bruijn indices: inside a
  quantifier, variable `0` is the one just bound, and the others shift up by one;
* substitution of terms for variables, and the **substitution lemma** relating it to semantics;
* structures, environments and satisfaction (`Formula.Realize`), unwinding the quantifiers
  exactly as in the lesson;
* natural deduction (`Derivable`), with rules for `⊥, →, ∧, ∨, ∀, ∃, =` and classical reductio;
* **soundness**: everything derivable is true in every structure (proved here, `independent`);
* examples: the group axioms hold in `(ℤ, +, 0, −)`, `∀x φ → ∃x φ` is derivable (structures are
  non-empty), `∃x P(x) → ∀x P(x)` is *not* derivable (a two-element countermodel plus soundness),
  and `(ℕ, <)` is not isomorphic to `(ℤ, <)` because isomorphic structures satisfy the same
  sentences (proved here).

Gödel's completeness theorem (the converse of soundness) is stated in the lesson but not proved:
see the Lumenary lesson on completeness. Mathlib has its own first-order logic
(`FirstOrder.Language`, `BoundedFormula`, `Sentence.Realize`), with isomorphism invariance
(`FirstOrder.Language.StrongHomClass.realize_sentence`, cited below); at this version it has no
proof calculus, which is one reason we build ours here.
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Int.Defs

namespace Lumenary.FirstOrderLogic

universe u v

/-! ### Syntax -/

-- @region first_order_logic.signature
-- @provenance definition
/-- A **signature** lists the non-logical symbols: for each arity `n`, the function symbols
`Func n` and the relation symbols `Rel n`. Constants are function symbols of arity `0`. -/
structure Signature where
  /-- Function symbols of each arity. -/
  Func : ℕ → Type
  /-- Relation symbols of each arity. -/
  Rel : ℕ → Type
-- @endregion

-- @region first_order_logic.term
-- @provenance definition
/-- **Terms** are built from variables `var i` by applying function symbols: if `f` has arity
`n` and `t₀, …, tₙ₋₁` are terms, so is `f(t₀, …, tₙ₋₁)`. -/
inductive Term (L : Signature) : Type
  | var : ℕ → Term L
  | func : {n : ℕ} → L.Func n → (Fin n → Term L) → Term L
-- @endregion

-- @region first_order_logic.formula
-- @provenance definition
/-- **Formulas**: `⊥`, equations `t = u`, atomic formulas `R(t₀, …, tₙ₋₁)`, the connectives
`→, ∧, ∨`, and the quantifiers `∀, ∃`. A quantifier binds variable `0` of its body (de Bruijn
indices), so `all (rel R ![var 0, var 1])` is `∀x R(x, y)` where `y` is the free variable `0`
outside the quantifier. -/
inductive Formula (L : Signature) : Type
  | falsum : Formula L
  | eq : Term L → Term L → Formula L
  | rel : {n : ℕ} → L.Rel n → (Fin n → Term L) → Formula L
  | imp : Formula L → Formula L → Formula L
  | and : Formula L → Formula L → Formula L
  | or : Formula L → Formula L → Formula L
  | all : Formula L → Formula L
  | ex : Formula L → Formula L
-- @endregion

variable {L : Signature}

-- @region first_order_logic.formula_not
-- @provenance definition
/-- Negation is an abbreviation: `¬φ` is `φ → ⊥`. -/
def Formula.not (φ : Formula L) : Formula L := .imp φ .falsum
-- @endregion

/-! ### Substitution -/

-- @region first_order_logic.term_subst
-- @provenance definition
/-- Simultaneous substitution in a term: replace each variable `var i` by the term `σ i`. -/
def Term.subst (σ : ℕ → Term L) : Term L → Term L
  | .var i => σ i
  | .func f ts => .func f (fun i => (ts i).subst σ)
-- @endregion

-- @region first_order_logic.term_shift
-- @provenance definition
/-- Shift every variable up by one (`var i ↦ var (i + 1)`), to make room for a new bound
variable `0`. -/
def Term.shift (t : Term L) : Term L := t.subst (fun i => .var (i + 1))
-- @endregion

-- @region first_order_logic.up
-- @provenance definition
/-- Moving a substitution under a quantifier: the newly bound variable `0` stays itself, and the
terms substituted for the other variables are shifted so that they do not get captured. -/
def up (σ : ℕ → Term L) : ℕ → Term L
  | 0 => .var 0
  | i + 1 => (σ i).shift
-- @endregion

-- @region first_order_logic.inst
-- @provenance definition
/-- The substitution `φ(t)`: put the term `t` for the bound variable `0` and shift the other
variables down (they were one level deeper under the quantifier). -/
def inst (t : Term L) : ℕ → Term L
  | 0 => t
  | i + 1 => .var i
-- @endregion

-- @region first_order_logic.formula_subst
-- @provenance definition
/-- Capture-avoiding substitution in a formula. Under a quantifier the substitution is
replaced by `up σ`. -/
def Formula.subst : (ℕ → Term L) → Formula L → Formula L
  | _, .falsum => .falsum
  | σ, .eq t u => .eq (t.subst σ) (u.subst σ)
  | σ, .rel R ts => .rel R (fun i => (ts i).subst σ)
  | σ, .imp φ ψ => .imp (φ.subst σ) (ψ.subst σ)
  | σ, .and φ ψ => .and (φ.subst σ) (ψ.subst σ)
  | σ, .or φ ψ => .or (φ.subst σ) (ψ.subst σ)
  | σ, .all φ => .all (φ.subst (up σ))
  | σ, .ex φ => .ex (φ.subst (up σ))
-- @endregion

-- @region first_order_logic.formula_shift
-- @provenance definition
/-- Shift all free variables of a formula up by one. -/
def Formula.shift (φ : Formula L) : Formula L := φ.subst (fun i => .var (i + 1))
-- @endregion

/-! ### Semantics -/

-- @region first_order_logic.structure
-- @provenance definition
/-- A **structure** for a signature: a domain `M` (a type) with an interpretation of each
function symbol as a function `Mⁿ → M` and of each relation symbol as a relation on `Mⁿ`.
Non-emptiness is not a field: it is automatic wherever an environment `ρ : ℕ → M` exists. -/
structure Structure (L : Signature) (M : Type u) where
  /-- Interpretation of function symbols. -/
  funMap : {n : ℕ} → L.Func n → (Fin n → M) → M
  /-- Interpretation of relation symbols. -/
  relMap : {n : ℕ} → L.Rel n → (Fin n → M) → Prop
-- @endregion

-- @region first_order_logic.cons
-- @provenance definition
/-- Extend an environment (an assignment `ρ` of elements to variables) by a value `a` for a
newly bound variable `0`; the old variable `i` becomes `i + 1`. -/
def cons {M : Type u} (a : M) (ρ : ℕ → M) : ℕ → M
  | 0 => a
  | i + 1 => ρ i
-- @endregion

-- @region first_order_logic.term_eval
-- @provenance definition
/-- The value of a term in a structure `S`, given values `ρ i` for the variables. -/
def Term.eval {M : Type u} (S : Structure L M) (ρ : ℕ → M) : Term L → M
  | .var i => ρ i
  | .func f ts => S.funMap f (fun i => (ts i).eval S ρ)
-- @endregion

-- @region first_order_logic.realize
-- @provenance definition
/-- **Satisfaction** `M ⊨ φ[ρ]`: the formula `φ` is true in the structure `S` when its free
variables take the values `ρ`. This is Tarski's definition, clause by clause; the quantifier
clauses range over all elements of the domain — *elements*, never subsets. -/
def Formula.Realize {M : Type u} (S : Structure L M) : Formula L → (ℕ → M) → Prop
  | .falsum, _ => False
  | .eq t u, ρ => t.eval S ρ = u.eval S ρ
  | .rel R ts, ρ => S.relMap R (fun i => (ts i).eval S ρ)
  | .imp φ ψ, ρ => φ.Realize S ρ → ψ.Realize S ρ
  | .and φ ψ, ρ => φ.Realize S ρ ∧ ψ.Realize S ρ
  | .or φ ψ, ρ => φ.Realize S ρ ∨ ψ.Realize S ρ
  | .all φ, ρ => ∀ a : M, φ.Realize S (cons a ρ)
  | .ex φ, ρ => ∃ a : M, φ.Realize S (cons a ρ)
-- @endregion

-- @region first_order_logic.holds
-- @provenance definition
/-- A formula **holds** in a structure if it is true under every assignment of the variables.
For a sentence (no free variables) the assignment does not matter, and this is `M ⊨ φ`. -/
def Formula.Holds {M : Type u} (S : Structure L M) (φ : Formula L) : Prop :=
  ∀ ρ : ℕ → M, φ.Realize S ρ
-- @endregion

section Substitution

variable {M : Type u} (S : Structure L M)

-- @region first_order_logic.eval_subst
-- @provenance independent
/-- Substituting and then evaluating is evaluating in the environment of substituted values:
`⟦t[σ]⟧ρ = ⟦t⟧(i ↦ ⟦σ i⟧ρ)`. Induction on the term. -/
theorem Term.eval_subst (σ : ℕ → Term L) (ρ : ℕ → M) (t : Term L) :
    (t.subst σ).eval S ρ = t.eval S (fun i => (σ i).eval S ρ) := by
  induction t with
  | var i => rfl
  | func f ts ih => simp only [Term.subst, Term.eval, ih]
-- @endregion

-- @region first_order_logic.eval_shift
-- @provenance independent
/-- A shifted term ignores the newly bound variable: `⟦t↑⟧(a, ρ) = ⟦t⟧ρ`. -/
theorem Term.eval_shift (t : Term L) (a : M) (ρ : ℕ → M) :
    t.shift.eval S (cons a ρ) = t.eval S ρ := by
  rw [Term.shift, Term.eval_subst]
  rfl
-- @endregion

-- @region first_order_logic.eval_up
-- @provenance independent
/-- Evaluating the lifted substitution `up σ` in the extended environment `(a, ρ)` gives the
extended environment of substituted values. -/
theorem eval_up (σ : ℕ → Term L) (a : M) (ρ : ℕ → M) :
    (fun i => (up σ i).eval S (cons a ρ)) = cons a (fun i => (σ i).eval S ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact Term.eval_shift S (σ i) a ρ
-- @endregion

-- @region first_order_logic.realize_subst
-- @provenance independent
/-- **The substitution lemma.** `M ⊨ φ[σ][ρ]` exactly when `M ⊨ φ[i ↦ ⟦σ i⟧ρ]`: substitution in
the syntax corresponds to changing the assignment in the semantics. Induction on `φ`; the
quantifier cases use `eval_up`. This lemma is the heart of the soundness proof for the
quantifier rules. -/
theorem Formula.realize_subst (φ : Formula L) :
    ∀ (σ : ℕ → Term L) (ρ : ℕ → M),
      (φ.subst σ).Realize S ρ ↔ φ.Realize S (fun i => (σ i).eval S ρ) := by
  induction φ with
  | falsum => intro σ ρ; exact Iff.rfl
  | eq t u => intro σ ρ; simp only [Formula.subst, Formula.Realize, Term.eval_subst]
  | rel R ts => intro σ ρ; simp only [Formula.subst, Formula.Realize, Term.eval_subst]
  | imp φ ψ ihφ ihψ => intro σ ρ; simp only [Formula.subst, Formula.Realize, ihφ, ihψ]
  | and φ ψ ihφ ihψ => intro σ ρ; simp only [Formula.subst, Formula.Realize, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intro σ ρ; simp only [Formula.subst, Formula.Realize, ihφ, ihψ]
  | all φ ih => intro σ ρ; simp only [Formula.subst, Formula.Realize, ih, eval_up]
  | ex φ ih => intro σ ρ; simp only [Formula.subst, Formula.Realize, ih, eval_up]
-- @endregion

-- @region first_order_logic.realize_shift
-- @provenance independent
/-- A shifted formula does not see the newly bound variable: `M ⊨ φ↑[a, ρ] ↔ M ⊨ φ[ρ]`. -/
theorem Formula.realize_shift (φ : Formula L) (a : M) (ρ : ℕ → M) :
    φ.shift.Realize S (cons a ρ) ↔ φ.Realize S ρ := by
  rw [Formula.shift, Formula.realize_subst]
  exact Iff.rfl
-- @endregion

-- @region first_order_logic.realize_inst
-- @provenance independent
/-- Instantiating the bound variable by a term `t` is the same as giving it the value of `t`:
`M ⊨ φ(t)[ρ] ↔ M ⊨ φ[⟦t⟧ρ, ρ]`. -/
theorem Formula.realize_inst (φ : Formula L) (t : Term L) (ρ : ℕ → M) :
    (φ.subst (inst t)).Realize S ρ ↔ φ.Realize S (cons (t.eval S ρ) ρ) := by
  rw [Formula.realize_subst]
  have h : (fun i => (inst t i).eval S ρ) = cons (t.eval S ρ) ρ := by
    funext i
    cases i <;> rfl
  rw [h]
-- @endregion

end Substitution

/-! ### Natural deduction -/

-- @region first_order_logic.derivable
-- @provenance definition
/-- **Natural deduction**, in sequent form: `Derivable Γ φ` means that `φ` can be derived from
the list of assumptions `Γ`. One introduction and one elimination rule per connective, ex falso,
classical reductio ad absurdum, and two rules for equality. In `allI` the assumptions are
shifted, so the variable `0` is *fresh* — it occurs free in no assumption (the eigenvariable
condition); in `exE` the witness is likewise a fresh variable. -/
inductive Derivable : List (Formula L) → Formula L → Prop
  | assume {Γ : List (Formula L)} {φ : Formula L} : φ ∈ Γ → Derivable Γ φ
  | impI {Γ : List (Formula L)} {φ ψ : Formula L} :
      Derivable (φ :: Γ) ψ → Derivable Γ (.imp φ ψ)
  | impE {Γ : List (Formula L)} {φ ψ : Formula L} :
      Derivable Γ (.imp φ ψ) → Derivable Γ φ → Derivable Γ ψ
  | andI {Γ : List (Formula L)} {φ ψ : Formula L} :
      Derivable Γ φ → Derivable Γ ψ → Derivable Γ (.and φ ψ)
  | andE₁ {Γ : List (Formula L)} {φ ψ : Formula L} : Derivable Γ (.and φ ψ) → Derivable Γ φ
  | andE₂ {Γ : List (Formula L)} {φ ψ : Formula L} : Derivable Γ (.and φ ψ) → Derivable Γ ψ
  | orI₁ {Γ : List (Formula L)} {φ ψ : Formula L} : Derivable Γ φ → Derivable Γ (.or φ ψ)
  | orI₂ {Γ : List (Formula L)} {φ ψ : Formula L} : Derivable Γ ψ → Derivable Γ (.or φ ψ)
  | orE {Γ : List (Formula L)} {φ ψ χ : Formula L} : Derivable Γ (.or φ ψ) →
      Derivable (φ :: Γ) χ → Derivable (ψ :: Γ) χ → Derivable Γ χ
  | falsumE {Γ : List (Formula L)} {φ : Formula L} : Derivable Γ .falsum → Derivable Γ φ
  | raa {Γ : List (Formula L)} {φ : Formula L} : Derivable (φ.not :: Γ) .falsum → Derivable Γ φ
  | allI {Γ : List (Formula L)} {φ : Formula L} :
      Derivable (Γ.map Formula.shift) φ → Derivable Γ (.all φ)
  | allE {Γ : List (Formula L)} {φ : Formula L} (t : Term L) :
      Derivable Γ (.all φ) → Derivable Γ (φ.subst (inst t))
  | exI {Γ : List (Formula L)} {φ : Formula L} (t : Term L) :
      Derivable Γ (φ.subst (inst t)) → Derivable Γ (.ex φ)
  | exE {Γ : List (Formula L)} {φ ψ : Formula L} : Derivable Γ (.ex φ) →
      Derivable (φ :: Γ.map Formula.shift) ψ.shift → Derivable Γ ψ
  | eqRefl {Γ : List (Formula L)} (t : Term L) : Derivable Γ (.eq t t)
  | eqSubst {Γ : List (Formula L)} {φ : Formula L} {s t : Term L} : Derivable Γ (.eq s t) →
      Derivable Γ (φ.subst (inst s)) → Derivable Γ (φ.subst (inst t))
-- @endregion

-- @region first_order_logic.soundness
-- @provenance independent
/-- **The soundness theorem.** If `φ` is derivable from `Γ`, then `φ` is true in every structure,
under every assignment that makes all of `Γ` true: `Γ ⊢ φ` implies `Γ ⊨ φ`.
Proof by induction on the derivation, one case per rule, exactly as in the lesson. The
propositional rules are the truth-table facts; `raa` uses classical logic in the metatheory;
the quantifier rules use the substitution lemma (`realize_inst`) and the fact that shifted
formulas ignore the new variable (`realize_shift`). -/
theorem soundness {Γ : List (Formula L)} {φ : Formula L} (h : Derivable Γ φ) :
    ∀ {M : Type u} (S : Structure L M) (ρ : ℕ → M),
      (∀ ψ ∈ Γ, ψ.Realize S ρ) → φ.Realize S ρ := by
  induction h with
  | assume hφ => intro M S ρ hΓ; exact hΓ _ hφ
  | impI _ ih =>
    intro M S ρ hΓ hφ
    apply ih S ρ
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hφ
    · exact hΓ ψ hψ
  | impE _ _ ih₁ ih₂ => intro M S ρ hΓ; exact ih₁ S ρ hΓ (ih₂ S ρ hΓ)
  | andI _ _ ih₁ ih₂ => intro M S ρ hΓ; exact ⟨ih₁ S ρ hΓ, ih₂ S ρ hΓ⟩
  | andE₁ _ ih => intro M S ρ hΓ; exact (ih S ρ hΓ).1
  | andE₂ _ ih => intro M S ρ hΓ; exact (ih S ρ hΓ).2
  | orI₁ _ ih => intro M S ρ hΓ; exact Or.inl (ih S ρ hΓ)
  | orI₂ _ ih => intro M S ρ hΓ; exact Or.inr (ih S ρ hΓ)
  | orE _ _ _ ih ih₁ ih₂ =>
    intro M S ρ hΓ
    rcases ih S ρ hΓ with hφ | hψ
    · apply ih₁ S ρ
      intro χ hχ
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hφ
      · exact hΓ χ hχ
    · apply ih₂ S ρ
      intro χ hχ
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hψ
      · exact hΓ χ hχ
  | falsumE _ ih => intro M S ρ hΓ; exact (ih S ρ hΓ).elim
  | @raa Γ φ _ ih =>
    intro M S ρ hΓ
    by_contra hn
    apply ih S ρ
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hn
    · exact hΓ ψ hψ
  | @allI Γ φ _ ih =>
    intro M S ρ hΓ a
    apply ih S (cons a ρ)
    intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hψ
    exact (Formula.realize_shift S χ a ρ).2 (hΓ χ hχ)
  | @allE Γ φ t _ ih =>
    intro M S ρ hΓ
    exact (Formula.realize_inst S φ t ρ).2 (ih S ρ hΓ (t.eval S ρ))
  | @exI Γ φ t _ ih =>
    intro M S ρ hΓ
    exact ⟨t.eval S ρ, (Formula.realize_inst S φ t ρ).1 (ih S ρ hΓ)⟩
  | @exE Γ φ ψ _ _ ih₁ ih₂ =>
    intro M S ρ hΓ
    obtain ⟨a, ha⟩ := ih₁ S ρ hΓ
    have h := ih₂ S (cons a ρ) (by
      intro χ hχ
      rcases List.mem_cons.1 hχ with rfl | hχ
      · exact ha
      · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hχ
        exact (Formula.realize_shift S θ a ρ).2 (hΓ θ hθ))
    exact (Formula.realize_shift S ψ a ρ).1 h
  | eqRefl t => intro M S ρ _; rfl
  | @eqSubst Γ φ s t _ _ ih₁ ih₂ =>
    intro M S ρ hΓ
    have hst : s.eval S ρ = t.eval S ρ := ih₁ S ρ hΓ
    have hs := (Formula.realize_inst S φ s ρ).1 (ih₂ S ρ hΓ)
    rw [hst] at hs
    exact (Formula.realize_inst S φ t ρ).2 hs
-- @endregion

/-! ### Derivable and underivable -/

-- @region first_order_logic.all_imp_ex
-- @provenance independent
/-- **`∀x φ → ∃x φ` is derivable**: assume `∀x φ`, instantiate it at the variable `0`, and use
that same variable as the witness for `∃x φ`. By soundness it is true in every structure — which
is only correct because structures are non-empty (an environment `ρ : ℕ → M` needs an element). -/
theorem all_imp_ex (φ : Formula L) : Derivable [] (.imp (.all φ) (.ex φ)) :=
  .impI (.exI (.var 0) (.allE (.var 0) (.assume (List.mem_singleton_self _))))
-- @endregion

-- @region first_order_logic.p_rel
-- @provenance definition
/-- A signature with a single unary relation symbol `P` and no function symbols. -/
inductive PRel : ℕ → Type
  | P : PRel 1
-- @endregion

-- @region first_order_logic.sig_p
-- @provenance definition
/-- The signature `{P}`. -/
def sigP : Signature := ⟨fun _ => Empty, PRel⟩
-- @endregion

-- @region first_order_logic.p_at
-- @provenance definition
/-- The atomic formula `P(x)` for the variable `x = var i`. -/
def pAt (i : ℕ) : Formula sigP := .rel (n := 1) PRel.P (fun _ => .var i)
-- @endregion

-- @region first_order_logic.bool_p
-- @provenance definition
/-- The two-element structure `{false, true}` in which `P` holds of `true` only. -/
def boolP : Structure sigP Bool where
  funMap := fun f _ => Empty.elim f
  relMap := fun {n} R xs => match n, R, xs with
    | _, PRel.P, xs => xs 0 = true
-- @endregion

-- @region first_order_logic.ex_imp_all_not_derivable
-- @provenance independent
/-- **`∃x P(x) → ∀x P(x)` is not derivable.** If it were, soundness would make it true in every
structure; but in `boolP` some element satisfies `P` (namely `true`) and not every element does
(`false` does not). Soundness turns a single countermodel into a proof of underivability. -/
theorem ex_imp_all_not_derivable : ¬ Derivable [] (.imp (.ex (pAt 0)) (.all (pAt 0))) := by
  intro h
  have htrue := soundness h boolP (fun _ => true) (by simp)
  have hfalse : false = true := htrue ⟨true, rfl⟩ false
  exact Bool.false_ne_true hfalse
-- @endregion

/-! ### Unwinding satisfaction: the group axioms in `(ℤ, +, 0, −)` -/

-- @region first_order_logic.group_func
-- @provenance definition
/-- The function symbols of the signature of groups: a binary `mul`, a constant `one` and a
unary `inv`. -/
inductive GroupFunc : ℕ → Type
  | mul : GroupFunc 2
  | one : GroupFunc 0
  | inv : GroupFunc 1
-- @endregion

-- @region first_order_logic.sig_group
-- @provenance definition
/-- The signature of groups `{·, 1, ⁻¹}`, with no relation symbols besides equality. -/
def sigGroup : Signature := ⟨GroupFunc, fun _ => Empty⟩
-- @endregion

-- @region first_order_logic.group_axioms
-- @provenance definition
/-- **The group axioms as first-order sentences** (variables are de Bruijn indices; in
`∀x∀y∀z`, `z` is `var 0`, `y` is `var 1`, `x` is `var 2`):
`∀x∀y∀z (x·y)·z = x·(y·z)`, `∀x x·1 = x`, `∀x 1·x = x`, `∀x x·x⁻¹ = 1`, `∀x x⁻¹·x = 1`. -/
def groupAxioms : List (Formula sigGroup) :=
  let mul (s t : Term sigGroup) : Term sigGroup := .func GroupFunc.mul ![s, t]
  let one : Term sigGroup := .func GroupFunc.one ![]
  let inv (s : Term sigGroup) : Term sigGroup := .func GroupFunc.inv ![s]
  [ .all (.all (.all (.eq (mul (mul (.var 2) (.var 1)) (.var 0))
                          (mul (.var 2) (mul (.var 1) (.var 0)))))),
    .all (.eq (mul (.var 0) one) (.var 0)),
    .all (.eq (mul one (.var 0)) (.var 0)),
    .all (.eq (mul (.var 0) (inv (.var 0))) one),
    .all (.eq (mul (inv (.var 0)) (.var 0)) one) ]
-- @endregion

-- @region first_order_logic.int_add
-- @provenance definition
/-- The integers as a structure for the signature of groups: `·` is `+`, `1` is `0` and `⁻¹`
is negation. -/
def intAdd : Structure sigGroup ℤ where
  funMap := fun {n} f xs => match n, f, xs with
    | _, GroupFunc.mul, xs => xs 0 + xs 1
    | _, GroupFunc.one, _ => 0
    | _, GroupFunc.inv, xs => -xs 0
  relMap := fun R _ => Empty.elim R
-- @endregion

-- @region first_order_logic.int_add_group
-- @provenance independent
/-- **`(ℤ, +, 0, −)` satisfies the group axioms.** Unwinding the definition of satisfaction turns
each sentence into an ordinary statement about integers — `(a + b) + c = a + (b + c)`,
`a + 0 = a`, … — which the ring-arithmetic lemmas prove. -/
theorem intAdd_group : ∀ φ ∈ groupAxioms, φ.Holds intAdd := by
  intro φ hφ ρ
  simp only [groupAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl
  · intro a b c
    show (a + b) + c = a + (b + c)
    exact Int.add_assoc a b c
  · intro a
    show a + 0 = a
    exact Int.add_zero a
  · intro a
    show 0 + a = a
    exact Int.zero_add a
  · intro a
    show a + -a = 0
    exact Int.add_right_neg a
  · intro a
    show -a + a = 0
    exact Int.add_left_neg a
-- @endregion

/-! ### Isomorphic structures satisfy the same sentences -/

-- @region first_order_logic.iso
-- @provenance definition
/-- An **isomorphism of structures**: a bijection that commutes with the interpretation of every
function symbol and preserves and reflects every relation. -/
structure Iso {M : Type u} {N : Type v} (S : Structure L M) (T : Structure L N) where
  /-- The underlying bijection. -/
  toEquiv : M ≃ N
  /-- It commutes with the functions. -/
  map_fun : ∀ {n} (f : L.Func n) (xs : Fin n → M),
    toEquiv (S.funMap f xs) = T.funMap f (fun i => toEquiv (xs i))
  /-- It preserves and reflects the relations. -/
  map_rel : ∀ {n} (R : L.Rel n) (xs : Fin n → M),
    S.relMap R xs ↔ T.relMap R (fun i => toEquiv (xs i))
-- @endregion

section Invariance

variable {M : Type u} {N : Type v} {S : Structure L M} {T : Structure L N}

-- @region first_order_logic.iso_eval
-- @provenance independent
/-- An isomorphism carries the value of a term to the value of the same term:
`e(⟦t⟧ρ) = ⟦t⟧(e ∘ ρ)`. Induction on the term, using `map_fun`. -/
theorem Iso.eval (e : Iso S T) (ρ : ℕ → M) (t : Term L) :
    e.toEquiv (t.eval S ρ) = t.eval T (fun i => e.toEquiv (ρ i)) := by
  induction t with
  | var i => rfl
  | func f ts ih => simp only [Term.eval, e.map_fun, ih]
-- @endregion

-- @region first_order_logic.iso_realize
-- @provenance independent
/-- **Isomorphisms preserve truth**: `M ⊨ φ[ρ]` if and only if `N ⊨ φ[e ∘ ρ]`, for every
formula. Induction on `φ`: equations use that `e` is injective, atomic formulas use `map_rel`,
and the quantifier cases use that `e` is surjective (every element of `N` is `e(a)`). -/
theorem Iso.realize (e : Iso S T) (φ : Formula L) :
    ∀ ρ : ℕ → M, φ.Realize S ρ ↔ φ.Realize T (fun i => e.toEquiv (ρ i)) := by
  have hcons : ∀ (a : M) (ρ : ℕ → M),
      (fun i => e.toEquiv (cons a ρ i)) = cons (e.toEquiv a) (fun i => e.toEquiv (ρ i)) := by
    intro a ρ
    funext i
    cases i <;> rfl
  induction φ with
  | falsum => intro ρ; exact Iff.rfl
  | eq t u =>
    intro ρ
    simp only [Formula.Realize, ← e.eval, e.toEquiv.apply_eq_iff_eq]
  | rel R ts =>
    intro ρ
    simp only [Formula.Realize, ← e.eval]
    exact e.map_rel R _
  | imp φ ψ ihφ ihψ => intro ρ; simp only [Formula.Realize, ihφ, ihψ]
  | and φ ψ ihφ ihψ => intro ρ; simp only [Formula.Realize, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intro ρ; simp only [Formula.Realize, ihφ, ihψ]
  | all φ ih =>
    intro ρ
    simp only [Formula.Realize]
    constructor
    · intro h b
      have hb := (ih (cons (e.toEquiv.symm b) ρ)).1 (h _)
      rw [hcons, Equiv.apply_symm_apply] at hb
      exact hb
    · intro h a
      rw [ih, hcons]
      exact h _
  | ex φ ih =>
    intro ρ
    simp only [Formula.Realize]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e.toEquiv a, ?_⟩
      rw [← hcons, ← ih]
      exact ha
    · rintro ⟨b, hb⟩
      refine ⟨e.toEquiv.symm b, ?_⟩
      rw [ih, hcons, Equiv.apply_symm_apply]
      exact hb
-- @endregion

-- @region first_order_logic.iso_holds
-- @provenance independent
/-- **Isomorphic structures satisfy exactly the same formulas** (in particular the same
sentences). Every assignment in `N` is `e ∘ ρ` for an assignment `ρ` in `M` (take
`ρ = e⁻¹ ∘ ρ'`), so "true under all assignments" transfers both ways. -/
theorem Iso.holds_iff (e : Iso S T) (φ : Formula L) : φ.Holds S ↔ φ.Holds T := by
  constructor
  · intro h ρ'
    have := (e.realize φ (fun i => e.toEquiv.symm (ρ' i))).1 (h _)
    simpa only [Equiv.apply_symm_apply] using this
  · intro h ρ
    exact (e.realize φ ρ).2 (h _)
-- @endregion

end Invariance

/-! ### `(ℕ, <)` and `(ℤ, <)` are not isomorphic -/

-- @region first_order_logic.ord_rel
-- @provenance definition
/-- The signature of strict orders has one binary relation symbol `<`. -/
inductive OrdRel : ℕ → Type
  | lt : OrdRel 2
-- @endregion

-- @region first_order_logic.sig_ord
-- @provenance definition
/-- The signature `{<}`. -/
def sigOrd : Signature := ⟨fun _ => Empty, OrdRel⟩
-- @endregion

-- @region first_order_logic.order_structure
-- @provenance definition
/-- Any type with a relation `<` is a structure for `{<}`. -/
def orderStructure (M : Type u) [LT M] : Structure sigOrd M where
  funMap := fun f _ => Empty.elim f
  relMap := fun {n} R xs => match n, R, xs with
    | _, OrdRel.lt, xs => xs 0 < xs 1
-- @endregion

-- @region first_order_logic.has_least
-- @provenance definition
/-- The sentence "there is a least element", `∃x ∀y ¬(y < x)`. Inside both quantifiers, `y` is
`var 0` and `x` is `var 1`. -/
def hasLeast : Formula sigOrd :=
  .ex (.all (Formula.not (.rel OrdRel.lt ![.var 0, .var 1])))
-- @endregion

-- @region first_order_logic.nat_has_least
-- @provenance independent
/-- `(ℕ, <) ⊨ ∃x ∀y ¬(y < x)`: take `x = 0`; no natural number is below `0`. -/
theorem nat_hasLeast : hasLeast.Holds (orderStructure ℕ) := by
  intro ρ
  refine ⟨0, fun b hb => ?_⟩
  exact Nat.not_lt_zero b hb
-- @endregion

-- @region first_order_logic.int_not_has_least
-- @provenance independent
/-- `(ℤ, <) ⊭ ∃x ∀y ¬(y < x)`: whatever `x` is proposed, `y = x − 1` is smaller. -/
theorem int_not_hasLeast : ¬ hasLeast.Holds (orderStructure ℤ) := by
  intro h
  obtain ⟨a, ha⟩ := h (fun _ => 0)
  exact ha (a - 1) (show a - 1 < a by omega)
-- @endregion

-- @region first_order_logic.nat_not_iso_int
-- @provenance independent
/-- **`(ℕ, <)` and `(ℤ, <)` are not isomorphic.** An order isomorphism `ℕ ≃o ℤ` would be an
isomorphism of `{<}`-structures (`a < b ↔ e a < e b`), and isomorphic structures satisfy the
same sentences; but "there is a least element" is true in `ℕ` and false in `ℤ`. -/
theorem nat_not_iso_int : IsEmpty (ℕ ≃o ℤ) := by
  constructor
  intro e
  let iso : Iso (orderStructure ℕ) (orderStructure ℤ) :=
    { toEquiv := e.toEquiv
      map_fun := fun f _ => Empty.elim f
      map_rel := fun {n} R xs => match n, R, xs with
        | _, OrdRel.lt, xs => e.lt_iff_lt.symm }
  exact int_not_hasLeast ((iso.holds_iff hasLeast).1 nat_hasLeast)
-- @endregion

/-! ### Mathlib's first-order logic -/

-- @region first_order_logic.iso_sentence_library
-- @provenance library
/-- Mathlib's version of isomorphism invariance, for its own syntax (`FirstOrder.Language`,
`Sentence`) and semantics (`Sentence.Realize`): an isomorphism of `L`-structures `M ≃[L] N`
preserves the truth of every sentence. This applies
`FirstOrder.Language.StrongHomClass.realize_sentence`. -/
theorem iso_sentence_library {L : FirstOrder.Language} {M : Type u} {N : Type v}
    [L.Structure M] [L.Structure N] (e : L.Equiv M N) (φ : L.Sentence) :
    φ.Realize M ↔ φ.Realize N :=
  FirstOrder.Language.StrongHomClass.realize_sentence e φ
-- @endregion

end Lumenary.FirstOrderLogic
