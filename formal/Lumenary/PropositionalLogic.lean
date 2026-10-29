/-
The Lumenary — formal mathematics
Propositional logic and truth tables: formulas, valuations, the truth-table method, and the
laws of the conditional (contrapositive, converse, negation) and De Morgan.

Two levels are formalised here.

* **Truth tables as computation.** `Formula n` is a small syntax of propositional formulas in
  `n` variables, `Formula.eval` computes a formula's truth value (a `Bool`) under a row of a
  truth table, and `valuations n` lists all `2 ^ n` rows. We prove (`@provenance independent`)
  that the list really contains every row, so checking every row — `isTautology` — is a correct
  test for tautologies and equivalence. Particular equivalences (contrapositive, De Morgan, the
  negation of a conditional) and non-equivalences (the converse, affirming the consequent) are
  then checked by evaluating their truth tables with `decide`.
* **Logic in Lean's `Prop`.** Lean's propositions are not just `true`/`false` values: a proof of
  `p → q` is a function turning proofs of `p` into proofs of `q`. We prove the same laws there.
  One direction of the contrapositive law needs the law of excluded middle (classical logic);
  the other does not. Library versions: `not_imp_not`, `not_and_or`, `not_or`,
  `Classical.not_imp` and `Classical.not_forall`.
-/
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs

namespace Lumenary.PropositionalLogic

/-! ### Formulas and their truth values -/

-- @region propositional_logic.formula
-- @provenance definition
/-- Propositional formulas in `n` variables `x₀, …, xₙ₋₁`: variables, the constants true and
false, and the connectives not, and, or, implies and if-and-only-if. -/
inductive Formula (n : ℕ) : Type where
  | var : Fin n → Formula n
  | tt : Formula n
  | ff : Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n
  | imp : Formula n → Formula n → Formula n
  | iff : Formula n → Formula n → Formula n
-- @endregion

-- @region propositional_logic.formula_eval
-- @provenance definition
/-- The truth value of a formula in one row of its truth table. A row (a *valuation*) `v`
assigns `true` or `false` to each variable. Note the conditional: `φ → ψ` is false only when
`φ` is true and `ψ` is false, i.e. it has the value `!φ || ψ`. -/
def Formula.eval {n : ℕ} (v : Fin n → Bool) : Formula n → Bool
  | .var i => v i
  | .tt => true
  | .ff => false
  | .not φ => !φ.eval v
  | .and φ ψ => φ.eval v && ψ.eval v
  | .or φ ψ => φ.eval v || ψ.eval v
  | .imp φ ψ => !φ.eval v || ψ.eval v
  | .iff φ ψ => φ.eval v == ψ.eval v
-- @endregion

/-! ### The rows of a truth table -/

-- @region propositional_logic.valuations
-- @provenance definition
/-- All rows of a truth table in `n` variables, in textbook order (the first variable is true
in the first half of the rows, false in the second half, and so on recursively). -/
def valuations : (n : ℕ) → List (Fin n → Bool)
  | 0 => [fun i => i.elim0]
  | n + 1 => [true, false].flatMap fun b => (valuations n).map (Fin.cons b)
-- @endregion

-- @region propositional_logic.length_valuations
-- @provenance independent
/-- A truth table in `n` variables has `2 ^ n` rows: each new variable doubles the number of
rows, once with the variable true and once with it false. Proved by induction on `n`. -/
theorem length_valuations (n : ℕ) : (valuations n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [valuations, ih, pow_succ, Nat.mul_two]
-- @endregion

-- @region propositional_logic.mem_valuations
-- @provenance independent
/-- **Every row appears.** Any assignment of truth values to `n` variables is one of the rows
listed by `valuations n`. Proof by induction on `n`: an assignment to `n + 1` variables is its
value on the first variable followed by an assignment to the remaining `n`
(`Fin.cons_self_tail`). -/
theorem mem_valuations : ∀ (n : ℕ) (v : Fin n → Bool), v ∈ valuations n
  | 0, v => by
    simp only [valuations, List.mem_singleton]
    funext i
    exact i.elim0
  | n + 1, v => by
    simp only [valuations, List.mem_flatMap, List.mem_map]
    refine ⟨v 0, by cases v 0 <;> simp, Fin.tail v, mem_valuations n (Fin.tail v), ?_⟩
    exact Fin.cons_self_tail v
-- @endregion

/-! ### Tautologies and equivalence, decided by truth tables -/

-- @region propositional_logic.is_tautology
-- @provenance definition
/-- The **truth-table test**: a formula passes when it is true in every row of its table. -/
def isTautology {n : ℕ} (φ : Formula n) : Bool := (valuations n).all fun v => φ.eval v
-- @endregion

-- @region propositional_logic.is_tautology_iff
-- @provenance independent
/-- **The truth-table method is correct.** The finite check `isTautology φ` succeeds exactly
when `φ` is true under *every* assignment, i.e. exactly when `φ` is a tautology. The forward
direction needs `mem_valuations`: no row has been forgotten. -/
theorem isTautology_iff {n : ℕ} (φ : Formula n) :
    isTautology φ = true ↔ ∀ v : Fin n → Bool, φ.eval v = true := by
  unfold isTautology
  rw [List.all_eq_true]
  exact ⟨fun h v => h v (mem_valuations n v), fun h v _ => h v⟩
-- @endregion

-- @region propositional_logic.equivalent
-- @provenance definition
/-- Two formulas are **logically equivalent** when they have the same truth value in every row
of the truth table. -/
def Equivalent {n : ℕ} (φ ψ : Formula n) : Prop := ∀ v : Fin n → Bool, φ.eval v = ψ.eval v
-- @endregion

-- @region propositional_logic.equivalent_iff_tautology
-- @provenance independent
/-- `φ` and `ψ` are equivalent exactly when the biconditional `φ ↔ ψ` is a tautology, so the
truth-table test also decides equivalence. -/
theorem equivalent_iff_tautology {n : ℕ} (φ ψ : Formula n) :
    Equivalent φ ψ ↔ isTautology (.iff φ ψ) = true := by
  rw [isTautology_iff]
  simp [Equivalent, Formula.eval]
-- @endregion

/-! ### Particular laws, checked row by row -/

section Laws

open Formula

-- @region propositional_logic.var_p
-- @provenance definition
/-- The variable `p`, the first of two variables. -/
abbrev p : Formula 2 := var 0
-- @endregion

-- @region propositional_logic.var_q
-- @provenance definition
/-- The variable `q`, the second of two variables. -/
abbrev q : Formula 2 := var 1
-- @endregion

-- @region propositional_logic.contrapositive_table
-- @provenance independent
/-- **Contrapositive.** `p → q` is equivalent to `¬q → ¬p`: the truth-table test passes on all
four rows (computed by `decide`). -/
theorem contrapositive_table : Equivalent (imp p q) (imp (not q) (not p)) := by
  rw [equivalent_iff_tautology]
  decide
-- @endregion

-- @region propositional_logic.converse_table
-- @provenance independent
/-- **The converse is different.** `p → q` and `q → p` are *not* equivalent: they disagree in
the row `p = false`, `q = true`, where `p → q` is (vacuously) true but `q → p` is false. -/
theorem converse_table : ¬ Equivalent (imp p q) (imp q p) := by
  intro h
  have row := h (fun i => if i = 0 then false else true)
  revert row
  decide
-- @endregion

-- @region propositional_logic.de_morgan_table
-- @provenance independent
/-- **De Morgan's laws** as truth tables: `¬(p ∧ q) ≡ ¬p ∨ ¬q` and `¬(p ∨ q) ≡ ¬p ∧ ¬q`. -/
theorem de_morgan_table :
    Equivalent (not (and p q)) (or (not p) (not q)) ∧
      Equivalent (not (or p q)) (and (not p) (not q)) := by
  rw [equivalent_iff_tautology, equivalent_iff_tautology]
  decide
-- @endregion

-- @region propositional_logic.not_imp_table
-- @provenance independent
/-- **Negating a conditional.** `¬(p → q) ≡ p ∧ ¬q`: a promise "if p then q" is broken exactly
when p happens and q does not. -/
theorem not_imp_table : Equivalent (not (imp p q)) (and p (not q)) := by
  rw [equivalent_iff_tautology]
  decide
-- @endregion

-- @region propositional_logic.argument_forms
-- @provenance independent
/-- **Valid and invalid argument forms.** *Modus ponens* `((p → q) ∧ p) → q` and *modus tollens*
`((p → q) ∧ ¬q) → ¬p` are tautologies; *affirming the consequent* `((p → q) ∧ q) → p` is not. -/
theorem argument_forms :
    isTautology (imp (and (imp p q) p) q) = true ∧
      isTautology (imp (and (imp p q) (not q)) (not p)) = true ∧
      isTautology (imp (and (imp p q) q) p) = false := by
  decide
-- @endregion

end Laws

/-! ### The same laws for Lean's propositions -/

-- @region propositional_logic.contrapositive
-- @provenance independent
/-- From `p → q` we get `¬q → ¬p`: if `q` fails, then `p` must fail too, since `p` would give `q`.
This direction is *constructive*: it uses no law of excluded middle. -/
theorem contrapositive {p q : Prop} (h : p → q) : ¬q → ¬p :=
  fun hnq hp => hnq (h hp)
-- @endregion

-- @region propositional_logic.contrapositive_iff
-- @provenance independent
/-- **The contrapositive law** `(p → q) ↔ (¬q → ¬p)`. The way back, from `¬q → ¬p` to `p → q`,
argues by contradiction: given `p`, if `q` failed we would get `¬p`, which is absurd. That step
uses classical logic (`by_contra`). -/
theorem contrapositive_iff (p q : Prop) : (p → q) ↔ (¬q → ¬p) := by
  constructor
  · exact contrapositive
  · intro h hp
    by_contra hnq
    exact h hnq hp
-- @endregion

-- @region propositional_logic.contrapositive_iff_library
-- @provenance library
/-- The contrapositive law, by Mathlib's `not_imp_not : (¬a → ¬b) ↔ (b → a)`. -/
theorem contrapositive_iff_library (p q : Prop) : (p → q) ↔ (¬q → ¬p) :=
  not_imp_not.symm
-- @endregion

-- @region propositional_logic.converse_fails
-- @provenance independent
/-- **An implication does not imply its converse.** Take `p` false and `q` true: `p → q` holds
(its hypothesis is false), but `q → p` would turn a proof of `True` into a proof of `False`. -/
theorem converse_fails : ¬ ∀ p q : Prop, (p → q) → (q → p) := by
  intro h
  exact h False True (fun hf => hf.elim) trivial
-- @endregion

-- @region propositional_logic.de_morgan_or
-- @provenance independent
/-- **De Morgan** `¬(p ∨ q) ↔ ¬p ∧ ¬q`, proved constructively: "neither p nor q". -/
theorem de_morgan_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
    fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩
-- @endregion

-- @region propositional_logic.de_morgan_and
-- @provenance library
/-- **De Morgan** `¬(p ∧ q) ↔ ¬p ∨ ¬q`, by Mathlib's `not_and_or`. Going from left to right
needs classical logic: to name *which* of `p`, `q` fails we must decide whether `p` holds. -/
theorem de_morgan_and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  not_and_or
-- @endregion

-- @region propositional_logic.not_imp_iff
-- @provenance library
/-- **Negating a conditional**: `¬(p → q) ↔ p ∧ ¬q`, by core Lean's `Classical.not_imp`. -/
theorem not_imp_iff (p q : Prop) : ¬(p → q) ↔ p ∧ ¬q :=
  Classical.not_imp
-- @endregion

-- @region propositional_logic.not_forall_imp
-- @provenance independent
/-- **Negating a quantified conditional**: "not every `x` with `P` has `Q`" means "some `x` has
`P` but not `Q`". It combines `Classical.not_forall` (`¬∀ ↔ ∃¬`) with the negation of a
conditional. -/
theorem not_forall_imp {α : Type*} (P Q : α → Prop) :
    (¬ ∀ x, P x → Q x) ↔ ∃ x, P x ∧ ¬ Q x := by
  rw [Classical.not_forall]
  exact exists_congr fun x => Classical.not_imp
-- @endregion

-- @region propositional_logic.not_every_prime_odd
-- @provenance independent
/-- "Every prime is odd" is false. By `not_forall_imp`, its negation is "some prime is not odd",
and `2` is a witness. -/
theorem not_every_prime_odd : ¬ ∀ n : ℕ, n.Prime → Odd n := by
  rw [not_forall_imp]
  exact ⟨2, Nat.prime_two, by decide⟩
-- @endregion

-- @region propositional_logic.vacuous_truth
-- @provenance independent
/-- **Vacuous truth.** "If a natural number is negative, then it equals 17" is *true*: its
hypothesis never holds, so it can never be broken. -/
theorem vacuous_truth : ∀ n : ℕ, n < 0 → n = 17 :=
  fun n h => absurd h (Nat.not_lt_zero n)
-- @endregion

end Lumenary.PropositionalLogic
