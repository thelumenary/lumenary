/-
The Lumenary — formal mathematics
Formal methods: the operational semantics of a small imperative language, Hoare logic and its
soundness, a verified program, type soundness by progress and preservation, model checking as a
fixed-point computation, and Rice's theorem.

What is proved here. The language IMP has deeply embedded commands and shallowly embedded
expressions (an arithmetic expression is any function `State → ℤ`, a test any `State → Bool`).
We prove: big-step evaluation is deterministic; every Hoare triple derivable by the rules of
Hoare logic is valid (soundness); the integer-division program meets its specification and
terminates; the loop `while true do skip` never terminates although it satisfies every
partial-correctness triple; a typed language of booleans and numbers is type sound (progress,
preservation, safety); and the CTL operator `EF φ` is the least fixed point of
`Z ↦ φ ∪ pre(Z)`, which is why model checkers compute it by iteration. Rice's theorem is applied
from Mathlib (`ComputablePred.rice`), as is the Knaster–Tarski least fixed point
(`OrderHom.lfp`). Relative completeness of Hoare logic (Cook 1978) and the complexity of CTL
model checking are not formalised.
-/
import Mathlib.Order.FixedPoints
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.Computability.Halting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Lumenary.FormalMethods

/-! ### IMP: syntax and big-step semantics -/

-- @region formal_methods.state
-- @provenance definition
/-- A state assigns an integer to every variable name. -/
abbrev State : Type := String → ℤ
-- @endregion

-- @region formal_methods.com
-- @provenance definition
/-- Commands of the language IMP. Expressions are shallowly embedded: an arithmetic expression
is a function `State → ℤ` and a test is a function `State → Bool`. -/
inductive Com where
  /-- Do nothing. -/
  | skip
  /-- `x := a`. -/
  | assign (x : String) (a : State → ℤ)
  /-- `c₁; c₂`. -/
  | seq (c₁ c₂ : Com)
  /-- `if b then c₁ else c₂`. -/
  | ite (b : State → Bool) (c₁ c₂ : Com)
  /-- `while b do c`. -/
  | while (b : State → Bool) (c : Com)
-- @endregion

-- @region formal_methods.big_step
-- @provenance definition
/-- Big-step operational semantics: `BigStep c s t` says that running `c` from state `s`
terminates in state `t`. Each constructor is one inference rule; a derivation is a finite tree,
so a non-terminating run has no derivation at all. -/
inductive BigStep : Com → State → State → Prop where
  | skip (s : State) : BigStep .skip s s
  | assign (x : String) (a : State → ℤ) (s : State) :
      BigStep (.assign x a) s (Function.update s x (a s))
  | seq {c₁ c₂ : Com} {s t u : State} :
      BigStep c₁ s t → BigStep c₂ t u → BigStep (.seq c₁ c₂) s u
  | ite_true {b : State → Bool} {c₁ c₂ : Com} {s t : State} :
      b s = true → BigStep c₁ s t → BigStep (.ite b c₁ c₂) s t
  | ite_false {b : State → Bool} {c₁ c₂ : Com} {s t : State} :
      b s = false → BigStep c₂ s t → BigStep (.ite b c₁ c₂) s t
  | while_true {b : State → Bool} {c : Com} {s t u : State} :
      b s = true → BigStep c s t → BigStep (.while b c) t u → BigStep (.while b c) s u
  | while_false {b : State → Bool} {c : Com} {s : State} :
      b s = false → BigStep (.while b c) s s
-- @endregion

-- @region formal_methods.big_step_deterministic
-- @provenance independent
/-- **Determinism.** If `c` run from `s` can end in `t` and in `t'`, then `t = t'`.
Proof by induction on the derivation of `BigStep c s t`, inverting the second derivation in
each case; in the `if` and `while` cases the test cannot be both true and false. -/
theorem bigStep_deterministic {c : Com} {s t t' : State}
    (h : BigStep c s t) (h' : BigStep c s t') : t = t' := by
  induction h generalizing t' with
  | skip => cases h'; rfl
  | assign => cases h'; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁ h₂ => exact ih₂ (ih₁ h₁ ▸ h₂)
  | ite_true hb _ ih =>
    cases h' with
    | ite_true _ h₂ => exact ih h₂
    | ite_false hb' _ => simp_all
  | ite_false hb _ ih =>
    cases h' with
    | ite_true hb' _ => simp_all
    | ite_false _ h₂ => exact ih h₂
  | while_true hb _ _ ih₁ ih₂ =>
    cases h' with
    | while_true _ h₁ h₂ => exact ih₂ (ih₁ h₁ ▸ h₂)
    | while_false hb' => simp_all
  | while_false hb =>
    cases h' with
    | while_true hb' _ _ => simp_all
    | while_false _ => rfl
-- @endregion

/-! ### Hoare logic -/

-- @region formal_methods.hoare
-- @provenance definition
/-- The **partial-correctness Hoare triple** `{P} c {Q}`: whenever `P` holds before `c` runs
*and the run terminates*, `Q` holds afterwards. Termination is not part of the claim. -/
def Hoare (P : State → Prop) (c : Com) (Q : State → Prop) : Prop :=
  ∀ s t, P s → BigStep c s t → Q t
-- @endregion

-- @region formal_methods.derivable
-- @provenance definition
/-- The proof rules of Hoare logic. `Derivable P c Q` means the triple has a derivation; it says
nothing yet about running programs — connecting the two is the soundness theorem. -/
inductive Derivable : (State → Prop) → Com → (State → Prop) → Prop where
  | skip (P : State → Prop) : Derivable P .skip P
  | assign (Q : State → Prop) (x : String) (a : State → ℤ) :
      Derivable (fun s => Q (Function.update s x (a s))) (.assign x a) Q
  | seq {P Q R : State → Prop} {c₁ c₂ : Com} :
      Derivable P c₁ Q → Derivable Q c₂ R → Derivable P (.seq c₁ c₂) R
  | ite {P Q : State → Prop} {b : State → Bool} {c₁ c₂ : Com} :
      Derivable (fun s => P s ∧ b s = true) c₁ Q →
      Derivable (fun s => P s ∧ b s = false) c₂ Q → Derivable P (.ite b c₁ c₂) Q
  | while {I : State → Prop} {b : State → Bool} {c : Com} :
      Derivable (fun s => I s ∧ b s = true) c I →
      Derivable I (.while b c) (fun s => I s ∧ b s = false)
  | conseq {P P' Q Q' : State → Prop} {c : Com} :
      (∀ s, P' s → P s) → Derivable P c Q → (∀ s, Q s → Q' s) → Derivable P' c Q'
-- @endregion

-- @region formal_methods.while_sound
-- @provenance independent
/-- The `while` rule is sound: if the body preserves the invariant `I` whenever the test is
true, then after the loop (if it terminates) `I` holds and the test is false. The proof is an
induction on the *execution* — not on the command, which does not get smaller when the loop
unfolds. -/
theorem while_sound {I : State → Prop} {b : State → Bool} {c : Com}
    (hbody : Hoare (fun s => I s ∧ b s = true) c I) :
    Hoare I (.while b c) (fun s => I s ∧ b s = false) := by
  intro s t hI hrun
  generalize hw : Com.while b c = w at hrun
  induction hrun with
  | while_true hb hc _ _ ih₂ =>
    cases hw
    exact ih₂ (hbody _ _ ⟨hI, hb⟩ hc) rfl
  | while_false hb =>
    cases hw
    exact ⟨hI, hb⟩
  | _ => cases hw
-- @endregion

-- @region formal_methods.soundness
-- @provenance independent
/-- **Soundness of Hoare logic.** Every derivable triple is valid. Induction on the derivation;
each rule is checked against the big-step semantics, with `while_sound` for loops. -/
theorem soundness {P Q : State → Prop} {c : Com} (h : Derivable P c Q) : Hoare P c Q := by
  induction h with
  | skip P =>
    intro s t hP hrun
    cases hrun
    exact hP
  | assign Q x a =>
    intro s t hP hrun
    cases hrun
    exact hP
  | seq _ _ ih₁ ih₂ =>
    intro s u hP hrun
    cases hrun with
    | seq h₁ h₂ => exact ih₂ _ _ (ih₁ _ _ hP h₁) h₂
  | ite _ _ ih₁ ih₂ =>
    intro s t hP hrun
    cases hrun with
    | ite_true hb h₁ => exact ih₁ _ _ ⟨hP, hb⟩ h₁
    | ite_false hb h₂ => exact ih₂ _ _ ⟨hP, hb⟩ h₂
  | «while» _ ih => exact while_sound ih
  | conseq hpre _ hpost ih =>
    intro s t hP hrun
    exact hpost _ (ih _ _ (hpre _ hP) hrun)
-- @endregion

/-! ### A verified program: division by repeated subtraction -/

-- @region formal_methods.div_loop
-- @provenance definition
/-- The loop `while b ≤ r do (r := r - b; q := q + 1)`. -/
def divLoop : Com :=
  .while (fun s => decide (s "b" ≤ s "r"))
    (.seq (.assign "r" (fun s => s "r" - s "b")) (.assign "q" (fun s => s "q" + 1)))
-- @endregion

-- @region formal_methods.div_prog
-- @provenance definition
/-- The program `r := a; q := 0; while b ≤ r do (r := r - b; q := q + 1)`. -/
def divProg : Com :=
  .seq (.assign "r" (fun s => s "a")) (.seq (.assign "q" (fun _ => 0)) divLoop)
-- @endregion

-- @region formal_methods.div_invariant
-- @provenance definition
/-- The loop invariant: `a = q·b + r`, `0 ≤ r` and `0 < b`. -/
def divInv (s : State) : Prop :=
  s "a" = s "q" * s "b" + s "r" ∧ 0 ≤ s "r" ∧ 0 < s "b"
-- @endregion

-- @region formal_methods.div_correct
-- @provenance independent
/-- **Partial correctness of division**, proved *inside Hoare logic* and then transported to the
semantics by `soundness`:
`{0 ≤ a ∧ 0 < b} divProg {a = q·b + r ∧ 0 ≤ r < b}`.
The only creative step is the invariant `divInv`; the rest is the verification conditions
`pre → I[q:=0][r:=a]`, `I ∧ b ≤ r → I[q:=q+1][r:=r-b]` and `I ∧ ¬(b ≤ r) → post`. -/
theorem div_correct :
    Hoare (fun s => 0 ≤ s "a" ∧ 0 < s "b") divProg
      (fun t => t "a" = t "q" * t "b" + t "r" ∧ 0 ≤ t "r" ∧ t "r" < t "b") := by
  apply soundness
  -- the loop body preserves the invariant
  have body : Derivable (fun s => divInv s ∧ decide (s "b" ≤ s "r") = true)
      (.seq (.assign "r" (fun s => s "r" - s "b")) (.assign "q" (fun s => s "q" + 1))) divInv := by
    refine .conseq ?_ (.seq (.assign _ _ _) (.assign divInv _ _)) (fun _ h => h)
    intro s ⟨⟨ha, hr, hb⟩, hle⟩
    simp only [decide_eq_true_eq] at hle
    simp only [divInv, Function.update_apply]
    simp only [String.reduceEq, ite_false, ite_true]
    refine ⟨by rw [ha]; ring, by linarith, hb⟩
  refine .conseq ?_ (.seq (.assign _ _ _) (.seq (.assign _ _ _) (.while body))) ?_
  · intro s ⟨ha, hb⟩
    simp only [divInv, Function.update_apply]
    simp only [String.reduceEq, ite_false, ite_true]
    exact ⟨by ring, ha, hb⟩
  · intro t ⟨⟨ha, hr, _⟩, hlt⟩
    simp only [decide_eq_false_iff_not, not_le] at hlt
    exact ⟨ha, hr, hlt⟩
-- @endregion

-- @region formal_methods.div_loop_terminates
-- @provenance independent
/-- **Termination of the loop.** The *variant* `r` is a natural-number measure that the body
decreases (because `b > 0`) and the loop stops before it goes negative. Formally: strong
induction on `n ≥ r`. -/
theorem divLoop_terminates (n : ℕ) :
    ∀ s : State, s "r" ≤ n → 0 < s "b" → ∃ t, BigStep divLoop s t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hr hb
    by_cases hle : s "b" ≤ s "r"
    · -- one iteration, then the induction hypothesis for the smaller value of `r`
      set s₁ := Function.update s "r" (s "r" - s "b") with hs₁
      set s₂ := Function.update s₁ "q" (s₁ "q" + 1) with hs₂
      have hr₂ : s₂ "r" = s "r" - s "b" := by simp [s₂, s₁]
      have hb₂ : s₂ "b" = s "b" := by simp [s₂, s₁]
      have hn : 0 < n := by omega
      obtain ⟨t, ht⟩ := ih (Int.toNat (s "r" - s "b")) (by omega) s₂ (by omega) (by omega)
      exact ⟨t, .while_true (by simpa using hle)
        (.seq (.assign _ _ _) (.assign _ _ _)) ht⟩
    · exact ⟨s, .while_false (by simpa using hle)⟩
-- @endregion

-- @region formal_methods.div_terminates
-- @provenance independent
/-- **Total correctness, the termination half**: from every state with `0 ≤ a` and `0 < b` the
division program terminates. Together with `div_correct` this is total correctness. -/
theorem div_terminates (s : State) (ha : 0 ≤ s "a") (hb : 0 < s "b") :
    ∃ t, BigStep divProg s t := by
  set s₁ := Function.update s "r" (s "a") with hs₁
  set s₂ := Function.update s₁ "q" 0 with hs₂
  have hr : s₂ "r" = s "a" := by simp [s₂, s₁]
  have hb₂ : s₂ "b" = s "b" := by simp [s₂, s₁]
  obtain ⟨t, ht⟩ := divLoop_terminates (Int.toNat (s "a")) s₂ (by omega) (by omega)
  exact ⟨t, .seq (.assign _ _ _) (.seq (.assign _ _ _) ht)⟩
-- @endregion

/-! ### Partial correctness does not imply termination -/

-- @region formal_methods.loop_forever
-- @provenance definition
/-- The program `while true do skip`. -/
def loopForever : Com := .while (fun _ => true) .skip
-- @endregion

-- @region formal_methods.loop_forever_diverges
-- @provenance independent
/-- `while true do skip` has no terminating run from any state: a derivation would have to end
with `while_false`, whose test is false. Induction on the (hypothetical) derivation. -/
theorem loopForever_diverges (s t : State) : ¬ BigStep loopForever s t := by
  intro h
  generalize hw : loopForever = w at h
  induction h with
  | while_true _ _ _ _ ih₂ => exact ih₂ hw
  | while_false hb =>
    cases hw
    simp at hb
  | _ => cases hw
-- @endregion

-- @region formal_methods.loop_forever_hoare
-- @provenance independent
/-- Hence the triple `{true} while true do skip {false}` is **valid** as a partial-correctness
statement — vacuously, because no run terminates. Partial correctness promises nothing about
termination. -/
theorem loopForever_hoare : Hoare (fun _ => True) loopForever (fun _ => False) :=
  fun s t _ h => loopForever_diverges s t h
-- @endregion

/-! ### Type soundness: progress and preservation -/

-- @region formal_methods.tm
-- @provenance definition
/-- Terms of a tiny expression language of booleans and natural numbers (Pierce, *Types and
Programming Languages*, chapter 8). -/
inductive Tm where
  | tru
  | fls
  | ite (c t e : Tm)
  | zero
  | succ (t : Tm)
  | pred (t : Tm)
  | iszero (t : Tm)
-- @endregion

-- @region formal_methods.ty
-- @provenance definition
/-- The two types. -/
inductive Ty where
  | bool
  | nat
-- @endregion

-- @region formal_methods.numval
-- @provenance definition
/-- Numeric values: `zero`, `succ zero`, … -/
inductive NumVal : Tm → Prop where
  | zero : NumVal .zero
  | succ {t : Tm} : NumVal t → NumVal (.succ t)
-- @endregion

-- @region formal_methods.value
-- @provenance definition
/-- Values: the booleans and the numeric values. -/
inductive Value : Tm → Prop where
  | tru : Value .tru
  | fls : Value .fls
  | num {t : Tm} : NumVal t → Value t
-- @endregion

-- @region formal_methods.step
-- @provenance definition
/-- Small-step reduction. A term that is not a value and cannot step is **stuck**, such as
`succ tru` or `if zero then … else …`. -/
inductive Step : Tm → Tm → Prop where
  | ite_tru {t e : Tm} : Step (.ite .tru t e) t
  | ite_fls {t e : Tm} : Step (.ite .fls t e) e
  | ite {c c' t e : Tm} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t' : Tm} : Step t t' → Step (.succ t) (.succ t')
  | pred_zero : Step (.pred .zero) .zero
  | pred_succ {v : Tm} : NumVal v → Step (.pred (.succ v)) v
  | pred {t t' : Tm} : Step t t' → Step (.pred t) (.pred t')
  | iszero_zero : Step (.iszero .zero) .tru
  | iszero_succ {v : Tm} : NumVal v → Step (.iszero (.succ v)) .fls
  | iszero {t t' : Tm} : Step t t' → Step (.iszero t) (.iszero t')
-- @endregion

-- @region formal_methods.has_type
-- @provenance definition
/-- The typing relation `t : T`. -/
inductive HasType : Tm → Ty → Prop where
  | tru : HasType .tru .bool
  | fls : HasType .fls .bool
  | ite {c t e : Tm} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
  | zero : HasType .zero .nat
  | succ {t : Tm} : HasType t .nat → HasType (.succ t) .nat
  | pred {t : Tm} : HasType t .nat → HasType (.pred t) .nat
  | iszero {t : Tm} : HasType t .nat → HasType (.iszero t) .bool
-- @endregion

-- @region formal_methods.numval_has_type
-- @provenance independent
/-- Every numeric value has type `nat`. -/
theorem numVal_hasType {t : Tm} (h : NumVal t) : HasType t .nat := by
  induction h with
  | zero => exact .zero
  | succ _ ih => exact .succ ih
-- @endregion

-- @region formal_methods.progress
-- @provenance independent
/-- **Progress.** A well-typed term is a value or can take a step. Induction on the typing
derivation, using the *canonical forms*: a value of type `bool` is `tru` or `fls`, and a value
of type `nat` is a numeric value. -/
theorem progress {t : Tm} {T : Ty} (h : HasType t T) : Value t ∨ ∃ t', Step t t' := by
  induction h with
  | tru => exact .inl .tru
  | fls => exact .inl .fls
  | zero => exact .inl (.num .zero)
  | @ite c t e T hc _ _ ihc _ _ =>
    right
    rcases ihc with hv | ⟨c', hs⟩
    · cases hv with
      | tru => exact ⟨t, .ite_tru⟩
      | fls => exact ⟨e, .ite_fls⟩
      | num hn => cases hn <;> cases hc
    · exact ⟨_, .ite hs⟩
  | succ _ ih =>
    rcases ih with hv | ⟨t', hs⟩
    · cases hv with
      | tru => contradiction
      | fls => contradiction
      | num hn => exact .inl (.num (.succ hn))
    · exact .inr ⟨_, .succ hs⟩
  | pred _ ih =>
    right
    rcases ih with hv | ⟨t', hs⟩
    · cases hv with
      | tru => contradiction
      | fls => contradiction
      | num hn =>
        cases hn with
        | zero => exact ⟨_, .pred_zero⟩
        | succ hn => exact ⟨_, .pred_succ hn⟩
    · exact ⟨_, .pred hs⟩
  | iszero _ ih =>
    right
    rcases ih with hv | ⟨t', hs⟩
    · cases hv with
      | tru => contradiction
      | fls => contradiction
      | num hn =>
        cases hn with
        | zero => exact ⟨_, .iszero_zero⟩
        | succ hn => exact ⟨_, .iszero_succ hn⟩
    · exact ⟨_, .iszero hs⟩
-- @endregion

-- @region formal_methods.preservation
-- @provenance independent
/-- **Preservation.** Reduction preserves types: if `t : T` and `t ⟶ t'` then `t' : T`.
Induction on the typing derivation, inverting the step. -/
theorem preservation {t t' : Tm} {T : Ty} (h : HasType t T) (hs : Step t t') :
    HasType t' T := by
  induction h generalizing t' with
  | tru => cases hs
  | fls => cases hs
  | zero => cases hs
  | ite hc ht he ihc _ _ =>
    cases hs with
    | ite_tru => exact ht
    | ite_fls => exact he
    | ite hs' => exact .ite (ihc hs') ht he
  | succ _ ih =>
    cases hs with
    | succ hs' => exact .succ (ih hs')
  | pred ht ih =>
    cases hs with
    | pred_zero => exact .zero
    | pred_succ hv => exact numVal_hasType hv
    | pred hs' => exact .pred (ih hs')
  | iszero _ ih =>
    cases hs with
    | iszero_zero => exact .tru
    | iszero_succ _ => exact .fls
    | iszero hs' => exact .iszero (ih hs')
-- @endregion

-- @region formal_methods.type_safety
-- @provenance independent
/-- **Type safety** ("well-typed programs cannot go wrong", Milner): every term reachable from a
well-typed term by any number of steps is a value or can step again — it is never stuck.
Induction on the reduction sequence, using preservation at each step and progress at the end. -/
theorem type_safety {t t' : Tm} {T : Ty} (h : HasType t T)
    (hs : Relation.ReflTransGen Step t t') : Value t' ∨ ∃ t'', Step t' t'' := by
  have : HasType t' T := by
    induction hs with
    | refl => exact h
    | tail _ hstep ih => exact preservation ih hstep
  exact progress this
-- @endregion

/-! ### Model checking: `EF φ` is a least fixed point -/

-- @region formal_methods.ef
-- @provenance definition
/-- In a transition system with relation `R`, the CTL formula `EF φ` ("along some path, φ
eventually holds") is satisfied by the states from which a `φ`-state is reachable. -/
def EF {S : Type*} (R : S → S → Prop) (φ : Set S) : Set S :=
  {s | ∃ t, Relation.ReflTransGen R s t ∧ t ∈ φ}
-- @endregion

-- @region formal_methods.ef_step
-- @provenance definition
/-- The monotone operator `Z ↦ φ ∪ pre(Z)`, where `pre(Z)` is the set of states with a
successor in `Z`. A model checker computes `EF φ` by iterating it from `∅`. -/
def efStep {S : Type*} (R : S → S → Prop) (φ : Set S) : Set S →o Set S where
  toFun Z := φ ∪ {s | ∃ t, R s t ∧ t ∈ Z}
  monotone' := fun _ _ hZ _ hs =>
    hs.elim Or.inl fun ⟨t, hst, ht⟩ => Or.inr ⟨t, hst, hZ ht⟩
-- @endregion

-- @region formal_methods.ef_eq_lfp
-- @provenance independent
/-- **`EF φ = μZ. φ ∪ pre(Z)`.** The set `EF φ` is the least fixed point of `efStep` (which
exists by the Knaster–Tarski theorem, Mathlib's `OrderHom.lfp`). One inclusion: `EF φ` is closed
under the operator, so it contains the least fixed point (`OrderHom.lfp_le`). The other: by
induction along a path to `φ`, every state of `EF φ` lies in every fixed point. -/
theorem ef_eq_lfp {S : Type*} (R : S → S → Prop) (φ : Set S) :
    EF R φ = OrderHom.lfp (efStep R φ) := by
  apply le_antisymm
  · rintro s ⟨t, hst, ht⟩
    have hfix := OrderHom.map_lfp (efStep R φ)
    induction hst using Relation.ReflTransGen.head_induction_on with
    | refl => rw [← hfix]; exact Or.inl ht
    | head hsu _ ih => rw [← hfix]; exact Or.inr ⟨_, hsu, ih⟩
  · apply OrderHom.lfp_le
    rintro s (hs | ⟨u, hsu, t, hut, ht⟩)
    · exact ⟨s, .refl, hs⟩
    · exact ⟨t, .head hsu hut, ht⟩
-- @endregion

/-! ### The limit: Rice's theorem -/

-- @region formal_methods.rice
-- @provenance library
/-- **Rice's theorem.** Let `C` be a set of partial functions `ℕ →. ℕ` such that membership of
a program's *behaviour* in `C` is decidable. If one partial recursive function lies in `C`, all
of them do: every decidable semantic property is trivial. This applies Mathlib's
`ComputablePred.rice`. -/
theorem rice (C : Set (ℕ →. ℕ))
    (h : ComputablePred fun c => Nat.Partrec.Code.eval c ∈ C)
    {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C :=
  ComputablePred.rice C h hf hg fC
-- @endregion

end Lumenary.FormalMethods
