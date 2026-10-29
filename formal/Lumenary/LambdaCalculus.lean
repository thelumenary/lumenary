/-
The Lumenary — formal mathematics
The λ-calculus: terms with de Bruijn indices, capture-avoiding substitution, β-reduction,
a term without a normal form, fixed-point combinators, Church numerals, and the
Church–Rosser theorem.

What is proved here (all independently, from the definitions in this file).
* **Syntax and substitution.** Untyped λ-terms with de Bruijn indices (a variable is the number
  of binders between it and its λ), so α-equivalent terms are literally equal and substitution
  cannot capture variables. Simultaneous substitution and its algebra (fusion laws).
* **Non-termination.** `Ω = (λx. x x)(λx. x x)` reduces only to itself, so it has no normal
  form. Turing's `Θ` satisfies `Θ F ↠ F (Θ F)`, and Curry's `Y F` and `F (Y F)` have a common
  reduct.
* **Church numerals.** A normal-order evaluator, proved sound (every step it takes is a
  β-step) and complete for normal forms (when it stops, no β-step applies); with it, the kernel
  computes `2 + 3 ↠ 5` and `2 × 3 ↠ 6`.
* **Church–Rosser.** β-reduction is confluent, by Tait and Martin-Löf's parallel reduction and
  Takahashi's complete developments; hence a term has at most one normal form. The abstract
  step "a diamond property for `→` gives confluence of `↠`" is proved from scratch and compared
  with Mathlib's `Relation.church_rosser`.

What is not formalised here: η-reduction, standardisation (normal order finds a normal form
whenever one exists), the equivalence with partial recursive functions, and normalisation of
the simply typed λ-calculus (see the lesson for proofs and references).
-/
import Mathlib.Logic.Relation

namespace Lumenary.LambdaCalculus

open Relation

/-! ### Terms and substitution -/

-- @region lambda_calculus.term
-- @provenance definition
/-- Untyped λ-terms with **de Bruijn indices**: `var n` refers to the variable bound by the
`n`-th enclosing `lam`, counting outwards from `0`. So `λx. λy. x` is `lam (lam (var 1))`, and
α-equivalent terms such as `λx. x` and `λy. y` are the same term `lam (var 0)`. -/
inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq, Repr
-- @endregion

open Term

-- @region lambda_calculus.up_ren
-- @provenance definition
/-- Lift a renaming `ξ` of variables under one binder: index `0` (the new bound variable) stays,
and every other index `n + 1` goes to `ξ n + 1`. -/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1
-- @endregion

-- @region lambda_calculus.rename
-- @provenance definition
/-- Rename the free variables of a term by `ξ`. -/
def rename (ξ : Nat → Nat) : Term → Term
  | var n => var (ξ n)
  | app s t => app (rename ξ s) (rename ξ t)
  | lam t => lam (rename (upRen ξ) t)
-- @endregion

-- @region lambda_calculus.up
-- @provenance definition
/-- Lift a substitution `σ` (a term for each free variable) under one binder: the new bound
variable stays put, and the substituted terms are shifted so that their free variables skip the
new binder. This shift is exactly what makes substitution **capture-avoiding**. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)
-- @endregion

-- @region lambda_calculus.subst
-- @provenance definition
/-- Simultaneous capture-avoiding substitution: replace each free variable `n` by `σ n`. -/
def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | app s t => app (subst σ s) (subst σ t)
  | lam t => lam (subst (up σ) t)
-- @endregion

-- @region lambda_calculus.scons
-- @provenance definition
/-- `scons s σ` sends `0 ↦ s` and `n + 1 ↦ σ n`. -/
def scons (s : Term) (σ : Nat → Term) : Nat → Term
  | 0 => s
  | n + 1 => σ n
-- @endregion

-- @region lambda_calculus.inst
-- @provenance definition
/-- `inst t s` is `t[s/x]` for the variable `x` bound by an enclosing `λ`: index `0` becomes
`s`, and the other free indices drop by one because that `λ` has disappeared. -/
def inst (t s : Term) : Term :=
  subst (scons s var) t
-- @endregion

/-! ### The algebra of substitution -/

-- @region lambda_calculus.rename_rename
-- @provenance independent
/-- Renaming twice is renaming once by the composite. -/
theorem rename_rename (t : Term) : ∀ (ξ ζ : Nat → Nat),
    rename ξ (rename ζ t) = rename (ξ ∘ ζ) t := by
  induction t with
  | var n => intro ξ ζ; rfl
  | app s t ihs iht => intro ξ ζ; simp [rename, ihs, iht]
  | lam t ih =>
    intro ξ ζ
    simp only [rename, ih]
    congr 2
    funext n
    cases n <;> rfl
-- @endregion

-- @region lambda_calculus.subst_rename
-- @provenance independent
/-- Substituting after renaming is substituting the renamed substitution. -/
theorem subst_rename (t : Term) : ∀ (σ : Nat → Term) (ξ : Nat → Nat),
    subst σ (rename ξ t) = subst (σ ∘ ξ) t := by
  induction t with
  | var n => intro σ ξ; rfl
  | app s t ihs iht => intro σ ξ; simp [rename, subst, ihs, iht]
  | lam t ih =>
    intro σ ξ
    simp only [rename, subst, ih]
    congr 2
    funext n
    cases n <;> rfl
-- @endregion

-- @region lambda_calculus.rename_subst
-- @provenance independent
/-- Renaming after substituting is substituting renamed terms. -/
theorem rename_subst (t : Term) : ∀ (ξ : Nat → Nat) (σ : Nat → Term),
    rename ξ (subst σ t) = subst (rename ξ ∘ σ) t := by
  induction t with
  | var n => intro ξ σ; rfl
  | app s t ihs iht => intro ξ σ; simp [rename, subst, ihs, iht]
  | lam t ih =>
    intro ξ σ
    simp only [rename, subst, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ k =>
      show rename (upRen ξ) (rename Nat.succ (σ k)) = rename Nat.succ (rename ξ (σ k))
      rw [rename_rename, rename_rename]
      rfl
-- @endregion

-- @region lambda_calculus.subst_subst
-- @provenance independent
/-- **Substitution is associative**: substituting `σ` and then `τ` is substituting the
composite `n ↦ subst τ (σ n)`. -/
theorem subst_subst (t : Term) : ∀ (σ τ : Nat → Term),
    subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  induction t with
  | var n => intro σ τ; rfl
  | app s t ihs iht => intro σ τ; simp [subst, ihs, iht]
  | lam t ih =>
    intro σ τ
    simp only [subst, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ k =>
      show subst (up τ) (rename Nat.succ (σ k)) = rename Nat.succ (subst τ (σ k))
      rw [subst_rename, rename_subst]
      rfl
-- @endregion

-- @region lambda_calculus.subst_var
-- @provenance independent
/-- Substituting every variable by itself does nothing. -/
theorem subst_var (t : Term) : ∀ (σ : Nat → Term), (∀ n, σ n = var n) → subst σ t = t := by
  induction t with
  | var n => intro σ h; exact h n
  | app s t ihs iht => intro σ h; simp [subst, ihs σ h, iht σ h]
  | lam t ih =>
    intro σ h
    simp only [subst]
    rw [ih]
    intro n
    cases n with
    | zero => rfl
    | succ k => simp [up, h k, rename]
-- @endregion

-- @region lambda_calculus.rename_inst
-- @provenance independent
/-- Renaming commutes with instantiation (renaming under the binder on the left). -/
theorem rename_inst (ξ : Nat → Nat) (t s : Term) :
    rename ξ (inst t s) = inst (rename (upRen ξ) t) (rename ξ s) := by
  simp only [inst, rename_subst, subst_rename]
  congr 1
  funext n
  cases n <;> rfl
-- @endregion

-- @region lambda_calculus.subst_inst
-- @provenance independent
/-- **The substitution lemma**: `(t[s/x])σ = (tσ')[sσ/x]`, where `σ'` is `σ` lifted under the
binder of `x`. -/
theorem subst_inst (σ : Nat → Term) (t s : Term) :
    subst σ (inst t s) = inst (subst (up σ) t) (subst σ s) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ k =>
    show σ k = subst (scons (subst σ s) var) (rename Nat.succ (σ k))
    rw [subst_rename, subst_var]
    intro m
    rfl
-- @endregion

/-! ### β-reduction -/

-- @region lambda_calculus.step
-- @provenance definition
/-- One step of **β-reduction**, anywhere in a term: `(λx. t) s → t[s/x]`, also inside
applications and under λ. -/
inductive Step : Term → Term → Prop where
  | beta (t s : Term) : Step (app (lam t) s) (inst t s)
  | appL {s s' : Term} (t : Term) : Step s s' → Step (app s t) (app s' t)
  | appR (s : Term) {t t' : Term} : Step t t' → Step (app s t) (app s t')
  | lam {t t' : Term} : Step t t' → Step (lam t) (lam t')
-- @endregion

-- @region lambda_calculus.normal
-- @provenance definition
/-- A term is in **normal form** if no β-step applies to it. -/
def Normal (t : Term) : Prop :=
  ∀ u, ¬ Step t u
-- @endregion

-- @region lambda_calculus.steps_app
-- @provenance independent
/-- Many-step reduction `↠` (the reflexive–transitive closure `ReflTransGen Step`) is a
congruence for application. -/
theorem steps_app {s s' t t' : Term} (hs : ReflTransGen Step s s')
    (ht : ReflTransGen Step t t') : ReflTransGen Step (app s t) (app s' t') :=
  (hs.lift (fun x => app x t) fun _ _ h => Step.appL t h).trans
    (ht.lift (fun y => app s' y) fun _ _ h => Step.appR s' h)
-- @endregion

-- @region lambda_calculus.steps_lam
-- @provenance independent
/-- Many-step reduction is a congruence for abstraction. -/
theorem steps_lam {t t' : Term} (h : ReflTransGen Step t t') :
    ReflTransGen Step (lam t) (lam t') :=
  h.lift lam fun _ _ h => Step.lam h
-- @endregion

/-! ### A term with no normal form -/

-- @region lambda_calculus.omega
-- @provenance definition
/-- `ω = λx. x x`, which applies its argument to itself. -/
def omega : Term := lam (app (var 0) (var 0))
-- @endregion

-- @region lambda_calculus.big_omega
-- @provenance definition
/-- `Ω = ω ω = (λx. x x)(λx. x x)`. -/
def bigOmega : Term := app omega omega
-- @endregion

-- @region lambda_calculus.omega_normal
-- @provenance independent
/-- `ω = λx. x x` itself is in normal form: its body `x x` is an application of a variable,
which is not a redex. -/
theorem omega_normal : Normal omega := by
  intro u h
  cases h with
  | lam h' =>
    cases h' with
    | appL _ h'' => cases h''
    | appR _ h'' => cases h''
-- @endregion

-- @region lambda_calculus.big_omega_step
-- @provenance independent
/-- **Ω reduces to itself and to nothing else.** The only redex is the whole term, and
contracting it substitutes `ω` for `x` in `x x`, giving `ω ω` back. -/
theorem bigOmega_step (u : Term) : Step bigOmega u ↔ u = bigOmega := by
  constructor
  · intro h
    cases h with
    | beta => rfl
    | appL _ h' => exact absurd h' (omega_normal _)
    | appR _ h' => exact absurd h' (omega_normal _)
  · rintro rfl
    exact Step.beta _ _
-- @endregion

-- @region lambda_calculus.big_omega_no_normal_form
-- @provenance independent
/-- **Ω has no normal form**: everything it reduces to is Ω, and Ω is not normal. So the untyped
λ-calculus has non-terminating computations. -/
theorem bigOmega_no_normal_form : ¬ ∃ u, ReflTransGen Step bigOmega u ∧ Normal u := by
  rintro ⟨u, hu, hn⟩
  have only : ∀ w, ReflTransGen Step bigOmega w → w = bigOmega := by
    intro w hw
    induction hw with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      exact (bigOmega_step _).1 hstep
  have := only u hu
  subst this
  exact hn bigOmega ((bigOmega_step bigOmega).2 rfl)
-- @endregion

/-! ### Fixed-point combinators -/

-- @region lambda_calculus.theta
-- @provenance definition
/-- **Turing's fixed-point combinator** `Θ = A A` with `A = λx. λy. y (x x y)`. -/
def theta : Term :=
  app (lam (lam (app (var 0) (app (app (var 1) (var 1)) (var 0)))))
    (lam (lam (app (var 0) (app (app (var 1) (var 1)) (var 0)))))
-- @endregion

-- @region lambda_calculus.theta_fixed_point
-- @provenance independent
/-- **`Θ F ↠ F (Θ F)` for every term `F`** — in two β-steps. This is how the untyped calculus
defines recursive functions: a solution of `f = F f`. -/
theorem theta_fixed_point (F : Term) : ReflTransGen Step (app theta F) (app F (app theta F)) := by
  refine ReflTransGen.head (Step.appL F (Step.beta _ _)) ?_
  exact ReflTransGen.single (Step.beta _ _)
-- @endregion

-- @region lambda_calculus.curry_y
-- @provenance definition
/-- **Curry's paradoxical combinator** `Y = λf. (λx. f (x x)) (λx. f (x x))`. -/
def curryY : Term :=
  lam (app (lam (app (var 1) (app (var 0) (var 0))))
    (lam (app (var 1) (app (var 0) (var 0)))))
-- @endregion

-- @region lambda_calculus.curry_y_fixed_point
-- @provenance independent
/-- **`Y F` and `F (Y F)` reduce to a common term**, so they are β-equal. (Unlike `Θ`, `Y F`
does not reduce to `F (Y F)` itself.) With `W = λx. F (x x)`: `Y F → W W → F (W W)` and
`F (Y F) → F (W W)`. -/
theorem curryY_fixed_point (F : Term) :
    ∃ N, ReflTransGen Step (app curryY F) N ∧ ReflTransGen Step (app F (app curryY F)) N := by
  let W : Term := lam (app (rename Nat.succ F) (app (var 0) (var 0)))
  have h1 : Step (app curryY F) (app W W) := Step.beta _ _
  have h2 : Step (app W W) (app F (app W W)) := by
    have e : inst (app (rename Nat.succ F) (app (var 0) (var 0))) W = app F (app W W) := by
      simp only [inst, subst]
      rw [subst_rename, subst_var]
      · rfl
      · intro n
        rfl
    rw [← e]
    exact Step.beta _ _
  exact ⟨app F (app W W), ReflTransGen.head h1 (ReflTransGen.single h2),
    ReflTransGen.single (Step.appR F h1)⟩
-- @endregion

/-! ### Church numerals and a normal-order evaluator -/

-- @region lambda_calculus.iterate
-- @provenance definition
/-- `iterate n = f (f (… (f x)))` with `n` copies of `f`, where `f` is index `1` and `x` is
index `0`. -/
def iterate : Nat → Term
  | 0 => var 0
  | n + 1 => app (var 1) (iterate n)
-- @endregion

-- @region lambda_calculus.church
-- @provenance definition
/-- The **Church numeral** `n̄ = λf. λx. fⁿ x`: the number `n` as "do something `n` times". -/
def church (n : Nat) : Term := lam (lam (iterate n))
-- @endregion

-- @region lambda_calculus.plus
-- @provenance definition
/-- `plus = λm. λn. λf. λx. m f (n f x)`: do `f` `n` times, then `m` more times. -/
def plus : Term :=
  lam (lam (lam (lam (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))
-- @endregion

-- @region lambda_calculus.times
-- @provenance definition
/-- `times = λm. λn. λf. m (n f)`: repeat "do `f` `n` times" `m` times. -/
def times : Term := lam (lam (lam (app (var 2) (app (var 1) (var 0)))))
-- @endregion

-- @region lambda_calculus.step_normal_order
-- @provenance definition
/-- One step of **normal-order** (leftmost-outermost) reduction, or `none` if the term is
normal: contract the head redex if there is one, otherwise reduce inside, left to right. -/
def stepNO : Term → Option Term
  | var _ => none
  | lam t => (stepNO t).map lam
  | app (lam t) s => some (inst t s)
  | app (var n) t => (stepNO t).map (app (var n))
  | app (app s₁ s₂) t =>
    match stepNO (app s₁ s₂) with
    | some s' => some (app s' t)
    | none => (stepNO t).map (app (app s₁ s₂))
-- @endregion

-- @region lambda_calculus.normalize
-- @provenance definition
/-- Run normal-order reduction for at most `fuel` steps. -/
def normalize : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
    match stepNO t with
    | some u => normalize fuel u
    | none => t
-- @endregion

-- @region lambda_calculus.step_normal_order_sound
-- @provenance independent
/-- **The evaluator is sound**: every step it takes is a β-step. -/
theorem stepNO_sound (t : Term) : ∀ u, stepNO t = some u → Step t u := by
  induction t with
  | var n => intro u h; cases h
  | lam t ih =>
    intro u h
    simp only [stepNO, Option.map_eq_some_iff] at h
    obtain ⟨t', ht', rfl⟩ := h
    exact Step.lam (ih t' ht')
  | app s t ihs iht =>
    intro u h
    cases s with
    | var n =>
      simp only [stepNO, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', rfl⟩ := h
      exact Step.appR _ (iht t' ht')
    | lam s₀ =>
      simp only [stepNO, Option.some.injEq] at h
      subst h
      exact Step.beta _ _
    | app s₁ s₂ =>
      simp only [stepNO] at h
      split at h
      · rename_i s' hs'
        simp only [Option.some.injEq] at h
        subst h
        exact Step.appL _ (ihs s' hs')
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨t', ht', rfl⟩ := h
        exact Step.appR _ (iht t' ht')
-- @endregion

-- @region lambda_calculus.step_normal_order_none
-- @provenance independent
/-- **When the evaluator stops, the term is normal**: if normal order finds no redex, there is
no redex at all. -/
theorem stepNO_none (t : Term) : stepNO t = none → Normal t := by
  induction t with
  | var n => intro _ u h; cases h
  | lam t ih =>
    intro h u hu
    simp only [stepNO, Option.map_eq_none_iff] at h
    cases hu with
    | lam h' => exact ih h _ h'
  | app s t ihs iht =>
    intro h u hu
    cases s with
    | var n =>
      simp only [stepNO, Option.map_eq_none_iff] at h
      cases hu with
      | appL _ h' => cases h'
      | appR _ h' => exact iht h _ h'
    | lam s₀ => simp [stepNO] at h
    | app s₁ s₂ =>
      simp only [stepNO] at h
      split at h
      · cases h
      · rename_i hs
        simp only [Option.map_eq_none_iff] at h
        cases hu with
        | appL _ h' => exact ihs hs _ h'
        | appR _ h' => exact iht h _ h'
-- @endregion

-- @region lambda_calculus.normalize_steps
-- @provenance independent
/-- Whatever the evaluator returns is a β-reduct of the input. -/
theorem normalize_steps (fuel : Nat) : ∀ t, ReflTransGen Step t (normalize fuel t) := by
  induction fuel with
  | zero => intro t; exact ReflTransGen.refl
  | succ fuel ih =>
    intro t
    simp only [normalize]
    split
    · rename_i u hu
      exact ReflTransGen.head (stepNO_sound t u hu) (ih u)
    · exact ReflTransGen.refl
-- @endregion

-- @region lambda_calculus.church_normal
-- @provenance independent
/-- Church numerals are in normal form. -/
theorem church_normal (n : Nat) : Normal (church n) := by
  apply stepNO_none
  have h : ∀ k, stepNO (iterate k) = none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [iterate, stepNO, ih]
  simp [church, stepNO, h]
-- @endregion

-- @region lambda_calculus.two_plus_three
-- @provenance independent
/-- **`plus 2̄ 3̄ ↠ 5̄`**. The kernel runs the evaluator (6 normal-order steps) and checks that
the result is the Church numeral `5̄`; soundness turns the run into a β-reduction. -/
theorem two_plus_three : ReflTransGen Step (app (app plus (church 2)) (church 3)) (church 5) := by
  have h : normalize 20 (app (app plus (church 2)) (church 3)) = church 5 := by decide
  rw [← h]
  exact normalize_steps 20 _
-- @endregion

-- @region lambda_calculus.two_times_three
-- @provenance independent
/-- **`times 2̄ 3̄ ↠ 6̄`**, computed the same way. -/
theorem two_times_three : ReflTransGen Step (app (app times (church 2)) (church 3)) (church 6) := by
  have h : normalize 30 (app (app times (church 2)) (church 3)) = church 6 := by decide
  rw [← h]
  exact normalize_steps 30 _
-- @endregion

/-! ### Confluence, abstractly -/

section Abstract

variable {α : Type*} (r : α → α → Prop)

-- @region lambda_calculus.diamond
-- @provenance definition
/-- A relation has the **diamond property** if any two one-step reducts of a term can be
joined by one more step on each side. -/
def Diamond : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d
-- @endregion

variable {r}

-- @region lambda_calculus.strip
-- @provenance independent
/-- **The strip lemma**: if `r` has the diamond property, a single `r`-step and a many-step
`r`-reduction from the same term can be joined (one step on the far side, many on the other).
Induction along the many-step reduction, tiling one diamond at a time. -/
theorem strip (hd : Diamond r) {a b c : α} (hab : r a b) (hac : ReflTransGen r a c) :
    ∃ d, ReflTransGen r b d ∧ r c d := by
  induction hac with
  | refl => exact ⟨b, ReflTransGen.refl, hab⟩
  | tail _ hcc' ih =>
    obtain ⟨d, hbd, hcd⟩ := ih
    obtain ⟨e, hde, hc'e⟩ := hd _ _ _ hcd hcc'
    exact ⟨e, hbd.tail hde, hc'e⟩
-- @endregion

-- @region lambda_calculus.diamond_confluent
-- @provenance independent
/-- **Diamond implies confluence**: if `r` has the diamond property, then any two many-step
reducts of a term have a common many-step reduct. Induction along one reduction, using the
strip lemma for each of its steps. -/
theorem diamond_confluent (hd : Diamond r) {a b c : α} (hab : ReflTransGen r a b)
    (hac : ReflTransGen r a c) : ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d := by
  induction hab with
  | refl => exact ⟨c, hac, ReflTransGen.refl⟩
  | tail _ hbb' ih =>
    obtain ⟨d, hbd, hcd⟩ := ih
    obtain ⟨e, hb'e, hde⟩ := strip hd hbb' hbd
    exact ⟨e, hb'e, hcd.tail hde⟩
-- @endregion

-- @region lambda_calculus.church_rosser_library
-- @provenance library
/-- The same abstract fact from Mathlib, in a slightly stronger form (Mathlib's
`Relation.church_rosser` only needs the joining step on one side to be optional). -/
theorem church_rosser_library (hd : Diamond r) {a b c : α} (hab : ReflTransGen r a b)
    (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c :=
  Relation.church_rosser (fun a b c hab hac =>
    let ⟨d, hbd, hcd⟩ := hd a b c hab hac
    ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩) hab hac
-- @endregion

end Abstract

/-! ### Parallel reduction and the Church–Rosser theorem -/

-- @region lambda_calculus.par
-- @provenance definition
/-- **Parallel reduction** `t ⇒ t'` (Tait, Martin-Löf): contract any set of redexes already
present in `t`, all at once. Unlike `→`, it has the diamond property. -/
inductive Par : Term → Term → Prop where
  | var (n : Nat) : Par (var n) (var n)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (app s t) (app s' t')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {t t' s s' : Term} : Par t t' → Par s s' → Par (app (lam t) s) (inst t' s')
-- @endregion

-- @region lambda_calculus.par_refl
-- @provenance independent
/-- Parallel reduction is reflexive (contract no redexes). -/
theorem par_refl (t : Term) : Par t t := by
  induction t with
  | var n => exact Par.var n
  | app s t ihs iht => exact Par.app ihs iht
  | lam t ih => exact Par.lam ih
-- @endregion

-- @region lambda_calculus.par_of_step
-- @provenance independent
/-- A single β-step is a parallel reduction. -/
theorem par_of_step {t u : Term} (h : Step t u) : Par t u := by
  induction h with
  | beta t s => exact Par.beta (par_refl t) (par_refl s)
  | appL t _ ih => exact Par.app ih (par_refl t)
  | appR s _ ih => exact Par.app (par_refl s) ih
  | lam _ ih => exact Par.lam ih
-- @endregion

-- @region lambda_calculus.steps_of_par
-- @provenance independent
/-- A parallel reduction can be done one β-step at a time. -/
theorem steps_of_par {t u : Term} (h : Par t u) : ReflTransGen Step t u := by
  induction h with
  | var n => exact ReflTransGen.refl
  | app _ _ ihs iht => exact steps_app ihs iht
  | lam _ ih => exact steps_lam ih
  | beta _ _ iht ihs =>
    exact (steps_app (steps_lam iht) ihs).tail (Step.beta _ _)
-- @endregion

-- @region lambda_calculus.par_rename
-- @provenance independent
/-- Parallel reduction is preserved by renaming variables. -/
theorem par_rename {t t' : Term} (h : Par t t') : ∀ ξ, Par (rename ξ t) (rename ξ t') := by
  induction h with
  | var n => intro ξ; exact Par.var _
  | app _ _ ihs iht => intro ξ; exact Par.app (ihs ξ) (iht ξ)
  | lam _ ih => intro ξ; exact Par.lam (ih _)
  | beta _ _ iht ihs =>
    intro ξ
    rw [rename_inst]
    exact Par.beta (iht _) (ihs ξ)
-- @endregion

-- @region lambda_calculus.par_subst
-- @provenance independent
/-- **Parallel reduction is preserved by substitution**: if `t ⇒ t'` and `σ n ⇒ τ n` for every
variable `n`, then `tσ ⇒ t'τ`. The β case is the substitution lemma `subst_inst`. -/
theorem par_subst {t t' : Term} (h : Par t t') :
    ∀ σ τ, (∀ n, Par (σ n) (τ n)) → Par (subst σ t) (subst τ t') := by
  induction h with
  | var n => intro σ τ hστ; exact hστ n
  | app _ _ ihs iht => intro σ τ hστ; exact Par.app (ihs σ τ hστ) (iht σ τ hστ)
  | lam _ ih =>
    intro σ τ hστ
    refine Par.lam (ih _ _ ?_)
    intro n
    cases n with
    | zero => exact Par.var 0
    | succ k => exact par_rename (hστ k) _
  | beta _ _ iht ihs =>
    intro σ τ hστ
    rw [subst_inst]
    refine Par.beta (iht _ _ ?_) (ihs σ τ hστ)
    intro n
    cases n with
    | zero => exact Par.var 0
    | succ k => exact par_rename (hστ k) _
-- @endregion

-- @region lambda_calculus.par_inst
-- @provenance independent
/-- If `t ⇒ t'` and `s ⇒ s'`, then `t[s/x] ⇒ t'[s'/x]`. -/
theorem par_inst {t t' s s' : Term} (ht : Par t t') (hs : Par s s') :
    Par (inst t s) (inst t' s') := by
  apply par_subst ht
  intro n
  cases n with
  | zero => exact hs
  | succ k => exact Par.var k
-- @endregion

-- @region lambda_calculus.complete_development
-- @provenance definition
/-- **The complete development** `t*` (Takahashi): contract *every* redex present in `t`,
innermost information first. -/
def cd : Term → Term
  | var n => var n
  | lam t => lam (cd t)
  | app (lam t) s => inst (cd t) (cd s)
  | app (var n) t => app (var n) (cd t)
  | app (app s₁ s₂) t => app (cd (app s₁ s₂)) (cd t)
-- @endregion

-- @region lambda_calculus.triangle
-- @provenance independent
/-- **The triangle property**: if `t ⇒ u`, then `u ⇒ t*`. Every parallel reduct of `t` can
catch up with the complete development of `t` in one more parallel step. -/
theorem triangle {t u : Term} (h : Par t u) : Par u (cd t) := by
  induction h with
  | var n => exact Par.var n
  | lam _ ih => exact Par.lam ih
  | beta _ _ iht ihs => exact par_inst iht ihs
  | @app s s' t t' hs _ ihs iht =>
    cases s with
    | var n => exact Par.app ihs iht
    | app s₁ s₂ => exact Par.app ihs iht
    | lam s₀ =>
      cases hs with
      | lam hs₀ =>
        cases ihs with
        | lam ih₀ => exact Par.beta ih₀ iht
-- @endregion

-- @region lambda_calculus.par_diamond
-- @provenance independent
/-- Parallel reduction has the **diamond property**: two parallel reducts of `t` both reduce in
one parallel step to the complete development `t*`. -/
theorem par_diamond : Diamond Par :=
  fun t _ _ hu hv => ⟨cd t, triangle hu, triangle hv⟩
-- @endregion

-- @region lambda_calculus.steps_iff_par_steps
-- @provenance independent
/-- Many β-steps and many parallel steps are the same relation, since
`→ ⊆ ⇒ ⊆ ↠`. -/
theorem steps_iff_par_steps {t u : Term} : ReflTransGen Step t u ↔ ReflTransGen Par t u := by
  constructor
  · intro h
    exact h.lift id fun _ _ hs => par_of_step hs
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hp ih => exact ih.trans (steps_of_par hp)
-- @endregion

-- @region lambda_calculus.church_rosser
-- @provenance independent
/-- **The Church–Rosser theorem** (Church and Rosser, 1936): β-reduction is confluent. If
`t ↠ u` and `t ↠ v`, there is a `w` with `u ↠ w` and `v ↠ w`. Proof: confluence of parallel
reduction (diamond ⇒ confluence), transported along `↠ = ⇒*`. -/
theorem church_rosser {t u v : Term} (hu : ReflTransGen Step t u) (hv : ReflTransGen Step t v) :
    ∃ w, ReflTransGen Step u w ∧ ReflTransGen Step v w := by
  obtain ⟨w, huw, hvw⟩ :=
    diamond_confluent par_diamond (steps_iff_par_steps.1 hu) (steps_iff_par_steps.1 hv)
  exact ⟨w, steps_iff_par_steps.2 huw, steps_iff_par_steps.2 hvw⟩
-- @endregion

-- @region lambda_calculus.normal_form_unique
-- @provenance independent
/-- **Normal forms are unique**: a term has at most one normal form. By Church–Rosser two normal
forms `u, v` of `t` reduce to a common `w`; a normal term reduces only to itself, so
`u = w = v`. -/
theorem normal_form_unique {t u v : Term} (hu : ReflTransGen Step t u) (hv : ReflTransGen Step t v)
    (nu : Normal u) (nv : Normal v) : u = v := by
  have stuck : ∀ {x y : Term}, Normal x → ReflTransGen Step x y → x = y := by
    intro x y nx hxy
    cases hxy.cases_head with
    | inl h => exact h
    | inr h =>
      obtain ⟨z, hxz, _⟩ := h
      exact absurd hxz (nx z)
  obtain ⟨w, huw, hvw⟩ := church_rosser hu hv
  rw [stuck nu huw, stuck nv hvw]
-- @endregion

-- @region lambda_calculus.plus_unique_value
-- @provenance independent
/-- Consequently `5̄` is *the* normal form of `plus 2̄ 3̄`: no reduction strategy can produce a
different normal form. -/
theorem plus_unique_value {v : Term} (hv : ReflTransGen Step (app (app plus (church 2)) (church 3)) v)
    (nv : Normal v) : v = church 5 :=
  (normal_form_unique two_plus_three hv (church_normal 5) nv).symm
-- @endregion

end Lumenary.LambdaCalculus
