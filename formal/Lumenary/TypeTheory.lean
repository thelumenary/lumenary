/-
The Lumenary — formal mathematics
Type theory and propositions as types: Lean's own logic read as programs, Π and Σ types,
inductive types with their induction principles, and the Curry–Howard correspondence for the
simply typed λ-calculus proved as a theorem.

What is proved here (all independently, in core Lean — no Mathlib is needed).
* **Proofs are programs.** The K and S combinators prove `A → B → A` and
  `(A → B → C) → (A → B) → A → C`; `¬¬(A ∨ ¬A)` has a constructive proof, while Peirce's law
  `((A → B) → A) → A` is proved only with the axiom of excluded middle (`Classical.em`).
* **Π and Σ.** `∀ n, ∃ m, n < m` is a function returning a witness and a proof; with Σ-types
  (subtypes) the type-theoretic "axiom of choice" is a theorem needing no axiom at all, whereas
  its version with the proof-irrelevant `∃` uses `Classical.choice`.
* **Inductive types.** A home-made natural-number type and list type, their induction principles
  derived from the recursors Lean generates, and freeness (constructors are injective and
  disjoint) derived from the recursor too.
* **Curry–Howard as a theorem.** The simply typed λ-calculus (Church style, de Bruijn indices)
  and natural deduction for implication: `Γ ⊢ A` is derivable if and only if some term has type
  `A` in context `Γ`. `λx. x x` has no type. Kripke semantics is sound for natural deduction, a
  two-world Kripke model refutes Peirce's law, and therefore **no closed λ-term has the type
  `((p → q) → p) → p`**.

Not formalised here: strong normalisation of the simply typed λ-calculus (Tait's method), the
correspondence between normalisation of proofs and β-reduction, and the metatheory of Lean's own
type theory (see the lesson's references).
-/

namespace Lumenary.TypeTheory

/-! ### Part 1. Propositions as types in Lean itself -/

-- @region type_theory.k_combinator
-- @provenance independent
/-- **A proof is a program.** The proof of `A → (B → A)` is the function that takes a proof
`a` of `A`, ignores a proof of `B`, and returns `a`: the K combinator `λa. λb. a`. -/
theorem k_combinator (A B : Prop) : A → B → A :=
  fun a _ => a
-- @endregion

-- @region type_theory.s_combinator
-- @provenance independent
/-- The S combinator `λf. λg. λa. f a (g a)` proves `(A → B → C) → (A → B) → A → C`. -/
theorem s_combinator (A B C : Prop) : (A → B → C) → (A → B) → A → C :=
  fun f g a => f a (g a)
-- @endregion

-- @region type_theory.and_comm_term
-- @provenance independent
/-- Conjunction is a pair type: a proof of `A ∧ B` is a pair of proofs, and swapping the pair
proves `B ∧ A`. -/
theorem and_comm_term (A B : Prop) : A ∧ B → B ∧ A :=
  fun ⟨a, b⟩ => ⟨b, a⟩
-- @endregion

-- @region type_theory.or_elim_term
-- @provenance independent
/-- Disjunction is a tagged union: a proof of `A ∨ B` is a proof of `A` or a proof of `B`,
labelled with which, and using it is a case analysis. -/
theorem or_elim_term (A B C : Prop) : A ∨ B → (A → C) → (B → C) → C :=
  fun h f g =>
    match h with
    | Or.inl a => f a
    | Or.inr b => g b
-- @endregion

-- @region type_theory.not_not_em
-- @provenance independent
/-- `¬¬(A ∨ ¬A)` has a **constructive** proof (no axioms): given `h : ¬(A ∨ ¬A)`, the function
`fun a => h (Or.inl a)` is a proof of `¬A`, and feeding `Or.inr` of it to `h` gives `False`. -/
theorem not_not_em (A : Prop) : ¬¬(A ∨ ¬A) :=
  fun h => h (Or.inr fun a => h (Or.inl a))
-- @endregion

-- @region type_theory.peirce_classical
-- @provenance independent
/-- **Peirce's law** `((A → B) → A) → A` is provable in Lean — but only by using the axiom of
excluded middle `Classical.em` (Lean derives it from `Classical.choice`). Its axiom list shows
this, unlike the K and S combinators above. -/
theorem peirce_classical (A B : Prop) : ((A → B) → A) → A :=
  fun h => (Classical.em A).elim id fun na => h fun a => absurd a na
-- @endregion

/-! ### Π and Σ: quantifiers as types -/

-- @region type_theory.exists_larger
-- @provenance independent
/-- A proof of `∀ n, ∃ m, n < m` is a dependent function: for each `n` it returns a witness
`n + 1` packaged with a proof that `n < n + 1`. `∀` is a Π-type and `∃` a (propositional)
Σ-type. -/
theorem exists_larger : ∀ n : Nat, ∃ m, n < m :=
  fun n => ⟨n + 1, Nat.lt_succ_self n⟩
-- @endregion

-- @region type_theory.tt_choice
-- @provenance definition
/-- **The type-theoretic axiom of choice is a theorem.** If for every `x : A` we are *given*
some `y : B` with `R x y` (an element of the Σ-type `{y // R x y}`), then the first components
form a function `f` with `R x (f x)` for all `x`. No axiom is used: in type theory, a proof of
"for all x there is a y" built from Σ already contains the choice function. -/
def ttChoice {A B : Type} {R : A → B → Prop} (h : ∀ x : A, {y : B // R x y}) :
    {f : A → B // ∀ x, R x (f x)} :=
  ⟨fun x => (h x).1, fun x => (h x).2⟩
-- @endregion

-- @region type_theory.prop_choice
-- @provenance library
/-- With the **propositional** `∃`, which forgets its witness, the same statement needs an axiom:
this applies core Lean's `Classical.axiomOfChoice`, which is proved from the axiom
`Classical.choice`. -/
theorem prop_choice {A B : Type} {R : A → B → Prop} (h : ∀ x : A, ∃ y : B, R x y) :
    ∃ f : A → B, ∀ x, R x (f x) :=
  Classical.axiomOfChoice h
-- @endregion

/-! ### Inductive types -/

-- @region type_theory.nat_type
-- @provenance definition
/-- The natural numbers as an **inductive type**: freely generated by `zero` and `succ`. Lean
generates the recursor `N.rec` from this declaration. -/
inductive N where
  | zero : N
  | succ : N → N
-- @endregion

-- @region type_theory.nat_induction
-- @provenance independent
/-- **Induction is the recursor.** To prove `P n` for all `n : N`, prove `P zero` and
`P n → P (succ n)`; the proof term is the recursor `N.rec` applied to the two cases, with the
predicate `P` as its motive. -/
theorem N.induction (P : N → Prop) (h0 : P N.zero) (hs : ∀ n, P n → P (N.succ n)) :
    ∀ n, P n :=
  fun n => N.rec (motive := P) h0 hs n
-- @endregion

-- @region type_theory.nat_add
-- @provenance definition
/-- Addition by **recursion** on the second argument: `m + 0 = m`, `m + succ n = succ (m + n)`. -/
def N.add : N → N → N
  | m, N.zero => m
  | m, N.succ n => N.succ (N.add m n)
-- @endregion

-- @region type_theory.nat_zero_add
-- @provenance independent
/-- `0 + n = n` is **not** true by computation (addition recurses on the *second* argument), so
it needs induction: `0 + 0 = 0` by definition, and `0 + succ n = succ (0 + n) = succ n`. -/
theorem N.zero_add (n : N) : N.add N.zero n = n :=
  N.induction (fun n => N.add N.zero n = n) rfl (fun _ ih => congrArg N.succ ih) n
-- @endregion

-- @region type_theory.nat_succ_ne_zero
-- @provenance independent
/-- **Constructors are disjoint**, derived from the recursor: the function `isZero` (defined
by recursion into `Prop`) sends `zero` to `True` and every `succ n` to `False`, so
`succ n = zero` would turn `True` into `False`. -/
theorem N.succ_ne_zero (n : N) : N.succ n ≠ N.zero := by
  intro h
  let isZero : N → Prop := fun m => N.rec (motive := fun _ => Prop) True (fun _ _ => False) m
  have hz : isZero N.zero := trivial
  rw [← h] at hz
  exact hz
-- @endregion

-- @region type_theory.nat_succ_injective
-- @provenance independent
/-- **Constructors are injective**, also from the recursor: the predecessor function (defined
by pattern matching, which compiles to the recursor) recovers `n` from `succ n`. -/
theorem N.succ_injective {m n : N} (h : N.succ m = N.succ n) : m = n :=
  congrArg (fun k => match k with
    | N.zero => N.zero
    | N.succ k => k) h
-- @endregion

-- @region type_theory.list_type
-- @provenance definition
/-- Lists over `α` as an inductive type, freely generated by `nil` and `cons`. -/
inductive Lst (α : Type) where
  | nil : Lst α
  | cons : α → Lst α → Lst α
-- @endregion

-- @region type_theory.list_induction
-- @provenance independent
/-- The induction principle for lists, again the recursor: prove `P nil`, and `P l → P (a :: l)`
for every `a`. -/
theorem Lst.induction {α : Type} (P : Lst α → Prop) (hnil : P Lst.nil)
    (hcons : ∀ a l, P l → P (Lst.cons a l)) : ∀ l, P l :=
  fun l => Lst.rec (motive := P) hnil hcons l
-- @endregion

-- @region type_theory.list_append
-- @provenance definition
/-- Concatenation, by recursion on the first list. -/
def Lst.append {α : Type} : Lst α → Lst α → Lst α
  | Lst.nil, l => l
  | Lst.cons a l₁, l₂ => Lst.cons a (Lst.append l₁ l₂)
-- @endregion

-- @region type_theory.list_length
-- @provenance definition
/-- Length, by recursion. -/
def Lst.length {α : Type} : Lst α → Nat
  | Lst.nil => 0
  | Lst.cons _ l => Lst.length l + 1
-- @endregion

-- @region type_theory.list_length_append
-- @provenance independent
/-- `length (l₁ ++ l₂) = length l₁ + length l₂`, by list induction on `l₁`. -/
theorem Lst.length_append {α : Type} (l₁ l₂ : Lst α) :
    (Lst.append l₁ l₂).length = l₁.length + l₂.length := by
  induction l₁ using Lst.induction with
  | hnil => simp [Lst.append, Lst.length]
  | hcons a l ih =>
    simp only [Lst.append, Lst.length, ih]
    omega
-- @endregion

/-! ### Part 2. The simply typed λ-calculus and natural deduction -/

-- @region type_theory.ty
-- @provenance definition
/-- Simple types, which double as formulas of implicational logic: base types `p₀, p₁, …`
(atomic propositions) and function types `A ⇒ B` (implications). -/
inductive Ty where
  /-- The base type (atomic proposition) number `n`. -/
  | base : Nat → Ty
  /-- The function type `A ⇒ B` (the implication "A implies B"). -/
  | arrow : Ty → Ty → Ty
  deriving DecidableEq
-- @endregion

@[inherit_doc] local infixr:25 " ⇒ " => Ty.arrow

-- @region type_theory.tm
-- @provenance definition
/-- Terms of the simply typed λ-calculus, Church style: a λ records the type of its variable.
Variables are de Bruijn indices: `var 0` is the variable bound by the nearest `lam`. -/
inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Ty → Tm → Tm
-- @endregion

-- @region type_theory.has_type
-- @provenance definition
/-- The **typing judgement** `Γ ⊢ t : A`, where the context `Γ` lists the types of the free
variables (index `0` first). The three rules: a variable has its declared type; if `s : A ⇒ B`
and `t : A` then `s t : B`; if `t : B` assuming `x : A`, then `λ(x : A). t : A ⇒ B`. -/
inductive HasType : List Ty → Tm → Ty → Prop where
  | var {Γ : List Ty} {n : Nat} {A : Ty} : Γ[n]? = some A → HasType Γ (Tm.var n) A
  | app {Γ : List Ty} {s t : Tm} {A B : Ty} :
      HasType Γ s (A ⇒ B) → HasType Γ t A → HasType Γ (Tm.app s t) B
  | lam {Γ : List Ty} {t : Tm} {A B : Ty} :
      HasType (A :: Γ) t B → HasType Γ (Tm.lam A t) (A ⇒ B)
-- @endregion

-- @region type_theory.derivable
-- @provenance definition
/-- **Natural deduction** for implication, `Γ ⊢ A`: use a hypothesis; →-introduction (discharge
a hypothesis `A` to prove `A ⇒ B`); →-elimination (modus ponens). -/
inductive Derivable : List Ty → Ty → Prop where
  | hyp {Γ : List Ty} {A : Ty} : A ∈ Γ → Derivable Γ A
  | impI {Γ : List Ty} {A B : Ty} : Derivable (A :: Γ) B → Derivable Γ (A ⇒ B)
  | impE {Γ : List Ty} {A B : Ty} : Derivable Γ (A ⇒ B) → Derivable Γ A → Derivable Γ B
-- @endregion

-- @region type_theory.s_typed
-- @provenance independent
/-- The S combinator as a typed term: `⊢ λf. λg. λx. f x (g x) : (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C`.
With de Bruijn indices `x = 0`, `g = 1`, `f = 2`. The typing derivation is built rule by rule. -/
theorem s_typed (A B C : Ty) :
    HasType [] (Tm.lam (A ⇒ B ⇒ C) (Tm.lam (A ⇒ B) (Tm.lam A
      (Tm.app (Tm.app (Tm.var 2) (Tm.var 0)) (Tm.app (Tm.var 1) (Tm.var 0))))))
      ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) :=
  HasType.lam (HasType.lam (HasType.lam
    (HasType.app (HasType.app (HasType.var rfl) (HasType.var rfl))
      (HasType.app (HasType.var rfl) (HasType.var rfl)))))
-- @endregion

-- @region type_theory.curry_howard_forget
-- @provenance independent
/-- **Curry–Howard, from terms to proofs**: erasing the term from a typing derivation leaves a
natural-deduction derivation. Variables become hypotheses, application becomes modus ponens and
λ becomes →-introduction. -/
theorem HasType.derivable {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Γ t A) :
    Derivable Γ A := by
  induction h with
  | var hn => exact Derivable.hyp (List.mem_of_getElem? hn)
  | app _ _ ihs iht => exact Derivable.impE ihs iht
  | lam _ ih => exact Derivable.impI ih
-- @endregion

-- @region type_theory.curry_howard_realise
-- @provenance independent
/-- **Curry–Howard, from proofs to terms**: every natural-deduction derivation is the shadow of
a typed term. A hypothesis `A ∈ Γ` is some position `n` of `Γ`, giving the variable `var n`. -/
theorem Derivable.exists_term {Γ : List Ty} {A : Ty} (h : Derivable Γ A) :
    ∃ t, HasType Γ t A := by
  induction h with
  | @hyp Γ A hA =>
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hA
    exact ⟨Tm.var n, HasType.var hn⟩
  | @impI Γ A B _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨Tm.lam A t, HasType.lam ht⟩
  | impE _ _ ih₁ ih₂ =>
    obtain ⟨s, hs⟩ := ih₁
    obtain ⟨t, ht⟩ := ih₂
    exact ⟨Tm.app s t, HasType.app hs ht⟩
-- @endregion

-- @region type_theory.curry_howard
-- @provenance independent
/-- **The Curry–Howard correspondence** (implicational fragment): a formula is provable from
hypotheses `Γ` exactly when the corresponding type is inhabited in context `Γ`. -/
theorem curry_howard (Γ : List Ty) (A : Ty) : Derivable Γ A ↔ ∃ t, HasType Γ t A :=
  ⟨Derivable.exists_term, fun ⟨_, ht⟩ => ht.derivable⟩
-- @endregion

-- @region type_theory.ne_arrow_self
-- @provenance independent
/-- No type is a function type out of itself: `A ≠ A ⇒ B`. (Compare sizes, by induction on `A`.) -/
theorem ne_arrow_self : ∀ (A B : Ty), A ≠ (A ⇒ B)
  | Ty.base _, _, h => Ty.noConfusion h
  | Ty.arrow A₁ A₂, _, h => by
    injection h with h₁ _
    exact ne_arrow_self A₁ A₂ h₁
-- @endregion

-- @region type_theory.self_application_untypable
-- @provenance independent
/-- **`λx. x x` has no simple type**, whatever type is declared for `x`: typing `x x` would need
`x : A ⇒ B` and `x : A` at once, so `A = A ⇒ B`, which `ne_arrow_self` forbids. So the
self-application behind `Ω` and the fixed-point combinators is ruled out by types. -/
theorem self_application_untypable (Γ : List Ty) (A T : Ty) :
    ¬ HasType Γ (Tm.lam A (Tm.app (Tm.var 0) (Tm.var 0))) T := by
  intro h
  cases h with
  | lam hbody =>
    cases hbody with
    | app h₁ h₂ =>
      cases h₁ with
      | var e₁ =>
        cases h₂ with
        | var e₂ =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e₁ e₂
          subst e₂
          exact ne_arrow_self _ _ e₁
-- @endregion

/-! ### Kripke models: showing that a type is empty -/

-- @region type_theory.kripke_model
-- @provenance definition
/-- A **Kripke model** for intuitionistic implicational logic: a preordered set of "states of
knowledge" and, for each state, the atomic propositions known there — knowledge only grows
along the order (`mono`). -/
structure KripkeModel where
  World : Type
  le : World → World → Prop
  refl : ∀ w, le w w
  trans : ∀ u v w, le u v → le v w → le u w
  val : World → Nat → Prop
  mono : ∀ u v n, le u v → val u n → val v n
-- @endregion

-- @region type_theory.forces
-- @provenance definition
/-- **Forcing**: `w ⊩ A ⇒ B` means that at every later state where `A` holds, `B` holds too. -/
def KripkeModel.Forces (M : KripkeModel) : M.World → Ty → Prop
  | w, Ty.base n => M.val w n
  | w, Ty.arrow A B => ∀ v, M.le w v → M.Forces v A → M.Forces v B
-- @endregion

-- @region type_theory.forces_mono
-- @provenance independent
/-- **Persistence**: what is forced stays forced at later states. By induction on the formula;
the implication case uses transitivity of the order. -/
theorem forces_mono (M : KripkeModel) : ∀ (A : Ty) {u v : M.World}, M.le u v →
    M.Forces u A → M.Forces v A
  | Ty.base n, u, v, huv, h => M.mono u v n huv h
  | Ty.arrow _ _, u, v, huv, h => fun w hvw hA => h w (M.trans u v w huv hvw) hA
-- @endregion

-- @region type_theory.kripke_sound
-- @provenance independent
/-- **Soundness of natural deduction for Kripke models**: if `Γ ⊢ A` and every formula of `Γ`
is forced at `w`, then `A` is forced at `w`. →-introduction uses persistence of the hypotheses;
→-elimination uses reflexivity. -/
theorem Derivable.sound {Γ : List Ty} {A : Ty} (h : Derivable Γ A) (M : KripkeModel) :
    ∀ w, (∀ B ∈ Γ, M.Forces w B) → M.Forces w A := by
  induction h with
  | hyp hA => exact fun w hΓ => hΓ _ hA
  | @impI Γ A B _ ih =>
    intro w hΓ v hwv hA
    apply ih v
    intro C hC
    cases List.mem_cons.1 hC with
    | inl hCA => exact hCA ▸ hA
    | inr hCΓ => exact forces_mono M C hwv (hΓ C hCΓ)
  | impE _ _ ih₁ ih₂ =>
    intro w hΓ
    exact ih₁ w hΓ w (M.refl w) (ih₂ w hΓ)
-- @endregion

-- @region type_theory.peirce_model
-- @provenance definition
/-- A **two-state Kripke model**: states `false ≤ true`; the atom `p₀` becomes known only at
the later state `true`, and `p₁` is never known. -/
def peirceModel : KripkeModel where
  World := Bool
  le u v := u = false ∨ v = true
  refl w := by cases w <;> simp
  trans u v w := by cases u <;> cases v <;> cases w <;> simp
  val w n := w = true ∧ n = 0
  mono u v n := by cases u <;> cases v <;> simp_all
-- @endregion

-- @region type_theory.peirce_not_derivable
-- @provenance independent
/-- **Peirce's law is not intuitionistically derivable**: `⊬ ((p ⇒ q) ⇒ p) ⇒ p`. At the first
state, `p ⇒ q` is not forced (later `p` becomes true but `q` never does), so `(p ⇒ q) ⇒ p`
holds vacuously there — yet `p` does not hold there. Soundness then rules out a derivation. -/
theorem peirce_not_derivable :
    ¬ Derivable [] (((Ty.base 0 ⇒ Ty.base 1) ⇒ Ty.base 0) ⇒ Ty.base 0) := by
  intro h
  have hf := h.sound peirceModel false (fun _ hB => absurd hB List.not_mem_nil)
  -- `(p ⇒ q) ⇒ p` is forced at `false`.
  have hpq : peirceModel.Forces false ((Ty.base 0 ⇒ Ty.base 1) ⇒ Ty.base 0) := by
    intro v _ hv
    cases v with
    | true => exact ⟨rfl, rfl⟩
    | false =>
      -- `p ⇒ q` fails at `false`: at `true`, `p` holds but `q` does not.
      have hq := hv true (Or.inl rfl) ⟨rfl, rfl⟩
      exact absurd hq.2 (by decide)
  have hp := hf false (Or.inl rfl) hpq
  exact absurd hp.1 (by decide)
-- @endregion

-- @region type_theory.peirce_uninhabited
-- @provenance independent
/-- **No closed λ-term has the type `((p ⇒ q) ⇒ p) ⇒ p`**: by Curry–Howard such a term would be a
derivation of Peirce's law. A classical tautology need not be an inhabited type. -/
theorem peirce_uninhabited :
    ¬ ∃ t, HasType [] t (((Ty.base 0 ⇒ Ty.base 1) ⇒ Ty.base 0) ⇒ Ty.base 0) :=
  fun ⟨_, ht⟩ => peirce_not_derivable ht.derivable
-- @endregion

end Lumenary.TypeTheory
