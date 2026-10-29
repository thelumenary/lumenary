/-
The Lumenary — formal mathematics
Categorical logic: the simply typed λ-calculus interpreted in a cartesian closed category,
quantifiers as adjoints, and Heyting algebras as models of intuitionistic logic.

What is proved here.
* **λ-calculus.** An intrinsically typed simply typed λ-calculus with unit, products and
  function types (`Ty`, `Var`, `Tm`), its interpretation in Lean's types and functions — the
  type-theoretic stand-in for the cartesian closed category **Set** — with a context denoting a
  product and a term denoting a map out of it, and the **soundness theorem**: βη-convertible
  terms have equal interpretations (`Conv.sound`). Corollary: no closed term has the base type.
* **Quantifiers as adjoints (Lawvere).** Image ⊣ preimage ⊣ "for all along `f`", proved from
  scratch and compared with Mathlib's `Set.image_preimage` and `Set.preimage_kernImage`; along a
  projection these are exactly `∃ y` and `∀ y`.
* **Heyting algebras.** `¬¬(a ∨ ¬a) = ⊤` in every Heyting algebra; intuitionistic propositional
  natural deduction (`Derives`) is **sound** for Heyting-algebra semantics; the open sets of ℝ
  form a Heyting algebra that is not Boolean; hence `p ∨ ¬p` is **not derivable**, while
  `¬¬(p ∨ ¬p)` is.

What is not proved here: the interpretation in an *arbitrary* cartesian closed category (we
use the single model **Set**/`Type`), the completeness theorems (term models, the
Lindenbaum–Tarski algebra), and Lambek's equivalence between λ-theories and cartesian closed
categories. Mathlib provides cartesian closed (`MonoidalClosed`) categories and the instance
for `Type u`, Heyting algebras, frames and the frame of open sets.
-/
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.CategoryTheory.Monoidal.Closed.Types

namespace Lumenary.CategoricalLogic

/-! ## 1. The simply typed λ-calculus with products -/

-- @region categorical_logic.ty
-- @provenance definition
/-- **Simple types**: one base type, the unit type, binary products and function types.
These are the objects of the "free cartesian closed category on one object". -/
inductive Ty where
  | base : Ty
  | unit : Ty
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq
-- @endregion

-- @region categorical_logic.var
-- @provenance definition
/-- **Variables** as typed de Bruijn indices. A context is a list of types (most recent
variable first); `Var Γ A` is a position in `Γ` holding the type `A`. -/
inductive Var : List Ty → Ty → Type where
  | zero {Γ : List Ty} {A : Ty} : Var (A :: Γ) A
  | succ {Γ : List Ty} {A B : Ty} : Var Γ A → Var (B :: Γ) A
-- @endregion

-- @region categorical_logic.tm
-- @provenance definition
/-- **Terms** of the simply typed λ-calculus with unit and products, typed *intrinsically*:
`Tm Γ A` contains exactly the well-typed terms of type `A` in context `Γ`. Read through
Curry–Howard, `Tm Γ A` is the set of natural-deduction proofs of `A` from hypotheses `Γ` in the
`⊤, ∧, →` fragment of intuitionistic logic. -/
inductive Tm : List Ty → Ty → Type where
  | var {Γ : List Ty} {A : Ty} : Var Γ A → Tm Γ A
  | star {Γ : List Ty} : Tm Γ .unit
  | pair {Γ : List Ty} {A B : Ty} : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst {Γ : List Ty} {A B : Ty} : Tm Γ (.prod A B) → Tm Γ A
  | snd {Γ : List Ty} {A B : Ty} : Tm Γ (.prod A B) → Tm Γ B
  | lam {Γ : List Ty} {A B : Ty} : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | app {Γ : List Ty} {A B : Ty} : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
-- @endregion

/-! ### Renaming and substitution -/

-- @region categorical_logic.ren_ext
-- @provenance definition
/-- Extend a renaming of variables under a binder: the new variable `zero` goes to `zero`. -/
def renExt {Γ Δ : List Ty} {B : Ty} (r : ∀ {A : Ty}, Var Γ A → Var Δ A) :
    ∀ {A : Ty}, Var (B :: Γ) A → Var (B :: Δ) A
  | _, .zero => .zero
  | _, .succ v => .succ (r v)
-- @endregion

-- @region categorical_logic.rename
-- @provenance definition
/-- Apply a renaming of variables to a term (used to weaken a term into a larger context). -/
def Tm.rename {Γ Δ : List Ty} (r : ∀ {A : Ty}, Var Γ A → Var Δ A) :
    ∀ {A : Ty}, Tm Γ A → Tm Δ A
  | _, .var v => .var (r v)
  | _, .star => .star
  | _, .pair s t => .pair (s.rename r) (t.rename r)
  | _, .fst t => .fst (t.rename r)
  | _, .snd t => .snd (t.rename r)
  | _, .lam t => .lam (t.rename (renExt r))
  | _, .app s t => .app (s.rename r) (t.rename r)
-- @endregion

-- @region categorical_logic.subst_ext
-- @provenance definition
/-- Extend a substitution under a binder: `zero` stays a variable, the other variables are
replaced as before and then weakened past the new binder. -/
def substExt {Γ Δ : List Ty} {B : Ty} (σ : ∀ {A : Ty}, Var Γ A → Tm Δ A) :
    ∀ {A : Ty}, Var (B :: Γ) A → Tm (B :: Δ) A
  | _, .zero => .var .zero
  | _, .succ v => (σ v).rename Var.succ
-- @endregion

-- @region categorical_logic.subst
-- @provenance definition
/-- Simultaneous, capture-avoiding substitution of terms for variables. -/
def Tm.subst {Γ Δ : List Ty} (σ : ∀ {A : Ty}, Var Γ A → Tm Δ A) :
    ∀ {A : Ty}, Tm Γ A → Tm Δ A
  | _, .var v => σ v
  | _, .star => .star
  | _, .pair s t => .pair (s.subst σ) (t.subst σ)
  | _, .fst t => .fst (t.subst σ)
  | _, .snd t => .snd (t.subst σ)
  | _, .lam t => .lam (t.subst (substExt σ))
  | _, .app s t => .app (s.subst σ) (t.subst σ)
-- @endregion

-- @region categorical_logic.single
-- @provenance definition
/-- The substitution `[u/x]` that replaces the most recent variable by `u` and renumbers the
others; `t.subst (single u)` is the result of a β-step `(λx. t) u ↦ t[u/x]`. -/
def single {Γ : List Ty} {B : Ty} (u : Tm Γ B) : ∀ {A : Ty}, Var (B :: Γ) A → Tm Γ A
  | _, .zero => u
  | _, .succ v => .var v
-- @endregion

/-! ### βη-conversion -/

-- @region categorical_logic.conv
-- @provenance definition
/-- **βη-conversion**: the equational theory of the simply typed λ-calculus with products.
It is the least congruence containing the β-rules (`fst ⟨s, t⟩ = s`, `snd ⟨s, t⟩ = t`,
`(λx. t) u = t[u/x]`) and the η-rules (`⟨fst p, snd p⟩ = p`, `t = ⋆` at unit type,
`λx. f x = f` with `x` not free in `f`). These are exactly the equations of a cartesian closed
category, read through the term ↔ morphism dictionary. -/
inductive Conv : {Γ : List Ty} → {A : Ty} → Tm Γ A → Tm Γ A → Prop where
  | refl {Γ : List Ty} {A : Ty} (t : Tm Γ A) : Conv t t
  | symm {Γ : List Ty} {A : Ty} {s t : Tm Γ A} : Conv s t → Conv t s
  | trans {Γ : List Ty} {A : Ty} {s t u : Tm Γ A} : Conv s t → Conv t u → Conv s u
  | pair {Γ : List Ty} {A B : Ty} {s s' : Tm Γ A} {t t' : Tm Γ B} :
      Conv s s' → Conv t t' → Conv (.pair s t) (.pair s' t')
  | fst {Γ : List Ty} {A B : Ty} {p p' : Tm Γ (.prod A B)} : Conv p p' → Conv (.fst p) (.fst p')
  | snd {Γ : List Ty} {A B : Ty} {p p' : Tm Γ (.prod A B)} : Conv p p' → Conv (.snd p) (.snd p')
  | lam {Γ : List Ty} {A B : Ty} {t t' : Tm (A :: Γ) B} : Conv t t' → Conv (.lam t) (.lam t')
  | app {Γ : List Ty} {A B : Ty} {s s' : Tm Γ (.arr A B)} {t t' : Tm Γ A} :
      Conv s s' → Conv t t' → Conv (.app s t) (.app s' t')
  | beta_fst {Γ : List Ty} {A B : Ty} (s : Tm Γ A) (t : Tm Γ B) : Conv (.fst (.pair s t)) s
  | beta_snd {Γ : List Ty} {A B : Ty} (s : Tm Γ A) (t : Tm Γ B) : Conv (.snd (.pair s t)) t
  | beta_arr {Γ : List Ty} {A B : Ty} (t : Tm (A :: Γ) B) (u : Tm Γ A) :
      Conv (.app (.lam t) u) (t.subst (single u))
  | eta_prod {Γ : List Ty} {A B : Ty} (p : Tm Γ (.prod A B)) : Conv (.pair (.fst p) (.snd p)) p
  | eta_unit {Γ : List Ty} (t : Tm Γ .unit) : Conv t .star
  | eta_arr {Γ : List Ty} {A B : Ty} (f : Tm Γ (.arr A B)) :
      Conv (.lam (.app (f.rename Var.succ) (.var .zero))) f
-- @endregion

/-! ### The interpretation in Set (Lean types) -/

-- @region categorical_logic.ty_denote
-- @provenance definition
/-- Interpret simple types as Lean types, given a type `X` for the base type: unit is the
terminal object `Unit`, `prod` is the cartesian product and `arr` is the function type — the
exponential object of **Set**. -/
def Ty.denote (X : Type) : Ty → Type
  | .base => X
  | .unit => Unit
  | .prod A B => A.denote X × B.denote X
  | .arr A B => A.denote X → B.denote X
-- @endregion

-- @region categorical_logic.ctx_denote
-- @provenance definition
/-- A context `[A₁, …, Aₙ]` is interpreted as the product `⟦A₁⟧ × (⋯ × (⟦Aₙ⟧ × 1))`. -/
def ctxDenote (X : Type) : List Ty → Type
  | [] => Unit
  | A :: Γ => A.denote X × ctxDenote X Γ
-- @endregion

-- @region categorical_logic.var_denote
-- @provenance definition
/-- A variable is interpreted as a **product projection** `⟦Γ⟧ → ⟦A⟧`. -/
def Var.denote {X : Type} : {Γ : List Ty} → {A : Ty} → Var Γ A → ctxDenote X Γ → A.denote X
  | _ :: _, _, .zero, γ => γ.1
  | _ :: _, _, .succ v, γ => v.denote γ.2
-- @endregion

-- @region categorical_logic.tm_denote
-- @provenance definition
/-- **The interpretation of terms as morphisms** `⟦Γ⟧ → ⟦A⟧` of the cartesian closed category
of types: pairing is the map into a product, `fst`/`snd` compose with projections, `lam` is
**currying** (the bijection `Hom(Γ × A, B) ≅ Hom(Γ, B^A)`), and `app` composes with
**evaluation** `B^A × A → B`. -/
def Tm.denote {X : Type} : {Γ : List Ty} → {A : Ty} → Tm Γ A → ctxDenote X Γ → A.denote X
  | _, _, .var v, γ => v.denote γ
  | _, _, .star, _ => ()
  | _, _, .pair s t, γ => (s.denote γ, t.denote γ)
  | _, _, .fst t, γ => (t.denote γ).1
  | _, _, .snd t, γ => (t.denote γ).2
  | _, _, .lam t, γ => fun a => t.denote (a, γ)
  | _, _, .app s t, γ => s.denote γ (t.denote γ)
-- @endregion

/-! ### Soundness -/

-- @region categorical_logic.denote_rename
-- @provenance independent
/-- **Renaming lemma.** If a renaming `r` sends each variable to one with the same value
(under environments `δ` and `γ`), then renaming does not change the value of any term.
Proved by induction on the term; the `lam` case extends both environments by the same value. -/
theorem denote_rename {X : Type} {Γ Δ : List Ty} {A : Ty} (t : Tm Γ A)
    (r : ∀ {B : Ty}, Var Γ B → Var Δ B) (δ : ctxDenote X Δ) (γ : ctxDenote X Γ)
    (h : ∀ {B : Ty} (v : Var Γ B), (r v).denote δ = v.denote γ) :
    (t.rename r).denote δ = t.denote γ := by
  induction t generalizing Δ with
  | var v => exact h v
  | star => rfl
  | pair s t ihs iht => exact congrArg₂ Prod.mk (ihs r δ γ h) (iht r δ γ h)
  | fst t ih => simp only [Tm.rename, Tm.denote, ih r δ γ h]
  | snd t ih => simp only [Tm.rename, Tm.denote, ih r δ γ h]
  | lam t ih =>
    funext a
    apply ih (renExt r) (a, δ) (a, γ)
    intro B v
    cases v with
    | zero => rfl
    | succ v => exact h v
  | app s t ihs iht => simp only [Tm.rename, Tm.denote, ihs r δ γ h, iht r δ γ h]
-- @endregion

-- @region categorical_logic.denote_subst
-- @provenance independent
/-- **Substitution lemma** — the semantic heart of Curry–Howard–Lambek: substituting terms for
variables is interpreted by *composition* with the tuple of their interpretations. Precisely,
if every `σ v` denotes (at `δ`) the value of `v` (at `γ`), then `t.subst σ` denotes (at `δ`) the
value of `t` (at `γ`). The `lam` case needs the renaming lemma for the weakening in
`substExt`. -/
theorem denote_subst {X : Type} {Γ Δ : List Ty} {A : Ty} (t : Tm Γ A)
    (σ : ∀ {B : Ty}, Var Γ B → Tm Δ B) (δ : ctxDenote X Δ) (γ : ctxDenote X Γ)
    (h : ∀ {B : Ty} (v : Var Γ B), (σ v).denote δ = v.denote γ) :
    (t.subst σ).denote δ = t.denote γ := by
  induction t generalizing Δ with
  | var v => exact h v
  | star => rfl
  | pair s t ihs iht => exact congrArg₂ Prod.mk (ihs σ δ γ h) (iht σ δ γ h)
  | fst t ih => simp only [Tm.subst, Tm.denote, ih σ δ γ h]
  | snd t ih => simp only [Tm.subst, Tm.denote, ih σ δ γ h]
  | lam t ih =>
    funext a
    apply ih (substExt σ) (a, δ) (a, γ)
    intro B v
    cases v with
    | zero => rfl
    | succ v =>
      show ((σ v).rename Var.succ).denote (a, δ) = v.denote γ
      rw [denote_rename (σ v) Var.succ (a, δ) δ (fun _ => rfl)]
      exact h v
  | app s t ihs iht => simp only [Tm.subst, Tm.denote, ihs σ δ γ h, iht σ δ γ h]
-- @endregion

-- @region categorical_logic.beta_sound
-- @provenance independent
/-- **β is sound**: `(λx. t) u` and `t[u/x]` have the same interpretation. In categorical
terms: evaluating a curried map is the same as substituting, `ev ∘ ⟨Λt, u⟩ = t ∘ ⟨u, id⟩`. -/
theorem beta_sound {X : Type} {Γ : List Ty} {A B : Ty} (t : Tm (A :: Γ) B) (u : Tm Γ A)
    (γ : ctxDenote X Γ) :
    (Tm.app (.lam t) u).denote γ = (t.subst (single u)).denote γ := by
  symm
  apply denote_subst t (single u) γ (u.denote γ, γ)
  intro B v
  cases v with
  | zero => rfl
  | succ v => rfl
-- @endregion

-- @region categorical_logic.conv_sound
-- @provenance independent
/-- **Soundness of the interpretation** (Lambek): βη-convertible terms denote the *same*
morphism `⟦Γ⟧ → ⟦A⟧`, for every interpretation `X` of the base type. Proved by induction on
the derivation of convertibility; the congruence rules use function extensionality, β for
functions is `beta_sound`, and η for functions is the renaming lemma. -/
theorem Conv.sound {X : Type} {Γ : List Ty} {A : Ty} {s t : Tm Γ A} (h : Conv s t) :
    (s.denote : ctxDenote X Γ → A.denote X) = t.denote := by
  induction h with
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | pair _ _ ih₁ ih₂ => funext γ; exact congrArg₂ Prod.mk (congrFun ih₁ γ) (congrFun ih₂ γ)
  | fst _ ih => funext γ; simp only [Tm.denote, ih]
  | snd _ ih => funext γ; simp only [Tm.denote, ih]
  | lam _ ih => funext γ a; exact congrFun ih (a, γ)
  | app _ _ ih₁ ih₂ => funext γ; simp only [Tm.denote, ih₁, ih₂]
  | beta_fst s t => rfl
  | beta_snd s t => rfl
  | beta_arr t u => funext γ; exact beta_sound t u γ
  | eta_prod p => rfl
  | eta_unit t => rfl
  | eta_arr f =>
    funext γ a
    show (f.rename Var.succ).denote (a, γ) a = f.denote γ a
    rw [denote_rename f Var.succ (a, γ) γ (fun _ => rfl)]
-- @endregion

-- @region categorical_logic.no_closed_term_of_base
-- @provenance independent
/-- **Consistency from a model.** There is no closed term of the base type: interpret the base
type as the empty type, and a closed term would denote an element of it. Through Curry–Howard:
an atomic proposition is not provable from no hypotheses. -/
theorem no_closed_term_of_base (t : Tm [] .base) : False :=
  (t.denote (X := Empty) ()).elim
-- @endregion

-- @region categorical_logic.curry_term
-- @provenance definition
/-- The closed term `λf. λa. λb. f ⟨a, b⟩` of type `(A × B → C) → (A → B → C)` — a proof of
`(A ∧ B → C) → (A → (B → C))` under Curry–Howard. -/
def curryTm (A B C : Ty) : Tm [] (.arr (.arr (.prod A B) C) (.arr A (.arr B C))) :=
  .lam (.lam (.lam (.app (.var (.succ (.succ .zero))) (.pair (.var (.succ .zero)) (.var .zero)))))
-- @endregion

-- @region categorical_logic.curry_term_denote
-- @provenance independent
/-- The interpretation of `curryTm` in **Set** is currying itself, `Function.curry`
(by computation: both sides reduce to `fun f a b => f (a, b)`). -/
theorem curryTm_denote (X : Type) (A B C : Ty) :
    (curryTm A B C).denote (X := X) () = Function.curry := rfl
-- @endregion

-- @region categorical_logic.types_closed
-- @provenance library
/-- Mathlib knows that the category of types is **cartesian closed**: `Type u`, with its
cartesian monoidal structure, carries a `MonoidalClosed` instance (the internal hom is the
function type and `− × B ⊣ (B → −)` is currying). This is Mathlib's instance from
`Mathlib.CategoryTheory.Monoidal.Closed.Types`. -/
theorem types_cartesianClosed : Nonempty (CategoryTheory.MonoidalClosed (Type)) :=
  ⟨inferInstance⟩
-- @endregion

/-! ## 2. Quantifiers as adjoints -/

-- @region categorical_logic.forall_along
-- @provenance definition
/-- **Universal quantification along `f : X → Y`**: `y` belongs to `∀_f S` when *every* `x`
over `y` lies in `S`. (Mathlib calls this `Set.kernImage f S`.) -/
def forallAlong {X Y : Type} (f : X → Y) (S : Set X) : Set Y :=
  {y | ∀ x, f x = y → x ∈ S}
-- @endregion

-- @region categorical_logic.exists_adjoint
-- @provenance independent
/-- **∃ is left adjoint to substitution** (Lawvere): for predicates `S` on `X` and `T` on `Y`,
`∃_f S ⊆ T ↔ S ⊆ f*T`, where `∃_f S = f '' S` is the direct image and `f*T = f ⁻¹' T` is
pulling back (substitution). -/
theorem exists_adjoint {X Y : Type} (f : X → Y) (S : Set X) (T : Set Y) :
    f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h hx
-- @endregion

-- @region categorical_logic.forall_adjoint
-- @provenance independent
/-- **∀ is right adjoint to substitution** (Lawvere): `f*T ⊆ S ↔ T ⊆ ∀_f S`. -/
theorem forall_adjoint {X Y : Type} (f : X → Y) (S : Set X) (T : Set Y) :
    f ⁻¹' T ⊆ S ↔ T ⊆ forallAlong f S := by
  constructor
  · intro h y hy x hxy
    apply h
    show f x ∈ T
    rw [hxy]
    exact hy
  · intro h x hx
    exact h hx x rfl
-- @endregion

-- @region categorical_logic.exists_along_fst
-- @provenance independent
/-- Along the projection `π : X × Y → X`, the left adjoint is the **existential quantifier**:
`∃_π S = {x | ∃ y, (x, y) ∈ S}`. -/
theorem exists_along_fst {X Y : Type} (S : Set (X × Y)) :
    Prod.fst '' S = {x | ∃ y, (x, y) ∈ S} := by
  ext x
  constructor
  · rintro ⟨⟨x', y⟩, h, rfl⟩
    exact ⟨y, h⟩
  · rintro ⟨y, h⟩
    exact ⟨(x, y), h, rfl⟩
-- @endregion

-- @region categorical_logic.forall_along_fst
-- @provenance independent
/-- Along the projection `π : X × Y → X`, the right adjoint is the **universal quantifier**:
`∀_π S = {x | ∀ y, (x, y) ∈ S}`. -/
theorem forall_along_fst {X Y : Type} (S : Set (X × Y)) :
    forallAlong Prod.fst S = {x | ∀ y, (x, y) ∈ S} := by
  ext x
  constructor
  · intro h y
    exact h (x, y) rfl
  · rintro h ⟨x', y⟩ rfl
    exact h y
-- @endregion

-- @region categorical_logic.quantifier_adjunctions_library
-- @provenance library
/-- The same two adjunctions, as Mathlib states them: Galois connections
`image f ⊣ preimage f` (`Set.image_preimage`) and `preimage f ⊣ kernImage f`
(`Set.preimage_kernImage`). A Galois connection is an adjunction between posets viewed as
categories. -/
theorem quantifier_adjunctions_library {X Y : Type} (f : X → Y) :
    GaloisConnection (Set.image f) (Set.preimage f) ∧
      GaloisConnection (Set.preimage f) (Set.kernImage f) :=
  ⟨Set.image_preimage, Set.preimage_kernImage⟩
-- @endregion

-- @region categorical_logic.frobenius
-- @provenance independent
/-- **Frobenius reciprocity**: `∃_f (S ∧ f*T) = ∃_f S ∧ T`. In logic: `∃x (φ(x) ∧ ψ(f x))` is
equivalent to `(∃x φ(x)) ∧ ψ` when `ψ` only depends on `y = f x`. It is one of the two
conditions (with Beck–Chevalley) that make `∃` behave well in a hyperdoctrine. -/
theorem frobenius {X Y : Type} (f : X → Y) (S : Set X) (T : Set Y) :
    f '' (S ∩ f ⁻¹' T) = f '' S ∩ T := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩
    exact ⟨⟨x, hxS, rfl⟩, hxT⟩
  · rintro ⟨⟨x, hxS, rfl⟩, hyT⟩
    exact ⟨x, ⟨hxS, hyT⟩, rfl⟩
-- @endregion

/-! ## 3. Heyting algebras and intuitionistic logic -/

-- @region categorical_logic.not_not_em_heyting
-- @provenance independent
/-- **`¬¬(a ∨ ¬a) = ⊤` in every Heyting algebra.** Write `n = ¬(a ∨ ¬a)`. Since `a ≤ a ∨ ¬a`,
`n ∧ a ≤ ⊥`, so `n ≤ ¬a ≤ a ∨ ¬a`; hence `n ≤ n ∧ (a ∨ ¬a) ≤ ⊥`, i.e. `n = ⊥` and `¬n = ⊤`.
Only the defining law `c ≤ (a ⇨ b) ↔ c ∧ a ≤ b` is used. -/
theorem not_not_em_heyting {α : Type*} [HeytingAlgebra α] (a : α) : (a ⊔ aᶜ)ᶜᶜ = ⊤ := by
  -- `x ∧ ¬x ≤ ⊥`, from the residuation law with `c = ¬x`.
  have contra : ∀ x : α, xᶜ ⊓ x ≤ ⊥ := fun x => by
    rw [← le_himp_iff, himp_bot]
  have hn_le_compl : (a ⊔ aᶜ)ᶜ ≤ aᶜ := by
    have h : (a ⊔ aᶜ)ᶜ ≤ a ⇨ ⊥ := by
      rw [le_himp_iff]
      exact le_trans (inf_le_inf_left _ le_sup_left) (contra (a ⊔ aᶜ))
    rwa [himp_bot] at h
  have hn_bot : (a ⊔ aᶜ)ᶜ ≤ ⊥ :=
    calc (a ⊔ aᶜ)ᶜ ≤ (a ⊔ aᶜ)ᶜ ⊓ (a ⊔ aᶜ) := le_inf le_rfl (hn_le_compl.trans le_sup_right)
      _ ≤ ⊥ := contra (a ⊔ aᶜ)
  have h : ⊤ ≤ (a ⊔ aᶜ)ᶜ ⇨ ⊥ := by
    rw [le_himp_iff]
    exact le_trans inf_le_right hn_bot
  rw [himp_bot] at h
  exact top_le_iff.mp h
-- @endregion

-- @region categorical_logic.le_compl_compl_heyting
-- @provenance independent
/-- `a ≤ ¬¬a` in every Heyting algebra: by residuation it says `a ∧ ¬a ≤ ⊥`. (The converse
`¬¬a ≤ a` holds exactly in Boolean algebras.) -/
theorem le_compl_compl_heyting {α : Type*} [HeytingAlgebra α] (a : α) : a ≤ aᶜᶜ := by
  have h : a ≤ aᶜ ⇨ ⊥ := by
    rw [le_himp_iff]
    have hc : aᶜ ⊓ a ≤ ⊥ := by rw [← le_himp_iff, himp_bot]
    rwa [inf_comm] at hc
  rwa [himp_bot] at h
-- @endregion

-- @region categorical_logic.not_not_em
-- @provenance independent
/-- The same law in Lean's own logic: `¬¬(P ∨ ¬P)`, proved **without** the law of excluded
middle (`#print axioms` reports no axioms). Given `h : ¬(P ∨ ¬P)`, the function
`fun p => h (Or.inl p)` proves `¬P`, and then `h (Or.inr …)` is a contradiction. -/
theorem not_not_em (P : Prop) : ¬¬(P ∨ ¬P) :=
  fun h => h (Or.inr fun p => h (Or.inl p))
-- @endregion

-- @region categorical_logic.opens_real_not_boolean
-- @provenance independent
/-- **The open sets of ℝ form a Heyting algebra that is not Boolean.** (`Opens ℝ` is a frame,
hence a Heyting algebra, in Mathlib.) For `U = (0, ∞)`, the pseudo-complement `¬U` is the
largest open set disjoint from `U`, and `U ∨ ¬U ≠ ℝ`: otherwise `U` would be open and closed,
hence `∅` or `ℝ`, because ℝ is connected (Mathlib's `isClopen_iff`). -/
theorem opens_real_not_boolean :
    ∃ U : TopologicalSpace.Opens ℝ, U ⊔ Uᶜ ≠ ⊤ := by
  refine ⟨⟨Set.Ioi 0, isOpen_Ioi⟩, fun h => ?_⟩
  set U : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩ with hU
  have hdisj : U ⊓ Uᶜ = ⊥ := inf_compl_self U
  have hunion : (U : Set ℝ) ∪ (Uᶜ : TopologicalSpace.Opens ℝ) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_sup, h, TopologicalSpace.Opens.coe_top]
  have hinter : (U : Set ℝ) ∩ (Uᶜ : TopologicalSpace.Opens ℝ) = ∅ := by
    rw [← TopologicalSpace.Opens.coe_inf, hdisj, TopologicalSpace.Opens.coe_bot]
  -- So the complement of `U` (as a set) is the open set `¬U`; hence `U` is clopen.
  have hcompl : (U : Set ℝ)ᶜ = (Uᶜ : TopologicalSpace.Opens ℝ) := by
    ext x
    constructor
    · intro hx
      have : x ∈ (U : Set ℝ) ∪ (Uᶜ : TopologicalSpace.Opens ℝ) := by rw [hunion]; trivial
      rcases this with h1 | h2
      · exact absurd h1 hx
      · exact h2
    · intro hx hxU
      have : x ∈ (U : Set ℝ) ∩ (Uᶜ : TopologicalSpace.Opens ℝ) := ⟨hxU, hx⟩
      rw [hinter] at this
      exact this
  have hclopen : IsClopen (U : Set ℝ) := by
    refine ⟨?_, U.isOpen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (Uᶜ : TopologicalSpace.Opens ℝ).isOpen
  rcases isClopen_iff.mp hclopen with h0 | h1
  · have : (1 : ℝ) ∈ (U : Set ℝ) := by
      show (1 : ℝ) ∈ Set.Ioi 0
      norm_num
    rw [h0] at this
    exact this
  · have : (-1 : ℝ) ∈ (U : Set ℝ) := by rw [h1]; trivial
    have : (0 : ℝ) < -1 := this
    norm_num at this
-- @endregion

/-! ### Intuitionistic propositional logic and its Heyting-algebra semantics -/

-- @region categorical_logic.form
-- @provenance definition
/-- **Propositional formulas** over atoms indexed by `ℕ`. Negation is defined: `¬φ := φ → ⊥`. -/
inductive Form where
  | atom : ℕ → Form
  | top : Form
  | bot : Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
-- @endregion

-- @region categorical_logic.form_neg
-- @provenance definition
/-- Intuitionistic negation `¬φ := φ → ⊥`. -/
def Form.neg (φ : Form) : Form := .imp φ .bot
-- @endregion

-- @region categorical_logic.derives
-- @provenance definition
/-- **Natural deduction for intuitionistic propositional logic** (IPC): `Derives Γ φ` means
`φ` is derivable from the list of hypotheses `Γ`. There is an introduction and an elimination
rule for each connective, and *no* rule for excluded middle or double-negation elimination. -/
inductive Derives : List Form → Form → Prop where
  | hyp {Γ : List Form} {φ : Form} : φ ∈ Γ → Derives Γ φ
  | topI {Γ : List Form} : Derives Γ .top
  | botE {Γ : List Form} {φ : Form} : Derives Γ .bot → Derives Γ φ
  | andI {Γ : List Form} {φ ψ : Form} : Derives Γ φ → Derives Γ ψ → Derives Γ (.and φ ψ)
  | andE₁ {Γ : List Form} {φ ψ : Form} : Derives Γ (.and φ ψ) → Derives Γ φ
  | andE₂ {Γ : List Form} {φ ψ : Form} : Derives Γ (.and φ ψ) → Derives Γ ψ
  | orI₁ {Γ : List Form} {φ ψ : Form} : Derives Γ φ → Derives Γ (.or φ ψ)
  | orI₂ {Γ : List Form} {φ ψ : Form} : Derives Γ ψ → Derives Γ (.or φ ψ)
  | orE {Γ : List Form} {φ ψ χ : Form} :
      Derives Γ (.or φ ψ) → Derives (φ :: Γ) χ → Derives (ψ :: Γ) χ → Derives Γ χ
  | impI {Γ : List Form} {φ ψ : Form} : Derives (φ :: Γ) ψ → Derives Γ (.imp φ ψ)
  | impE {Γ : List Form} {φ ψ : Form} : Derives Γ (.imp φ ψ) → Derives Γ φ → Derives Γ ψ
-- @endregion

-- @region categorical_logic.form_eval
-- @provenance definition
/-- **Heyting-algebra semantics**: given values `v n` for the atoms in a Heyting algebra `α`,
`∧, ∨, →, ⊤, ⊥` are interpreted by meet, join, Heyting implication, top and bottom. -/
def Form.eval {α : Type*} [HeytingAlgebra α] (v : ℕ → α) : Form → α
  | .atom n => v n
  | .top => ⊤
  | .bot => ⊥
  | .and φ ψ => φ.eval v ⊓ ψ.eval v
  | .or φ ψ => φ.eval v ⊔ ψ.eval v
  | .imp φ ψ => φ.eval v ⇨ ψ.eval v
-- @endregion

-- @region categorical_logic.ctx_eval
-- @provenance definition
/-- A list of hypotheses is interpreted as the meet of their values (`⊤` for no hypotheses). -/
def ctxEval {α : Type*} [HeytingAlgebra α] (v : ℕ → α) : List Form → α
  | [] => ⊤
  | φ :: Γ => φ.eval v ⊓ ctxEval v Γ
-- @endregion

-- @region categorical_logic.ctx_eval_le_of_mem
-- @provenance independent
/-- The meet of the hypotheses lies below each hypothesis. -/
theorem ctxEval_le_of_mem {α : Type*} [HeytingAlgebra α] (v : ℕ → α) {Γ : List Form}
    {φ : Form} (h : φ ∈ Γ) : ctxEval v Γ ≤ φ.eval v := by
  induction Γ with
  | nil => exact absurd h List.not_mem_nil
  | cons ψ Γ ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact inf_le_left
    · exact inf_le_right.trans (ih h')
-- @endregion

-- @region categorical_logic.derives_sound
-- @provenance independent
/-- **Soundness of intuitionistic logic for Heyting algebras**: if `φ` is derivable from `Γ`,
then in *every* Heyting algebra and for *every* valuation, `⋀Γ ≤ ⟦φ⟧`. Each rule is one law of
Heyting algebras: `→I` and `→E` are the two directions of `c ≤ (a ⇨ b) ↔ c ∧ a ≤ b`, and
`∨E` uses distributivity `c ∧ (a ∨ b) = (c ∧ a) ∨ (c ∧ b)`. -/
theorem derives_sound {α : Type*} [HeytingAlgebra α] (v : ℕ → α) {Γ : List Form} {φ : Form}
    (h : Derives Γ φ) : ctxEval v Γ ≤ φ.eval v := by
  induction h with
  | hyp hm => exact ctxEval_le_of_mem v hm
  | topI => exact le_top
  | botE _ ih => exact ih.trans bot_le
  | andI _ _ ih₁ ih₂ => exact le_inf ih₁ ih₂
  | andE₁ _ ih => exact ih.trans inf_le_left
  | andE₂ _ ih => exact ih.trans inf_le_right
  | orI₁ _ ih => exact ih.trans le_sup_left
  | orI₂ _ ih => exact ih.trans le_sup_right
  | @orE Γ φ ψ χ _ _ _ ih ih₁ ih₂ =>
    -- `c ≤ a ∨ b`, `a ∧ c ≤ x` and `b ∧ c ≤ x` give `c = c ∧ (a ∨ b) = (c ∧ a) ∨ (c ∧ b) ≤ x`.
    calc ctxEval v Γ ≤ ctxEval v Γ ⊓ (φ.eval v ⊔ ψ.eval v) := le_inf le_rfl ih
      _ = (ctxEval v Γ ⊓ φ.eval v) ⊔ (ctxEval v Γ ⊓ ψ.eval v) := inf_sup_left _ _ _
      _ ≤ χ.eval v := by
        apply sup_le
        · rw [inf_comm]; exact ih₁
        · rw [inf_comm]; exact ih₂
  | @impI Γ φ ψ _ ih =>
    show ctxEval v Γ ≤ φ.eval v ⇨ ψ.eval v
    rw [le_himp_iff, inf_comm]
    exact ih
  | impE _ _ ih₁ ih₂ =>
    exact (le_inf ih₁ ih₂).trans himp_inf_le
-- @endregion

-- @region categorical_logic.derives_imp_self
-- @provenance independent
/-- `φ → φ` is derivable from no hypotheses: assume `φ` (`→I`), then use the hypothesis. Under
Curry–Howard this derivation is the identity function `λx. x`. -/
theorem derives_imp_self (φ : Form) : Derives [] (.imp φ φ) :=
  Derives.impI (Derives.hyp (List.mem_singleton_self φ))
-- @endregion

-- @region categorical_logic.derives_not_not_em
-- @provenance independent
/-- `¬¬(p ∨ ¬p)` **is** derivable intuitionistically. The derivation: assume
`h : ¬(p ∨ ¬p)`; to refute it, prove `p ∨ ¬p` by proving `¬p` (assume `p`, then `h (inl p)` is
absurd) and applying `inr`. -/
theorem derives_not_not_em (n : ℕ) :
    Derives [] (Form.neg (Form.neg (.or (.atom n) (Form.neg (.atom n))))) := by
  apply Derives.impI
  apply Derives.impE (Derives.hyp (List.mem_singleton_self _))
  apply Derives.orI₂
  apply Derives.impI
  apply Derives.impE (Derives.hyp (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact Derives.orI₁ (Derives.hyp (List.mem_cons_self))
-- @endregion

-- @region categorical_logic.not_derives_em
-- @provenance independent
/-- **Excluded middle is not derivable** in intuitionistic propositional logic. If it were,
soundness would force `U ∨ ¬U = ⊤` for every open set `U ⊆ ℝ`, contradicting
`opens_real_not_boolean`. (The semantics does the work: no search through derivations.) -/
theorem not_derives_em (n : ℕ) : ¬ Derives [] (.or (.atom n) (Form.neg (.atom n))) := by
  intro h
  obtain ⟨U, hU⟩ := opens_real_not_boolean
  have hs := derives_sound (fun _ => U) h
  apply hU
  apply top_le_iff.mp
  simpa [ctxEval, Form.eval, Form.neg, himp_bot] using hs
-- @endregion

end Lumenary.CategoricalLogic
