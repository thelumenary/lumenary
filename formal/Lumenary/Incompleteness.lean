/-
The Lumenary — formal mathematics
Gödel's incompleteness theorems: the diagonal argument behind them, Tarski's undefinability of
truth, and an incompleteness theorem derived from the unsolvability of the halting problem.

What is formalised, honestly. Mathlib does not contain Gödel's theorems for Peano arithmetic: the
arithmetisation of syntax and the representability of computable functions in Robinson
arithmetic `Q` are long and are not done here. What *is* proved below is:
1. Lawvere's fixed-point theorem, the abstract shape of every diagonal argument (independent);
2. an abstract diagonal lemma, Tarski's theorem and the (semantic) first incompleteness theorem
   for any "diagonalisable system" in the sense of Smullyan — the arithmetical facts that
   provability, substitution and negation are definable appear as *hypotheses* (independent);
3. a genuine incompleteness theorem about programs: no sound theory whose theorems can be
   computably listed proves every true statement "program `c` does not halt". It is derived
   from Mathlib's proof that the halting problem is not semi-decidable (independent);
4. library facts: Turing's theorem, that first-order formulas over a countable language can be
   numbered, and that multiplication is not definable in Presburger arithmetic.
-/
import Mathlib.Computability.Halting
import Mathlib.ModelTheory.Encoding
import Mathlib.ModelTheory.Arithmetic.Presburger.Definability

namespace Lumenary.Incompleteness

/-! ### The diagonal argument, abstractly -/

-- @region incompleteness.lawvere_fixed_point
-- @provenance independent
/-- **Lawvere's fixed-point theorem** (1969), the abstract core of the diagonal arguments of
Cantor, Russell, Gödel, Tarski and Turing. If `e : A → (A → B)` hits *every* function
`A → B`, then every map `f : B → B` has a fixed point.
Proof: the diagonal function `g a = f (e a a)` is `e a₀` for some `a₀`, and then
`e a₀ a₀ = g a₀ = f (e a₀ a₀)`. -/
theorem lawvere_fixed_point {A B : Type*} (e : A → A → B) (he : Function.Surjective e)
    (f : B → B) : ∃ b, f b = b := by
  obtain ⟨a₀, ha₀⟩ := he (fun a => f (e a a))
  -- Evaluate the equation `e a₀ = g` at the diagonal point `a₀`.
  exact ⟨e a₀ a₀, (congrFun ha₀ a₀).symm⟩
-- @endregion

-- @region incompleteness.cantor_from_lawvere
-- @provenance independent
/-- Cantor's theorem as a corollary: there is no surjection from `A` onto the predicates
`A → Prop`, because negation `¬ : Prop → Prop` has no fixed point (`P ↔ ¬P` is absurd).
Mathlib's version for sets is `Function.cantor_surjective`. -/
theorem cantor_from_lawvere {A : Type*} (e : A → A → Prop) : ¬ Function.Surjective e := by
  intro he
  obtain ⟨P, hP⟩ := lawvere_fixed_point e he Not
  exact iff_not_self (Iff.of_eq hP.symm)
-- @endregion

/-! ### Diagonalisable systems (after Smullyan) -/

-- @region incompleteness.diag_system
-- @provenance definition
/-- An abstract **diagonalisable system**, after R. M. Smullyan, *Gödel's Incompleteness
Theorems* (1992), chapter 1. It has formulas with one free variable, sentences, Gödel numbers
for both, the substitution `subst φ n = φ(n̄)` of a numeral, a negation, and two predicates on
sentences: truth (in the intended model) and provability (in the theory). The number
`diag (code ψ)` is the Gödel number of the *diagonalisation* `ψ(⌜ψ⌝)`. For first-order
arithmetic all of this is real: Gödel numbers are natural numbers and `diag` is primitive
recursive. -/
structure DiagSystem where
  /-- Formulas with one free variable. -/
  Formula : Type
  /-- Sentences (no free variables). -/
  Sentence : Type
  /-- The Gödel number `⌜ψ⌝` of a formula. -/
  code : Formula → ℕ
  /-- The Gödel number of a sentence. -/
  scode : Sentence → ℕ
  /-- Different sentences have different Gödel numbers. -/
  scode_injective : Function.Injective scode
  /-- `subst ψ n` is the sentence `ψ(n̄)`. -/
  subst : Formula → ℕ → Sentence
  /-- Negation of sentences. -/
  neg : Sentence → Sentence
  /-- Truth in the intended model. -/
  True : Sentence → Prop
  /-- Provability in the theory. -/
  Provable : Sentence → Prop
  true_neg : ∀ s, True (neg s) ↔ ¬ True s
  /-- The diagonal function on Gödel numbers. -/
  diag : ℕ → ℕ
  diag_code : ∀ ψ, diag (code ψ) = scode (subst ψ (code ψ))
-- @endregion

namespace DiagSystem

variable (S : DiagSystem)

-- @region incompleteness.expressible
-- @provenance definition
/-- A set `A` of natural numbers is **expressible** if some formula `ψ` defines it:
`ψ(n̄)` is true exactly when `n ∈ A`. -/
def Expressible (A : Set ℕ) : Prop :=
  ∃ ψ : S.Formula, ∀ n, S.True (S.subst ψ n) ↔ n ∈ A
-- @endregion

-- @region incompleteness.diagonal_lemma
-- @provenance independent
/-- **The diagonal lemma (semantic form).** Suppose that whenever `A` is expressible, so is
`diag⁻¹(A) = {n | diag n ∈ A}` (in arithmetic: substitution is definable). Then for every
expressible `A` there is a sentence `G` that is true iff its own Gödel number lies in `A`.
Proof: let `ψ` express `diag⁻¹(A)` and put `G = ψ(⌜ψ⌝)`. Then
`G` true ⟺ `⌜ψ⌝ ∈ diag⁻¹(A)` ⟺ `diag ⌜ψ⌝ ∈ A` ⟺ `⌜G⌝ ∈ A`. -/
theorem diagonal_lemma
    (hdiag : ∀ A : Set ℕ, S.Expressible A → S.Expressible (S.diag ⁻¹' A))
    {A : Set ℕ} (hA : S.Expressible A) : ∃ G : S.Sentence, S.True G ↔ S.scode G ∈ A := by
  obtain ⟨ψ, hψ⟩ := hdiag A hA
  refine ⟨S.subst ψ (S.code ψ), ?_⟩
  calc S.True (S.subst ψ (S.code ψ)) ↔ S.code ψ ∈ S.diag ⁻¹' A := hψ (S.code ψ)
    _ ↔ S.diag (S.code ψ) ∈ A := Iff.rfl
    _ ↔ S.scode (S.subst ψ (S.code ψ)) ∈ A := by rw [S.diag_code ψ]
-- @endregion

-- @region incompleteness.tarski_undefinability
-- @provenance independent
/-- **Tarski's undefinability of truth (abstract form).** If expressible sets are closed under
complements (negation is definable) and under `diag⁻¹` (substitution is definable), then the set
of Gödel numbers of *true* sentences is not expressible.
Proof: otherwise its complement is expressible, and the diagonal lemma gives a sentence `G`
that is true iff `⌜G⌝` is not the number of a true sentence, i.e. iff `G` is false. -/
theorem tarski_undefinability
    (hcompl : ∀ A : Set ℕ, S.Expressible A → S.Expressible Aᶜ)
    (hdiag : ∀ A : Set ℕ, S.Expressible A → S.Expressible (S.diag ⁻¹' A)) :
    ¬ S.Expressible (S.scode '' {s | S.True s}) := by
  intro hT
  obtain ⟨G, hG⟩ := S.diagonal_lemma hdiag (hcompl _ hT)
  -- `⌜G⌝` is the code of a true sentence iff `G` is true, by injectivity of the coding.
  have hcode : S.scode G ∈ S.scode '' {s | S.True s} ↔ S.True G :=
    S.scode_injective.mem_set_image
  have : S.True G ↔ ¬ S.True G := hG.trans (not_congr hcode)
  exact iff_not_self this
-- @endregion

-- @region incompleteness.first_incompleteness
-- @provenance independent
/-- **The first incompleteness theorem (abstract, semantic form).** Suppose the theory is
*sound* (it proves only true sentences), that the set of Gödel numbers of provable sentences is
expressible (Gödel's arithmetisation), and that expressible sets are closed under complements
and `diag⁻¹`. Then there is a sentence `G` that is true but unprovable, and whose negation is
unprovable too: the theory is incomplete.
Proof: the diagonal lemma applied to the non-provable codes gives `G` with
"`G` true ⟺ `G` unprovable". If `G` were provable it would be true, hence unprovable; so `G`
is unprovable, hence true. If `¬G` were provable it would be true, so `G` would be false. -/
theorem first_incompleteness
    (sound : ∀ s, S.Provable s → S.True s)
    (hprov : S.Expressible (S.scode '' {s | S.Provable s}))
    (hcompl : ∀ A : Set ℕ, S.Expressible A → S.Expressible Aᶜ)
    (hdiag : ∀ A : Set ℕ, S.Expressible A → S.Expressible (S.diag ⁻¹' A)) :
    ∃ G : S.Sentence, S.True G ∧ ¬ S.Provable G ∧ ¬ S.Provable (S.neg G) := by
  obtain ⟨G, hG⟩ := S.diagonal_lemma hdiag (hcompl _ hprov)
  have hcode : S.scode G ∈ S.scode '' {s | S.Provable s} ↔ S.Provable G :=
    S.scode_injective.mem_set_image
  -- The fixed-point property: `G` is true iff `G` is not provable.
  have hfix : S.True G ↔ ¬ S.Provable G := hG.trans (not_congr hcode)
  have hunprov : ¬ S.Provable G := fun hp => hfix.mp (sound G hp) hp
  have htrue : S.True G := hfix.mpr hunprov
  refine ⟨G, htrue, hunprov, fun hneg => ?_⟩
  exact (S.true_neg G).mp (sound _ hneg) htrue
-- @endregion

end DiagSystem

/-! ### Incompleteness from the halting problem -/

-- @region incompleteness.halting_undecidable
-- @provenance library
/-- **Turing (1936):** the halting problem is undecidable — no computable procedure decides,
for every program `c`, whether `c` halts on input `n`. Here programs are Mathlib's codes
`Nat.Partrec.Code` for partial recursive functions; this applies
`ComputablePred.halting_problem`. -/
theorem halting_undecidable (n : ℕ) :
    ¬ ComputablePred fun c : Nat.Partrec.Code => (c.eval n).Dom :=
  ComputablePred.halting_problem n
-- @endregion

-- @region incompleteness.halting_incompleteness
-- @provenance independent
/-- **Incompleteness from the halting problem** (after Turing 1936 and Kleene). Let `Provable`
be any set of (Gödel numbers of) sentences whose members can be computably listed — as the
theorems of every recursively axiomatised theory can — and let `nonHalt c` be a computable
assignment, to each program `c`, of a sentence meaning "`c` does not halt on input `n`". If the
theory is sound for these sentences, then some program never halts but the theory cannot prove
it. Proof: otherwise "`c` does not halt" would be semi-decidable — list the theorems and wait
for `nonHalt c` — and Mathlib's `ComputablePred.halting_problem_not_re` says it is not. -/
theorem halting_incompleteness (n : ℕ) (Provable : ℕ → Prop) (hre : REPred Provable)
    (nonHalt : Nat.Partrec.Code → ℕ) (hc : Computable nonHalt)
    (sound : ∀ c, Provable (nonHalt c) → ¬ (c.eval n).Dom) :
    ∃ c : Nat.Partrec.Code, ¬ (c.eval n).Dom ∧ ¬ Provable (nonHalt c) := by
  by_contra h
  push Not at h
  -- `h : ∀ c, ¬ (c.eval n).Dom → Provable (nonHalt c)`: the theory would be complete for
  -- non-halting, so non-halting would be semi-decidable.
  have hcomp : REPred fun c => Provable (nonHalt c) := hre.comp hc
  exact ComputablePred.halting_problem_not_re n (hcomp.of_eq fun c => ⟨sound c, h c⟩)
-- @endregion

/-! ### Arithmetisation and the need for multiplication -/

-- @region incompleteness.formulas_countable
-- @provenance library
/-- The first step of arithmetisation: over a countable language, the first-order formulas
(with variables indexed by `ℕ`) form a countable set, so they can be numbered. This is the
instance `FirstOrder.Language.Formula`'s `Countable` from `Mathlib.ModelTheory.Encoding`. -/
theorem formulas_countable (L : FirstOrder.Language) [Countable L.Symbols] :
    Countable (L.Formula ℕ) :=
  inferInstance
-- @endregion

-- @region incompleteness.presburger_mul_not_definable
-- @provenance library
/-- Incompleteness needs multiplication. In the language `(0, 1, +)` of Presburger arithmetic
the graph of multiplication `{(a, b, c) | a = b * c}` is **not definable** in `ℕ`, even with
any set `A` of parameters — and Presburger arithmetic is complete and decidable. This applies
Mathlib's `FirstOrder.Language.presburger.mul_not_definable` (the definable sets are exactly the
semilinear ones). -/
theorem presburger_mul_not_definable (A : Set ℕ) :
    ¬ A.Definable FirstOrder.Language.presburger {v : Fin 3 → ℕ | v 0 = v 1 * v 2} :=
  FirstOrder.Language.presburger.mul_not_definable
-- @endregion

end Lumenary.Incompleteness
