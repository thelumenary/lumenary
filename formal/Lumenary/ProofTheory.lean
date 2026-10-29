/-
The Lumenary — formal mathematics
Proof theory: a one-sided (Tait-style) sequent calculus for classical propositional logic, its
soundness, the completeness of its *cut-free* fragment, and hence the admissibility of cut and
the consistency of the calculus; a glimpse of Curry–Howard; and the ordinal ε₀.

What is proved here. Derivations are an inductive predicate on lists of formulas in negation
normal form. Soundness is proved by induction on derivations; completeness of the cut-free
calculus by a terminating proof search (decompose a compound formula, recurse; a sequent of
literals that is valid must contain a complementary pair). Cut admissibility then follows
*semantically*: a derivation with cuts is sound, and every valid sequent has a cut-free
derivation. This is not Gentzen's syntactic cut-elimination procedure (which the lesson proves
by hand and which also works where no completeness theorem is available); the formal proof
shows the same *statement* for propositional logic. The facts about ε₀ apply Mathlib's
`Ordinal.epsilon` (`Mathlib.SetTheory.Ordinal.Veblen`). Gentzen's consistency proof for PA is
not formalised.
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.SetTheory.Ordinal.Veblen

namespace Lumenary.ProofTheory

/-! ### Formulas in negation normal form -/

-- @region proof_theory.fml
-- @provenance definition
/-- Propositional formulas in **negation normal form**: atoms `pos n` (the variable `pₙ`),
negated atoms `neg n` (`¬pₙ`), conjunction and disjunction. Every propositional formula is
equivalent to one of these (push negations inwards with De Morgan's laws). -/
inductive Fml : Type
  | pos : ℕ → Fml
  | neg : ℕ → Fml
  | and : Fml → Fml → Fml
  | or : Fml → Fml → Fml
  deriving DecidableEq
-- @endregion

namespace Fml

-- @region proof_theory.dual
-- @provenance definition
/-- The **dual** `Aᗮ` of a formula: its negation, pushed to the atoms by De Morgan's laws. -/
def dual : Fml → Fml
  | pos n => neg n
  | neg n => pos n
  | and A B => or (dual A) (dual B)
  | or A B => and (dual A) (dual B)
-- @endregion

-- @region proof_theory.eval
-- @provenance definition
/-- Truth of a formula under a valuation `v` assigning a proposition to each variable. -/
def eval (v : ℕ → Prop) : Fml → Prop
  | pos n => v n
  | neg n => ¬ v n
  | and A B => eval v A ∧ eval v B
  | or A B => eval v A ∨ eval v B
-- @endregion

-- @region proof_theory.eval_dual
-- @provenance independent
/-- The dual really is the negation: `Aᗮ` is true exactly when `A` is false. By induction on
`A`, using De Morgan's laws at the connectives. -/
theorem eval_dual (v : ℕ → Prop) : ∀ A : Fml, eval v (dual A) ↔ ¬ eval v A
  | pos n => by simp [dual, eval]
  | neg n => by simp [dual, eval]
  | and A B => by
      simp only [dual, eval, eval_dual v A, eval_dual v B]
      tauto
  | or A B => by
      simp only [dual, eval, eval_dual v A, eval_dual v B]
      tauto
-- @endregion

-- @region proof_theory.weight
-- @provenance definition
/-- The number of connectives: literals weigh `0`. Used as a termination measure. -/
def weight : Fml → ℕ
  | pos _ => 0
  | neg _ => 0
  | and A B => weight A + weight B + 1
  | or A B => weight A + weight B + 1
-- @endregion

end Fml

open Fml

/-! ### Sequents and derivations -/

-- @region proof_theory.valid
-- @provenance definition
/-- A one-sided sequent `⊢ Γ` is read as the disjunction of the formulas in `Γ`. It is
**valid** if every valuation makes at least one formula of `Γ` true. -/
def Valid (Γ : List Fml) : Prop :=
  ∀ v : ℕ → Prop, ∃ A ∈ Γ, A.eval v
-- @endregion

-- @region proof_theory.deriv
-- @provenance definition
/-- Derivations in a one-sided sequent calculus (after Schütte and Tait). `Deriv c Γ` means
`⊢ Γ` is derivable, using the cut rule only if the flag `c` is `true`. The rules:
* **axiom**: `⊢ Γ` whenever `Γ` contains both `pₙ` and `¬pₙ`;
* **∧**: from `⊢ A, Γ` and `⊢ B, Γ` infer `⊢ A ∧ B, Γ`;
* **∨**: from `⊢ A, B, Γ` infer `⊢ A ∨ B, Γ`;
* **exchange**: reorder a sequent;
* **cut**: from `⊢ A, Γ` and `⊢ Aᗮ, Γ` infer `⊢ Γ` (only when `c = true`).
No weakening or contraction rules are needed: the axiom allows any side formulas, and both rules
are admissible (a consequence of `cut_free_complete` below). -/
inductive Deriv : Bool → List Fml → Prop
  | ax {c : Bool} {Γ : List Fml} (n : ℕ) :
      pos n ∈ Γ → neg n ∈ Γ → Deriv c Γ
  | and {c : Bool} {Γ : List Fml} (A B : Fml) :
      Deriv c (A :: Γ) → Deriv c (B :: Γ) → Deriv c (Fml.and A B :: Γ)
  | or {c : Bool} {Γ : List Fml} (A B : Fml) :
      Deriv c (A :: B :: Γ) → Deriv c (Fml.or A B :: Γ)
  | exchange {c : Bool} {Γ Δ : List Fml} :
      Γ.Perm Δ → Deriv c Γ → Deriv c Δ
  | cut {Γ : List Fml} (A : Fml) :
      Deriv true (A :: Γ) → Deriv true (dual A :: Γ) → Deriv true Γ
-- @endregion

-- @region proof_theory.excluded_middle
-- @provenance independent
/-- A first cut-free derivation: `⊢ p₀ ∨ ¬p₀`. Apply the ∨-rule, then the axiom. -/
theorem excluded_middle : Deriv false [Fml.or (pos 0) (neg 0)] :=
  Deriv.or _ _ (Deriv.ax 0 (by simp) (by simp))
-- @endregion

/-! ### Soundness -/

-- @region proof_theory.soundness
-- @provenance independent
/-- **Soundness**: every derivable sequent — with or without cut — is valid. By induction on
the derivation. For the cut rule: if neither `A` nor `Aᗮ` is the true formula supplied by the
premises, some formula of `Γ` is true; and `A`, `Aᗮ` cannot both be true. -/
theorem soundness {c : Bool} {Γ : List Fml} (d : Deriv c Γ) : Valid Γ := by
  induction d with
  | ax n hp hn =>
      intro v
      by_cases h : v n
      · exact ⟨pos n, hp, h⟩
      · exact ⟨neg n, hn, h⟩
  | and A B _ _ ihA ihB =>
      intro v
      obtain ⟨C, hC, hCv⟩ := ihA v
      obtain ⟨D, hD, hDv⟩ := ihB v
      rcases List.mem_cons.mp hC with rfl | hC
      · rcases List.mem_cons.mp hD with rfl | hD
        · exact ⟨Fml.and C D, by simp, hCv, hDv⟩
        · exact ⟨D, List.mem_cons_of_mem _ hD, hDv⟩
      · exact ⟨C, List.mem_cons_of_mem _ hC, hCv⟩
  | or A B _ ih =>
      intro v
      obtain ⟨C, hC, hCv⟩ := ih v
      rcases List.mem_cons.mp hC with rfl | hC
      · exact ⟨Fml.or C B, by simp, Or.inl hCv⟩
      rcases List.mem_cons.mp hC with rfl | hC
      · exact ⟨Fml.or A C, by simp, Or.inr hCv⟩
      · exact ⟨C, List.mem_cons_of_mem _ hC, hCv⟩
  | exchange hp _ ih =>
      intro v
      obtain ⟨C, hC, hCv⟩ := ih v
      exact ⟨C, hp.subset hC, hCv⟩
  | cut A _ _ ih₁ ih₂ =>
      intro v
      obtain ⟨C, hC, hCv⟩ := ih₁ v
      obtain ⟨D, hD, hDv⟩ := ih₂ v
      rcases List.mem_cons.mp hC with rfl | hC
      · rcases List.mem_cons.mp hD with rfl | hD
        · exact absurd hCv ((eval_dual v C).mp hDv)
        · exact ⟨D, hD, hDv⟩
      · exact ⟨C, hC, hCv⟩
-- @endregion

-- @region proof_theory.consistency
-- @provenance independent
/-- **Consistency**: the empty sequent (which would mean "false") has no derivation, even with
cut — no valuation makes a formula of the empty list true. -/
theorem consistency : ¬ Deriv true [] := by
  intro d
  obtain ⟨A, hA, _⟩ := soundness d (fun _ => True)
  simp at hA
-- @endregion

/-! ### Completeness of the cut-free calculus -/

-- @region proof_theory.weight_sum
-- @provenance definition
/-- The total weight (number of connectives) of a sequent. -/
def weightSum (Γ : List Fml) : ℕ := (Γ.map Fml.weight).sum
-- @endregion

-- @region proof_theory.weight_sum_perm
-- @provenance independent
/-- Reordering a sequent does not change its weight. -/
theorem weightSum_perm {Γ Δ : List Fml} (h : Γ.Perm Δ) : weightSum Γ = weightSum Δ :=
  (h.map _).sum_eq
-- @endregion

-- @region proof_theory.weight_sum_cons
-- @provenance independent
/-- The weight of `A, Γ` is the weight of `A` plus that of `Γ`. -/
theorem weightSum_cons (A : Fml) (Γ : List Fml) :
    weightSum (A :: Γ) = A.weight + weightSum Γ := by
  simp [weightSum]
-- @endregion

-- @region proof_theory.valid_perm
-- @provenance independent
/-- Validity does not depend on the order of the formulas. -/
theorem valid_perm {Γ Δ : List Fml} (h : Γ.Perm Δ) (hv : Valid Γ) : Valid Δ := fun v => by
  obtain ⟨C, hC, hCv⟩ := hv v
  exact ⟨C, h.subset hC, hCv⟩
-- @endregion

-- @region proof_theory.valid_and_left
-- @provenance independent
/-- Invertibility of the ∧-rule, semantically: if `⊢ A ∧ B, Γ` is valid, so is `⊢ A, Γ`. -/
theorem valid_and_left {A B : Fml} {Γ : List Fml} (hv : Valid (Fml.and A B :: Γ)) :
    Valid (A :: Γ) := fun v => by
  obtain ⟨C, hC, hCv⟩ := hv v
  rcases List.mem_cons.mp hC with rfl | hC
  · exact ⟨A, by simp, hCv.1⟩
  · exact ⟨C, List.mem_cons_of_mem _ hC, hCv⟩
-- @endregion

-- @region proof_theory.valid_and_right
-- @provenance independent
/-- Invertibility of the ∧-rule, second premise. -/
theorem valid_and_right {A B : Fml} {Γ : List Fml} (hv : Valid (Fml.and A B :: Γ)) :
    Valid (B :: Γ) := fun v => by
  obtain ⟨C, hC, hCv⟩ := hv v
  rcases List.mem_cons.mp hC with rfl | hC
  · exact ⟨B, by simp, hCv.2⟩
  · exact ⟨C, List.mem_cons_of_mem _ hC, hCv⟩
-- @endregion

-- @region proof_theory.valid_or
-- @provenance independent
/-- Invertibility of the ∨-rule, semantically: if `⊢ A ∨ B, Γ` is valid, so is `⊢ A, B, Γ`. -/
theorem valid_or {A B : Fml} {Γ : List Fml} (hv : Valid (Fml.or A B :: Γ)) :
    Valid (A :: B :: Γ) := fun v => by
  obtain ⟨C, hC, hCv⟩ := hv v
  rcases List.mem_cons.mp hC with rfl | hC
  · rcases hCv with h | h
    · exact ⟨A, by simp, h⟩
    · exact ⟨B, by simp, h⟩
  · exact ⟨C, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC), hCv⟩
-- @endregion

-- @region proof_theory.literal_case
-- @provenance independent
/-- A valid sequent of literals contains a complementary pair `pₙ, ¬pₙ`: otherwise the
valuation "`pₙ` is true iff `¬pₙ` occurs in `Γ`" falsifies every formula of `Γ`. -/
theorem literal_case {Γ : List Fml} (hv : Valid Γ)
    (hand : ∀ A B, Fml.and A B ∉ Γ) (hor : ∀ A B, Fml.or A B ∉ Γ) :
    ∃ n, pos n ∈ Γ ∧ neg n ∈ Γ := by
  by_contra hnone
  push Not at hnone
  obtain ⟨C, hC, hCv⟩ := hv (fun n => neg n ∈ Γ)
  cases C with
  | pos n => exact hnone n hC hCv
  | neg n => exact hCv hC
  | and A B => exact hand A B hC
  | or A B => exact hor A B hC
-- @endregion

-- @region proof_theory.cut_free_complete
-- @provenance independent
/-- **Completeness of the cut-free calculus**: every valid sequent has a cut-free derivation.
By strong induction on the number of connectives in `Γ`. If `Γ` contains `A ∧ B`, move it to the
front; `⊢ A, Γ'` and `⊢ B, Γ'` are still valid (invertibility) and smaller, so derivable; apply
the ∧-rule. Similarly for `A ∨ B`. If `Γ` consists of literals, validity forces a complementary
pair, and the axiom applies. Note that only subformulas of `Γ` ever appear: this is the
*subformula property* of cut-free proofs. -/
theorem cut_free_complete : ∀ (k : ℕ) (Γ : List Fml), weightSum Γ = k → Valid Γ →
    Deriv false Γ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Γ hk hv
    by_cases hand : ∃ A B, Fml.and A B ∈ Γ
    · obtain ⟨A, B, hmem⟩ := hand
      have hp : Γ.Perm (Fml.and A B :: Γ.erase (Fml.and A B)) := List.perm_cons_erase hmem
      have hw := weightSum_perm hp
      rw [weightSum_cons] at hw
      have hv' := valid_perm hp hv
      have dA : Deriv false (A :: Γ.erase (Fml.and A B)) :=
        ih _ (by simp only [Fml.weight] at hw; rw [weightSum_cons]; omega) _ rfl
          (valid_and_left hv')
      have dB : Deriv false (B :: Γ.erase (Fml.and A B)) :=
        ih _ (by simp only [Fml.weight] at hw; rw [weightSum_cons]; omega) _ rfl
          (valid_and_right hv')
      exact Deriv.exchange hp.symm (Deriv.and A B dA dB)
    by_cases hor : ∃ A B, Fml.or A B ∈ Γ
    · obtain ⟨A, B, hmem⟩ := hor
      have hp : Γ.Perm (Fml.or A B :: Γ.erase (Fml.or A B)) := List.perm_cons_erase hmem
      have hw := weightSum_perm hp
      rw [weightSum_cons] at hw
      have d : Deriv false (A :: B :: Γ.erase (Fml.or A B)) :=
        ih _ (by simp only [Fml.weight] at hw; rw [weightSum_cons, weightSum_cons]; omega) _ rfl
          (valid_or (valid_perm hp hv))
      exact Deriv.exchange hp.symm (Deriv.or A B d)
    push Not at hand hor
    obtain ⟨n, hp, hn⟩ := literal_case hv hand hor
    exact Deriv.ax n hp hn
-- @endregion

-- @region proof_theory.cut_admissible
-- @provenance independent
/-- **Cut is admissible** in classical propositional logic: whatever can be derived with cuts can
be derived without. Here by the semantic route — soundness, then cut-free completeness —
rather than by Gentzen's syntactic reduction of cuts, which the lesson gives by hand. -/
theorem cut_admissible {Γ : List Fml} (d : Deriv true Γ) : Deriv false Γ :=
  cut_free_complete _ Γ rfl (soundness d)
-- @endregion

-- @region proof_theory.not_derivable_atom
-- @provenance independent
/-- A non-example: the sequent `⊢ p₀` is not derivable, even with cut — the valuation making
every variable false refutes it (soundness). -/
theorem not_derivable_atom : ¬ Deriv true [pos 0] := by
  intro d
  obtain ⟨A, hA, hAv⟩ := soundness d (fun _ => False)
  simp only [List.mem_singleton] at hA
  subst hA
  exact hAv
-- @endregion

/-! ### Curry–Howard: proofs are programs -/

-- @region proof_theory.curry_howard_swap
-- @provenance independent
/-- In Lean, as in the Curry–Howard correspondence, a proof of `A ∧ B → B ∧ A` *is* a program:
the function that takes a pair and swaps its components. Normalising the proof is running the
program. -/
theorem curry_howard_swap (A B : Prop) : A ∧ B → B ∧ A :=
  fun h => ⟨h.2, h.1⟩
-- @endregion

/-! ### The ordinal ε₀ -/

open Ordinal

-- @region proof_theory.epsilon_zero_fixed
-- @provenance library
/-- `ε₀` is a fixed point of `α ↦ ω^α`: `ω^ε₀ = ε₀`. It is the least one, the limit of
`ω, ω^ω, ω^ω^ω, …`. This applies Mathlib's `Ordinal.omega0_opow_epsilon`. -/
theorem epsilon_zero_fixed : ω ^ ε₀ = ε₀ :=
  omega0_opow_epsilon 0
-- @endregion

-- @region proof_theory.omega_tower_lt_epsilon_zero
-- @provenance library
/-- Every finite tower `ω^ω^…^ω` lies below `ε₀`; conversely every ordinal below `ε₀` lies below
such a tower (`Ordinal.lt_epsilon_zero`). Gentzen's proof uses induction along exactly these
ordinals. This applies Mathlib's `Ordinal.iterate_omega0_opow_lt_epsilon_zero`. -/
theorem omega_tower_lt_epsilon_zero (n : ℕ) : (fun a => ω ^ a)^[n] 0 < ε₀ :=
  iterate_omega0_opow_lt_epsilon_zero n
-- @endregion

-- @region proof_theory.omega_pow_omega_lt_epsilon_zero
-- @provenance independent
/-- A concrete instance: `ω^ω < ε₀`, since `ω^ω` is the third stage `ω^(ω^(ω^0))` of the tower
(`ω^0 = 1`, `ω^1 = ω`). -/
theorem omega_pow_omega_lt_epsilon_zero : ω ^ ω < ε₀ := by
  have h := iterate_omega0_opow_lt_epsilon_zero 3
  simpa [Function.iterate_succ, opow_zero, opow_one] using h
-- @endregion

end Lumenary.ProofTheory
