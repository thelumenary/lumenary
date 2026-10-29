/-
The Lumenary — formal mathematics
Homotopy type theory: identity types as path spaces, path induction, transport, and why Lean's
own type theory is *not* homotopy type theory (it validates uniqueness of identity proofs, so
univalence fails in it).

What is proved here. We define an identity type `Paths a b` living in `Type` and build the
first layer of HoTT from its eliminator alone (path induction, `J`): inverses, concatenation,
`ap`, transport, and the groupoid laws as *paths between paths* (so they are `def`s, not
`theorem`s). Then we prove two theorems about Lean itself: every `Paths a b` has at most one
element (Lean's proof-irrelevant `Eq` forces uniqueness of identity proofs), and therefore the
map `idtoeqv : Paths Bool Bool → (Bool ≃ Bool)` is not surjective, so the univalence axiom is
false in Lean. Finally we connect to the classical theorem `π₁(S¹) ≅ ℤ`, which Mathlib proves
with covering spaces (`AddCircle.windingNumberIso`), and formalise the arithmetic step of the
encode–decode proof. Not formalised (and not formalisable in Lean as it stands): univalent
universes, higher inductive types such as the circle `S¹` with `loop : base = base`, and the
synthetic proof that `Ω(S¹) ≃ ℤ`; these live in proof assistants such as Agda (Cubical Agda),
Coq/Rocq with the HoTT library, and Arend.
-/
import Mathlib.Logic.Equiv.Bool
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Topology.Covering.FundamentalGroupCircle

universe u v

namespace Lumenary.HomotopyTypeTheory

/-! ### Identity types and path induction -/

-- @region homotopy_type_theory.paths
-- @provenance definition
/-- The **identity type** of `A`, based at `a`: an inductive family `Paths a b` with a single
constructor `refl : Paths a a`. Read an element `p : Paths a b` as a *path* from `a` to `b`.
Unlike Lean's `Eq`, which lives in `Prop`, this type lives in `Type u`, so its elements are data
and can, a priori, be distinct. -/
inductive Paths {A : Type u} (a : A) : A → Type u
  | refl : Paths a a
-- @endregion

namespace Paths

-- @region homotopy_type_theory.path_induction
-- @provenance definition
/-- **Path induction** (the `J` eliminator, in Paulin-Mohring's based form). To construct an
element of `C b p` for *every* `b` and every path `p : Paths a b`, it suffices to construct one
for `b = a` and `p = refl`. Pattern matching on `refl` with the endpoint `b` free is exactly
this rule; everything below is built from `J` alone. -/
def J {A : Type u} {a : A} (C : (b : A) → Paths a b → Sort v) (c : C a refl) :
    {b : A} → (p : Paths a b) → C b p
  | _, refl => c
-- @endregion

-- @region homotopy_type_theory.inv
-- @provenance definition
/-- The inverse of a path, by path induction: the inverse of `refl` is `refl`. -/
def inv {A : Type u} {a b : A} (p : Paths a b) : Paths b a :=
  J (fun b _ => Paths b a) refl p
-- @endregion

-- @region homotopy_type_theory.concat
-- @provenance definition
/-- Concatenation of paths, by path induction on the second path: `p ⬝ refl = p`. -/
def concat {A : Type u} {a b c : A} (p : Paths a b) (q : Paths b c) : Paths a c :=
  J (fun c _ => Paths a c) p q
-- @endregion

-- @region homotopy_type_theory.ap
-- @provenance definition
/-- **Functions act on paths**: `ap f : Paths a b → Paths (f a) (f b)`. Every function is
automatically "continuous" in HoTT, because it must respect path induction. -/
def ap {A : Type u} {B : Type v} (f : A → B) {a b : A} (p : Paths a b) : Paths (f a) (f b) :=
  J (fun b _ => Paths (f a) (f b)) refl p
-- @endregion

-- @region homotopy_type_theory.transport
-- @provenance definition
/-- **Transport**: a path `p : Paths a b` in the base gives a function `P a → P b` between the
fibres of any type family `P`. Geometrically: lifting a path to a fibration. Logically: the
indiscernibility of identicals (Leibniz's law). -/
def transport {A : Type u} (P : A → Type v) {a b : A} (p : Paths a b) : P a → P b :=
  J (fun b _ => P a → P b) id p
-- @endregion

/-! ### The groupoid laws, as paths between paths -/

-- @region homotopy_type_theory.refl_concat
-- @provenance independent
/-- Left unit law, `refl ⬝ p = p`, as a **path** between paths, constructed by path induction on
`p`. (The right unit law `p ⬝ refl = p` holds by definition of `concat`.) In HoTT a proof of an
equation is an element of an identity type, so this is a `def`: Lean reserves `theorem` for
statements in `Prop`, and `Paths` lives in `Type`. -/
def refl_concat {A : Type u} {a b : A} (p : Paths a b) : Paths (concat refl p) p :=
  J (fun _ p => Paths (concat refl p) p) refl p
-- @endregion

-- @region homotopy_type_theory.concat_inv
-- @provenance independent
/-- Inverse law: `p ⬝ p⁻¹ = refl`, as a path, by path induction on `p`. -/
def concat_inv {A : Type u} {a b : A} (p : Paths a b) : Paths (concat p (inv p)) refl :=
  J (fun _ p => Paths (concat p (inv p)) refl) refl p
-- @endregion

-- @region homotopy_type_theory.concat_assoc
-- @provenance independent
/-- Associativity: `(p ⬝ q) ⬝ r = p ⬝ (q ⬝ r)`, as a path, by path induction on `r` (both sides
then reduce to `p ⬝ q`). In HoTT these laws are themselves paths, and they satisfy further
laws (the pentagon, …) up to higher paths: every type is a weak ∞-groupoid. -/
def concat_assoc {A : Type u} {a b c d : A} (p : Paths a b) (q : Paths b c) (r : Paths c d) :
    Paths (concat (concat p q) r) (concat p (concat q r)) :=
  J (fun _ r => Paths (concat (concat p q) r) (concat p (concat q r))) refl r
-- @endregion

-- @region homotopy_type_theory.transport_concat
-- @provenance independent
/-- Transport is functorial: transporting along `p ⬝ q` is transporting along `p` and then along
`q`. (A path, by induction on `q`.) This is what makes `transport` into a functor from the
path groupoid of `A` to types. -/
def transport_concat {A : Type u} (P : A → Type v) {a b c : A} (p : Paths a b)
    (q : Paths b c) (x : P a) :
    Paths (transport P (concat p q) x) (transport P q (transport P p x)) :=
  J (fun _ q => Paths (transport P (concat p q) x) (transport P q (transport P p x))) refl q
-- @endregion

/-! ### Univalence would identify paths between types with equivalences -/

-- @region homotopy_type_theory.idtoeqv
-- @provenance definition
/-- The canonical map from paths between types to equivalences, `idtoeqv`: by path induction it
sends `refl` to the identity equivalence. **Voevodsky's univalence axiom** says that this map is
itself an equivalence, for all types `A` and `B` in a universe. -/
def idtoeqv {A B : Type u} (p : Paths A B) : A ≃ B :=
  J (fun B _ => A ≃ B) (Equiv.refl A) p
-- @endregion

/-! ### Lean is not homotopy type theory -/

-- @region homotopy_type_theory.paths_subsingleton
-- @provenance independent
/-- **Uniqueness of identity proofs holds in Lean**, even for our `Type`-valued `Paths`: any two
paths `p q : Paths a b` are equal. Proof: `Paths a b` is a *retract* of Lean's `a = b` (map a path
to an equality, and back, and path induction shows the round trip is the identity), and `a = b`
is a proposition with at most one proof (Lean has definitional proof irrelevance). A retract of
a type with at most one element has at most one element. In HoTT this fails: the type of paths
from a point to itself in the circle is `ℤ`. -/
theorem paths_subsingleton {A : Type u} {a b : A} (p q : Paths a b) : p = q := by
  -- From paths to Lean equalities, and back.
  let toEq : {b : A} → Paths a b → a = b := fun p => J (fun b _ => a = b) rfl p
  let ofEq : {b : A} → a = b → Paths a b := fun h => h ▸ refl
  -- The round trip is the identity (path induction, with a motive in `Prop`).
  have round : ∀ {b : A} (p : Paths a b), ofEq (toEq p) = p := by
    intro b p
    exact J (fun _ p => ofEq (toEq p) = p) rfl p
  -- `toEq p` and `toEq q` are proofs of the same proposition, hence equal.
  calc p = ofEq (toEq p) := (round p).symm
    _ = ofEq (toEq q) := rfl
    _ = q := round q
-- @endregion

-- @region homotopy_type_theory.univalence_fails
-- @provenance independent
/-- **The univalence axiom is false in Lean.** The map `idtoeqv : Paths Bool Bool → (Bool ≃ Bool)`
is not surjective: there are two equivalences `Bool ≃ Bool` (the identity and negation), but at
most one path `Bool = Bool` (`paths_subsingleton`). So univalence cannot be added to Lean as an
axiom without making Lean inconsistent; HoTT needs a type theory *without* uniqueness of identity
proofs. -/
theorem univalence_fails : ¬ Function.Surjective (idtoeqv : Paths Bool Bool → (Bool ≃ Bool)) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (Equiv.refl Bool)
  obtain ⟨q, hq⟩ := hsurj Equiv.boolNot
  -- `p = q`, so the identity and negation would be the same equivalence.
  have hpq : p = q := paths_subsingleton p q
  have h : Equiv.refl Bool = Equiv.boolNot := by rw [← hp, ← hq, hpq]
  -- Evaluate both at `true`.
  have h' : true = false := congrArg (fun e : Bool ≃ Bool => e true) h
  exact Bool.noConfusion h'
-- @endregion

end Paths

-- @region homotopy_type_theory.funext_library
-- @provenance library
/-- **Function extensionality**: pointwise equal functions are equal. In HoTT it is a theorem
deduced from univalence (Voevodsky); in Lean it is a theorem deduced from quotient types
(`Quot.sound`). This applies core Lean's `funext`. -/
theorem funext_library {α : Type u} {β : α → Type v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g :=
  funext h
-- @endregion

-- @region homotopy_type_theory.bijective_iff_unique_fibres
-- @provenance library
/-- The set-level shadow of "an equivalence is a map with contractible fibres": a function is
bijective exactly when every fibre `{a | f a = b}` has exactly one element. (In HoTT,
"contractible" replaces "has exactly one element", and the definition then works for types with
higher paths too.) This applies Mathlib's `Function.bijective_iff_existsUnique`. -/
theorem bijective_iff_unique_fibres {α : Type u} {β : Type v} (f : α → β) :
    Function.Bijective f ↔ ∀ b, ∃! a, f a = b :=
  Function.bijective_iff_existsUnique f
-- @endregion

/-! ### The circle -/

-- @region homotopy_type_theory.fundamental_group_circle
-- @provenance library
/-- **The classical theorem: `π₁(S¹) ≅ ℤ`.** Mathlib's `AddCircle.windingNumberIso` proves it
for the circle `ℝ / pℤ` using covering-space theory (the universal cover `ℝ → S¹`), sending a
loop to its winding number. Homotopy type theory proves a synthetic version, `Ω(S¹) ≃ ℤ`, for
the higher inductive circle (Licata and Shulman, 2013). -/
theorem fundamental_group_circle (p : ℝ) [Fact (0 < p)] (x : AddCircle p) :
    Nonempty (FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ) :=
  ⟨AddCircle.windingNumberIso x⟩
-- @endregion

-- @region homotopy_type_theory.encode_loop_pow
-- @provenance independent
/-- **The arithmetic step of encode–decode.** In the HoTT proof, the universal cover of the
circle is the family `code : S¹ → U` with `code(base) = ℤ`, and univalence makes transport along
`loop` equal to the successor `succ : ℤ ≃ ℤ`. Since transport turns concatenation into
composition (`transport_concat`), transport along `loopⁿ` is `succⁿ`, and `encode(loopⁿ)` is
`succⁿ(0)`. Here we prove the last step in ordinary Lean: the `n`-th power of the successor
permutation of `ℤ` sends `k` to `k + n`, for every integer `n` (negative powers included). In
particular `succⁿ(0) = n`. -/
theorem encode_loop_pow (n k : ℤ) : ((Equiv.addRight (1 : ℤ)) ^ n) k = k + n := by
  induction n using Int.induction_on generalizing k with
  | zero => simp
  | succ m ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    simp only [Equiv.coe_addRight]
    ring
  | pred m ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    simp only [Equiv.Perm.inv_def, Equiv.addRight_symm, Equiv.coe_addRight]
    ring
-- @endregion

end Lumenary.HomotopyTypeTheory
