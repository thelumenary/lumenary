/-
The Lumenary — formal mathematics
Structure-preserving maps: homomorphisms and isomorphisms.

Proved here (`@provenance independent`), mirroring the lesson: composites of operation-preserving
maps preserve the operation; the inverse of a bijective operation-preserving map preserves the
operation (for *any* binary operations, so in particular for groups and rings); an additive
homomorphism of groups sends `0` to `0` and negatives to negatives; a surjective homomorphism
transfers commutativity; reduction modulo `n` is not injective; `ln(uv) = ln u + ln v`,
derived from `exp(x + y) = exp x · exp y` by the inverse theorem; clock arithmetic mod 4 is not
isomorphic to the Klein four-group `ℤ/2 × ℤ/2`; an explicit isomorphism `ℤ/6 ≅ ℤ/2 × ℤ/3`; and
a bijection that preserves an order relation although its inverse does not.

From the library (`@provenance library`): `Int.cast_add`, `Int.cast_mul` (reduction mod `n`
preserves `+` and `×`), `Real.exp_add`, `ZMod.chineseRemainder`, and Mathlib's definition of a
graph colouring as a graph homomorphism. Our `PreservesOp` is a home-made, unbundled notion;
Mathlib's bundled versions are `AddHom`, `AddMonoidHom` (`→+`), `MonoidHom` (`→*`),
`RingHom` (`→+*`) and the equivalences `AddEquiv` (`≃+`), `MulEquiv` (`≃*`), `RingEquiv`
(`≃+*`), which package the map together with the proofs.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Lumenary.StructurePreservingMaps

universe u v w

/-! ### Preserving an operation -/

-- @region structure_preserving_maps.preserves_op
-- @provenance definition
/-- `PreservesOp f opA opB` says that `f : A → B` **preserves the operation**: combining first
and then mapping gives the same as mapping first and then combining,
`f (x ∗ y) = f x ⋆ f y` for all `x y`, where `∗` is `opA` and `⋆` is `opB`. -/
def PreservesOp {A : Type u} {B : Type v} (f : A → B) (opA : A → A → A) (opB : B → B → B) :
    Prop :=
  ∀ x y, f (opA x y) = opB (f x) (f y)
-- @endregion

-- @region structure_preserving_maps.preserves_op_id
-- @provenance independent
/-- The identity map preserves every operation: both sides are `x ∗ y`. -/
theorem preservesOp_id {A : Type u} (op : A → A → A) : PreservesOp id op op :=
  fun _ _ => rfl
-- @endregion

-- @region structure_preserving_maps.preserves_op_comp
-- @provenance independent
/-- **Composites of homomorphisms are homomorphisms.** If `f` turns `∗` into `⋆` and `g` turns
`⋆` into `•`, then `g ∘ f` turns `∗` into `•`:
`g(f(x ∗ y)) = g(f x ⋆ f y) = g(f x) • g(f y)`. -/
theorem PreservesOp.comp {A : Type u} {B : Type v} {C : Type w}
    {opA : A → A → A} {opB : B → B → B} {opC : C → C → C} {f : A → B} {g : B → C}
    (hf : PreservesOp f opA opB) (hg : PreservesOp g opB opC) :
    PreservesOp (g ∘ f) opA opC := by
  intro x y
  calc (g ∘ f) (opA x y) = g (f (opA x y)) := rfl
    _ = g (opB (f x) (f y)) := by rw [hf]
    _ = opC (g (f x)) (g (f y)) := hg _ _
-- @endregion

-- @region structure_preserving_maps.preserves_op_inverse
-- @provenance independent
/-- **The inverse of a bijective homomorphism is a homomorphism.** Let `g` be a two-sided inverse
of `f` (`g (f x) = x` and `f (g u) = u`). For `u v` in `B`, write `u = f (g u)` and
`v = f (g v)`; then
`g (u ⋆ v) = g (f (g u) ⋆ f (g v)) = g (f (g u ∗ g v)) = g u ∗ g v`.
Nothing about groups is used: this holds for any binary operations. -/
theorem PreservesOp.inverse {A : Type u} {B : Type v} {opA : A → A → A} {opB : B → B → B}
    {f : A → B} {g : B → A} (hf : PreservesOp f opA opB)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) :
    PreservesOp g opB opA := by
  intro u v
  calc g (opB u v) = g (opB (f (g u)) (f (g v))) := by rw [hfg u, hfg v]
    _ = g (f (opA (g u) (g v))) := by rw [hf]
    _ = opA (g u) (g v) := hgf _
-- @endregion

/-! ### Reduction modulo `n` -/

-- @region structure_preserving_maps.reduce_add
-- @provenance library
/-- Reduction modulo `n`, `ℤ → ℤ/n`, preserves addition. This is core Mathlib's `Int.cast_add`
(the map `ℤ → ZMod n` is the canonical "cast"). -/
theorem reduce_add (n : ℕ) : PreservesOp (fun a : ℤ => (a : ZMod n)) (· + ·) (· + ·) :=
  fun a b => Int.cast_add a b
-- @endregion

-- @region structure_preserving_maps.reduce_mul
-- @provenance library
/-- Reduction modulo `n` also preserves multiplication: Mathlib's `Int.cast_mul`. -/
theorem reduce_mul (n : ℕ) : PreservesOp (fun a : ℤ => (a : ZMod n)) (· * ·) (· * ·) :=
  fun a b => Int.cast_mul a b
-- @endregion

-- @region structure_preserving_maps.reduce_not_injective
-- @provenance independent
/-- …but for `n ≠ 0` it is **not injective**: `n` and `0` have the same remainder. So reduction
mod `n` is a homomorphism, not an isomorphism. -/
theorem reduce_not_injective (n : ℕ) (hn : n ≠ 0) :
    ¬ Function.Injective (fun a : ℤ => (a : ZMod n)) := by
  intro hinj
  have h : ((n : ℤ) : ZMod n) = ((0 : ℤ) : ZMod n) := by
    rw [Int.cast_natCast, ZMod.natCast_self, Int.cast_zero]
  have h' : (n : ℤ) = 0 := hinj h
  exact hn (by exact_mod_cast h')
-- @endregion

/-! ### Homomorphisms of groups -/

-- @region structure_preserving_maps.map_zero
-- @provenance independent
/-- An addition-preserving map between additive groups sends `0` to `0`:
`f 0 + f 0 = f (0 + 0) = f 0 = f 0 + 0`, and cancelling `f 0` gives `f 0 = 0`.
(Mathlib: `map_zero` for bundled homomorphisms.) -/
theorem map_zero_of_preservesOp {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] {f : A → B}
    (hf : PreservesOp f (· + ·) (· + ·)) : f 0 = 0 := by
  have h : f 0 + f 0 = f 0 + 0 :=
    calc f 0 + f 0 = f (0 + 0) := (hf 0 0).symm
      _ = f 0 := by rw [add_zero]
      _ = f 0 + 0 := (add_zero _).symm
  exact add_left_cancel h
-- @endregion

-- @region structure_preserving_maps.map_neg
-- @provenance independent
/-- …and it sends negatives to negatives: `f (-x) + f x = f (-x + x) = f 0 = 0`, so
`f (-x) = -f x`. (Mathlib: `map_neg`.) -/
theorem map_neg_of_preservesOp {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] {f : A → B}
    (hf : PreservesOp f (· + ·) (· + ·)) (x : A) : f (-x) = -f x := by
  have h : f (-x) + f x = 0 :=
    calc f (-x) + f x = f (-x + x) := (hf (-x) x).symm
      _ = f 0 := by rw [neg_add_cancel]
      _ = 0 := map_zero_of_preservesOp hf
  exact eq_neg_of_add_eq_zero_left h
-- @endregion

-- @region structure_preserving_maps.comm_of_surjective
-- @provenance independent
/-- **Structure transfers along homomorphisms.** If `f` preserves the operation and is
surjective, and `∗` is commutative, then so is `⋆`: write `u = f x`, `v = f y`; then
`u ⋆ v = f (x ∗ y) = f (y ∗ x) = v ⋆ u`. In particular isomorphic structures are either both
commutative or both not. -/
theorem comm_of_surjective {A : Type u} {B : Type v} {opA : A → A → A} {opB : B → B → B}
    {f : A → B} (hf : PreservesOp f opA opB) (hsurj : Function.Surjective f)
    (hcomm : ∀ x y, opA x y = opA y x) : ∀ u v, opB u v = opB v u := by
  intro u v
  obtain ⟨x, rfl⟩ := hsurj u
  obtain ⟨y, rfl⟩ := hsurj v
  rw [← hf, ← hf, hcomm]
-- @endregion

/-! ### Exponential and logarithm -/

-- @region structure_preserving_maps.exp_preserves
-- @provenance library
/-- `exp : (ℝ, +) → (ℝ, ×)` turns sums into products: Mathlib's `Real.exp_add`. -/
theorem exp_preserves : PreservesOp Real.exp (· + ·) (· * ·) :=
  Real.exp_add
-- @endregion

-- @region structure_preserving_maps.pos_mul
-- @provenance definition
/-- The positive reals `ℝ>0`, as the subtype `{y : ℝ // 0 < y}`, with multiplication
(a product of positive numbers is positive, `mul_pos`). -/
def posMul (u v : {y : ℝ // 0 < y}) : {y : ℝ // 0 < y} :=
  ⟨u.1 * v.1, mul_pos u.2 v.2⟩
-- @endregion

-- @region structure_preserving_maps.exp_pos
-- @provenance definition
/-- `exp` as a map `ℝ → ℝ>0` (its values are positive, `Real.exp_pos`). -/
noncomputable def expPos (x : ℝ) : {y : ℝ // 0 < y} :=
  ⟨Real.exp x, Real.exp_pos x⟩
-- @endregion

-- @region structure_preserving_maps.log_pos
-- @provenance definition
/-- `ln` as a map `ℝ>0 → ℝ`. -/
noncomputable def logPos (u : {y : ℝ // 0 < y}) : ℝ :=
  Real.log u.1
-- @endregion

-- @region structure_preserving_maps.exp_pos_preserves
-- @provenance independent
/-- `exp : (ℝ, +) → (ℝ>0, ×)` preserves the operations; two elements of a subtype are equal
when their values are (`Subtype.ext`), so this is `Real.exp_add` again. -/
theorem expPos_preserves : PreservesOp expPos (· + ·) posMul :=
  fun x y => Subtype.ext (Real.exp_add x y)
-- @endregion

-- @region structure_preserving_maps.log_exp_inverse
-- @provenance independent
/-- `ln` and `exp` are inverse to each other between `ℝ` and `ℝ>0`:
`ln (exp x) = x` (`Real.log_exp`) and `exp (ln u) = u` for `u > 0` (`Real.exp_log`). -/
theorem log_exp_inverse :
    Function.LeftInverse logPos expPos ∧ Function.RightInverse logPos expPos :=
  ⟨fun x => Real.log_exp x, fun u => Subtype.ext (Real.exp_log u.2)⟩
-- @endregion

-- @region structure_preserving_maps.log_pos_preserves
-- @provenance independent
/-- **`ln (uv) = ln u + ln v`, for free.** `exp` is a bijective homomorphism, so by
`PreservesOp.inverse` its inverse `ln` is a homomorphism `(ℝ>0, ×) → (ℝ, +)`. We never touch
the definition of the logarithm. -/
theorem logPos_preserves : PreservesOp logPos posMul (· + ·) :=
  expPos_preserves.inverse log_exp_inverse.1 log_exp_inverse.2
-- @endregion

/-! ### Isomorphic or not? -/

-- @region structure_preserving_maps.no_injective_hom_zmod4_klein
-- @provenance independent
/-- **Clock arithmetic mod 4 is not isomorphic to the Klein four-group** `ℤ/2 × ℤ/2` — not even
by an injective homomorphism. In `ℤ/2 × ℤ/2` every element satisfies `x + x = 0`. If `f`
preserved addition, then `f (1 + 1) = f 1 + f 1 = 0 = f 0 + f 0 = f (0 + 0)`, and injectivity
would give `1 + 1 = 0` in `ℤ/4`, which is false. -/
theorem no_injective_hom_zmod4_klein :
    ¬ ∃ f : ZMod 4 → ZMod 2 × ZMod 2, Function.Injective f ∧ PreservesOp f (· + ·) (· + ·) := by
  rintro ⟨f, hinj, hf⟩
  have hdouble : ∀ x : ZMod 2 × ZMod 2, x + x = 0 := by decide
  have h : f (1 + 1) = f (0 + 0) :=
    calc f (1 + 1) = f 1 + f 1 := hf 1 1
      _ = 0 := hdouble _
      _ = f 0 + f 0 := (hdouble _).symm
      _ = f (0 + 0) := (hf 0 0).symm
  exact absurd (hinj h) (by decide)
-- @endregion

-- @region structure_preserving_maps.zmod4_not_iso_klein
-- @provenance independent
/-- The same fact for Mathlib's bundled isomorphisms of additive groups (`≃+`): there is no
`e : ZMod 4 ≃+ ZMod 2 × ZMod 2`, because `e` would be an injective homomorphism. -/
theorem zmod4_not_iso_klein (e : ZMod 4 ≃+ ZMod 2 × ZMod 2) : False :=
  no_injective_hom_zmod4_klein ⟨e, e.injective, fun x y => map_add e x y⟩
-- @endregion

-- @region structure_preserving_maps.crt6
-- @provenance definition
/-- The map `ℤ/6 → ℤ/2 × ℤ/3`, `x ↦ (x mod 2, x mod 3)`. (`ZMod.cast` reduces a residue
mod 6 to a residue mod 2 or mod 3; this is well defined because 2 and 3 divide 6.) -/
def crt6 (x : ZMod 6) : ZMod 2 × ZMod 3 :=
  (ZMod.cast x, ZMod.cast x)
-- @endregion

-- @region structure_preserving_maps.crt6_iso
-- @provenance independent
/-- **`ℤ/6 ≅ ℤ/2 × ℤ/3`**: `crt6` is a bijection and preserves addition and multiplication.
All three facts are finite checks over the 6 (or 36) cases, done by `decide`. -/
theorem crt6_iso :
    Function.Bijective crt6 ∧ PreservesOp crt6 (· + ·) (· + ·) ∧
      PreservesOp crt6 (· * ·) (· * ·) := by
  unfold PreservesOp
  decide
-- @endregion

-- @region structure_preserving_maps.crt6_library
-- @provenance library
/-- Mathlib's version: the **Chinese remainder theorem** `ZMod.chineseRemainder` gives a ring
isomorphism `ℤ/(mn) ≃+* ℤ/m × ℤ/n` whenever `m` and `n` are coprime. -/
def crt6Library : ZMod 6 ≃+* ZMod 2 × ZMod 3 :=
  ZMod.chineseRemainder (by decide : Nat.Coprime 2 3)
-- @endregion

/-! ### When a structure-preserving bijection is not an isomorphism -/

-- @region structure_preserving_maps.preserves_rel
-- @provenance definition
/-- For a **relation** (an order, the edges of a graph…), "preserving" means: related inputs have
related outputs, `r x y → s (f x) (f y)`. -/
def PreservesRel {A : Type u} {B : Type v} (f : A → B) (r : A → A → Prop) (s : B → B → Prop) :
    Prop :=
  ∀ x y, r x y → s (f x) (f y)
-- @endregion

-- @region structure_preserving_maps.bijection_not_iso
-- @provenance independent
/-- **A structure-preserving bijection whose inverse does not preserve structure.** On `Bool`,
compare the "discrete" order in which only `x ≤ x` holds (the relation `=`) with the usual order
`false ≤ true`. The identity map is a bijection and preserves order from the discrete order to
the usual one; but its inverse (the identity again, read backwards) sends `false ≤ true` to
`false = true`, which fails. So for relations, "bijective and preserving" does not imply
"isomorphism". -/
theorem bijection_not_iso :
    Function.Bijective (id : Bool → Bool) ∧ PreservesRel (id : Bool → Bool) (· = ·) (· ≤ ·) ∧
      ¬ PreservesRel (id : Bool → Bool) (· ≤ ·) (· = ·) := by
  refine ⟨Function.bijective_id, ?_, ?_⟩
  · intro x y h
    subst h
    exact le_refl x
  · intro h
    have hft : false = true := h false true (by decide)
    exact Bool.false_ne_true hft
-- @endregion

/-! ### Graph homomorphisms -/

-- @region structure_preserving_maps.coloring_is_hom
-- @provenance library
/-- In Mathlib, a **colouring** of a graph `G` with colours `α` is *defined* to be a graph
homomorphism from `G` to the complete graph on `α` (adjacent vertices must go to adjacent, that
is, different, colours). This holds by Mathlib's definition `SimpleGraph.Coloring`. -/
theorem coloring_is_hom {V : Type u} (G : SimpleGraph V) (α : Type v) :
    G.Coloring α = (G →g SimpleGraph.completeGraph α) :=
  rfl
-- @endregion

end Lumenary.StructurePreservingMaps
