/-
The Lumenary — formal mathematics
Monads: the list monad and its algebras, the "maybe" monad, Kleisli composition, and the general
theory (adjunctions, Kleisli and Eilenberg–Moore categories, Beck's theorem) from Mathlib.

What is proved here. For the list monad on types we check the monad laws and the Kleisli laws by
induction, and prove the lesson's central example in full: a list-algebra structure on a type `X`
(an evaluation map `List X → X` satisfying the unit and associativity laws) is *the same thing*
as a monoid structure on `X` (`listAlgebraEquivMonoid`). We also show that algebras for the
"maybe" monad `Option` are exactly choices of a base point. These are stated with plain functions
on types, so that the code can be read without the categorical machinery.

What Mathlib provides. `CategoryTheory.Monad`, `Monad.Algebra` (the Eilenberg–Moore category),
`Kleisli`, `Adjunction.toMonad`, the comparison functor, `Monad.monadMonEquiv` (monads are monoids
in the category of endofunctors) and Beck's monadicity theorem
`Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`. We cite these as library results.
Not formalised here: that `Grp` is monadic over `Set`, and the non-equivalence of the Kleisli and
Eilenberg–Moore categories of the list monad (proved in the lesson by counting endomorphisms).
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Ext
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.EquivMon
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Monad.Monadicity

namespace Lumenary.Monads

universe u v w

/-! ### The list monad, by hand -/

-- @region monads.list_monad_laws
-- @provenance independent
/-- **The list monad satisfies the monad laws.** Here `T X = List X`, the unit `η` sends `x` to
the one-element list `[x]`, and the multiplication `μ` flattens a list of lists.
1. associativity `μ ∘ Tμ = μ ∘ μT`: flattening the inner lists first, or the outer list first,
   gives the same list;
2. left unit `μ ∘ ηT = id`: flattening `[xs]` gives `xs`;
3. right unit `μ ∘ Tη = id`: flattening `[[x₁], …, [xₙ]]` gives `[x₁, …, xₙ]`.
Each law is proved by induction on the outer list. -/
theorem list_monad_laws {α : Type u} :
    (∀ xsss : List (List (List α)), (xsss.map List.flatten).flatten = xsss.flatten.flatten) ∧
    (∀ xs : List α, [xs].flatten = xs) ∧
    (∀ xs : List α, (xs.map fun x => [x]).flatten = xs) := by
  refine ⟨fun xsss => ?_, fun xs => by simp, fun xs => ?_⟩
  · induction xsss with
    | nil => rfl
    | cons xss rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatten_append, ih]
  · induction xs with
    | nil => rfl
    | cons x rest ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]
-- @endregion

-- @region monads.list_kleisli
-- @provenance definition
/-- **Kleisli composition for the list monad.** A Kleisli arrow `α → List β` is a
"many-valued function". To compose `f : α → List β` with `g : β → List γ`, apply `g` to every
output of `f` and flatten: in categorical notation `μ ∘ T g ∘ f`. -/
def listKleisli {α : Type u} {β : Type v} {γ : Type w} (f : α → List β) (g : β → List γ) :
    α → List γ :=
  fun a => (f a).flatMap g
-- @endregion

-- @region monads.list_kleisli_laws
-- @provenance independent
/-- **The Kleisli category of the list monad is a category.** Kleisli composition is associative,
and `η = fun a => [a]` is a two-sided identity. Associativity is core Lean's `List.flatMap_assoc`;
the identity laws are short computations. -/
theorem list_kleisli_laws {α β γ δ : Type u} (f : α → List β) (g : β → List γ)
    (h : γ → List δ) :
    listKleisli (listKleisli f g) h = listKleisli f (listKleisli g h) ∧
    listKleisli (fun a => [a]) f = f ∧
    listKleisli f (fun b => [b]) = f := by
  refine ⟨?_, ?_, ?_⟩
  · funext a
    exact List.flatMap_assoc
  · funext a
    simp [listKleisli]
  · funext a
    simp [listKleisli]
-- @endregion

/-! ### Algebras for the list monad are monoids -/

-- @region monads.list_algebra
-- @provenance definition
/-- An **algebra for the list monad** on a type `X`: an evaluation map `act : List X → X` such
that evaluating a one-element list returns its element (`act ∘ η = id`), and evaluating a list of
lists "inside first" or "flatten first" agrees (`act ∘ T act = act ∘ μ`). -/
structure ListAlgebra (X : Type u) where
  /-- Evaluate a list of elements to a single element. -/
  act : List X → X
  /-- The unit law `act [x] = x`. -/
  unit : ∀ x : X, act [x] = x
  /-- The associativity law: evaluate the inner lists first, or flatten first. -/
  assoc : ∀ xss : List (List X), act (xss.map act) = act xss.flatten
-- @endregion

namespace ListAlgebra

variable {X : Type u}

-- @region monads.list_algebra.ext
-- @provenance independent
/-- Two list-algebra structures are equal when their evaluation maps are. -/
@[ext]
theorem ext {A B : ListAlgebra X} (h : A.act = B.act) : A = B := by
  cases A
  cases B
  cases h
  rfl
-- @endregion

-- @region monads.list_algebra.act_cons
-- @provenance independent
/-- In a list algebra, evaluating `x :: xs` is the same as evaluating the two-element list
`[x, act xs]`:
`act [x, act xs] = act [act [x], act xs] = act (flatten [[x], xs]) = act (x :: xs)`,
using the unit law and then the associativity law. -/
theorem act_cons (A : ListAlgebra X) (x : X) (xs : List X) :
    A.act (x :: xs) = A.act [x, A.act xs] := by
  calc A.act (x :: xs) = A.act ([[x], xs].flatten) := by simp
    _ = A.act ([[x], xs].map A.act) := (A.assoc [[x], xs]).symm
    _ = A.act [x, A.act xs] := by simp [A.unit]
-- @endregion

-- @region monads.list_algebra.to_monoid
-- @provenance definition
/-- **Every list algebra is a monoid.** Multiply by evaluating two-element lists,
`x * y = act [x, y]`, and take `1 = act []`. The monoid laws follow from the algebra laws:
for example `(x * y) * z = act [act [x, y], act [z]] = act [x, y, z]`, and likewise
`x * (y * z) = act [x, y, z]`. -/
@[instance_reducible]
def toMonoid (A : ListAlgebra X) : Monoid X where
  mul x y := A.act [x, y]
  one := A.act []
  mul_assoc x y z := by
    show A.act [A.act [x, y], z] = A.act [x, A.act [y, z]]
    have h₁ : A.act [A.act [x, y], z] = A.act [x, y, z] := by
      calc A.act [A.act [x, y], z] = A.act ([[x, y], [z]].map A.act) := by simp [A.unit]
        _ = A.act [x, y, z] := by rw [A.assoc]; simp
    have h₂ : A.act [x, A.act [y, z]] = A.act [x, y, z] := by
      calc A.act [x, A.act [y, z]] = A.act ([[x], [y, z]].map A.act) := by simp [A.unit]
        _ = A.act [x, y, z] := by rw [A.assoc]; simp
    rw [h₁, h₂]
  one_mul x := by
    show A.act [A.act [], x] = x
    calc A.act [A.act [], x] = A.act ([[], [x]].map A.act) := by simp [A.unit]
      _ = x := by rw [A.assoc]; simp [A.unit]
  mul_one x := by
    show A.act [x, A.act []] = x
    calc A.act [x, A.act []] = A.act ([[x], []].map A.act) := by simp [A.unit]
      _ = x := by rw [A.assoc]; simp [A.unit]
-- @endregion

-- @region monads.list_algebra.of_monoid
-- @provenance definition
/-- **Every monoid is a list algebra**: evaluate a list by multiplying it out, `act = List.prod`.
The unit law is `List.prod_singleton` and the associativity law is core Lean's
`List.prod_flatten` (multiplying blockwise, then multiplying the results, is multiplying
everything). -/
def ofMonoid (M : Type u) [Monoid M] : ListAlgebra M where
  act := List.prod
  unit _ := List.prod_singleton
  assoc _ := List.prod_flatten.symm
-- @endregion

-- @region monads.list_algebra.act_eq_prod
-- @provenance independent
/-- **A list algebra is determined by its binary multiplication and unit.** Evaluating any list
is multiplying it out in the monoid `A.toMonoid`. Proof by induction on the list, using
`act_cons` at each step. -/
theorem act_eq_prod (A : ListAlgebra X) (xs : List X) :
    A.act xs = @List.prod X A.toMonoid.toMul A.toMonoid.toOne xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [act_cons, ih]
    rfl
-- @endregion

end ListAlgebra

-- @region monads.list_algebra_equiv_monoid
-- @provenance independent
/-- **Algebras for the list monad are exactly monoids.** On any type `X`, list-algebra structures
correspond bijectively to monoid structures: send an algebra to its binary multiplication, and a
monoid to `List.prod`. Going around one way uses `act_eq_prod`; going around the other way only
has to check that the multiplications agree (`Monoid.ext`), and `List.prod [x, y] = x * (y * 1)`. -/
def listAlgebraEquivMonoid (X : Type u) : ListAlgebra X ≃ Monoid X where
  toFun A := A.toMonoid
  invFun m := @ListAlgebra.ofMonoid X m
  left_inv A := by
    ext xs
    exact (A.act_eq_prod xs).symm
  right_inv m := by
    let _ := m
    apply Monoid.ext
    funext x y
    show List.prod [x, y] = x * y
    simp
-- @endregion

/-! ### Algebras for the "maybe" monad are pointed sets -/

-- @region monads.option_algebra
-- @provenance definition
/-- An **algebra for the maybe monad** `Option` on `X`: a map `act : Option X → X` with
`act (some x) = x` (unit law) and `act ∘ Option.map act = act ∘ Option.join`
(associativity law). -/
structure OptionAlgebra (X : Type u) where
  /-- Evaluate an optional element. -/
  act : Option X → X
  /-- The unit law. -/
  unit : ∀ x : X, act (some x) = x
  /-- The associativity law. -/
  assoc : ∀ oo : Option (Option X), act (oo.map act) = act oo.join
-- @endregion

-- @region monads.option_algebra_equiv
-- @provenance independent
/-- **Algebras for the maybe monad are exactly pointed sets.** An `Option`-algebra on `X` is
determined by where it sends `none`, and every choice of base point gives an algebra (with
`act = fun o => o.getD a`; the associativity law then holds automatically, by checking the three
shapes `none`, `some none`, `some (some x)`). -/
def optionAlgebraEquiv (X : Type u) : OptionAlgebra X ≃ X where
  toFun A := A.act none
  invFun a :=
    { act := fun o => o.getD a
      unit := fun _ => rfl
      assoc := by
        intro oo
        rcases oo with _ | _ | x <;> rfl }
  left_inv A := by
    rcases A with ⟨act, unit, assoc⟩
    have h : (fun o => o.getD (act none)) = act := by
      funext o
      cases o with
      | none => rfl
      | some x => exact (unit x).symm
    simp only [OptionAlgebra.mk.injEq]
    exact h
  right_inv _ := rfl
-- @endregion

/-! ### The general theory, from Mathlib -/

open CategoryTheory

section General

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]

-- @region monads.adjunction_monad
-- @provenance library
/-- **Every adjunction induces a monad.** For `F ⊣ G` with unit `η` and counit `ε`, the monad
`h.toMonad` (Mathlib's `Adjunction.toMonad`) has underlying functor `G ∘ F` (written `F ⋙ G` in
diagrammatic order), unit `η`, and multiplication `μ_X = G(ε_{F X})`. -/
theorem adjunction_monad {F : C ⥤ D} {G : D ⥤ C} (h : F ⊣ G) (X : C) :
    (h.toMonad : C ⥤ C) = F ⋙ G ∧ h.toMonad.η = h.unit ∧
      h.toMonad.μ.app X = G.map (h.counit.app (F.obj X)) :=
  ⟨rfl, rfl, rfl⟩
-- @endregion

-- @region monads.kleisli_induces
-- @provenance library
/-- **The Kleisli adjunction induces the monad.** For a monad `T`, the free functor
`C ⥤ Kleisli T` followed by the forgetful functor `Kleisli T ⥤ C` is isomorphic to `T`
(Mathlib's `Kleisli.Adjunction.toKleisliCompFromKleisliIsoSelf`). -/
theorem kleisli_induces (T : Monad C) :
    Nonempty (Kleisli.Adjunction.toKleisli T ⋙ Kleisli.Adjunction.fromKleisli T ≅
      (T : C ⥤ C)) :=
  ⟨Kleisli.Adjunction.toKleisliCompFromKleisliIsoSelf T⟩
-- @endregion

-- @region monads.eilenberg_moore_induces
-- @provenance library
/-- **The Eilenberg–Moore adjunction induces the monad.** The free-algebra functor
`T.free : C ⥤ T.Algebra` is left adjoint to the forgetful functor (`T.adj`), and the monad of
this adjunction is isomorphic to `T` (Mathlib's `Adjunction.adjToMonadIso`). -/
theorem eilenberg_moore_induces (T : Monad C) : Nonempty (T.adj.toMonad ≅ T) :=
  ⟨Adjunction.adjToMonadIso T⟩
-- @endregion

-- @region monads.comparison
-- @provenance library
/-- **The comparison functor.** For any adjunction `F ⊣ G` with monad `T = G F`, the functor
`K = Monad.comparison h : D ⥤ T.Algebra` sends `B` to the algebra `(G B, G ε_B)`. It is
compatible with both adjunctions: `K ∘ F` is the free-algebra functor (`Monad.left_comparison`)
and the forgetful functor after `K` is `G` (`Monad.comparisonForget`). -/
theorem comparison {F : C ⥤ D} {G : D ⥤ C} (h : F ⊣ G) :
    F ⋙ Monad.comparison h = h.toMonad.free ∧
      Nonempty (Monad.comparison h ⋙ h.toMonad.forget ≅ G) :=
  ⟨Monad.left_comparison h, ⟨Monad.comparisonForget h⟩⟩
-- @endregion

-- @region monads.beck
-- @provenance library
/-- **Beck's monadicity theorem** (one of Mathlib's versions,
`Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`): if `G` has a left adjoint, `D` has
coequalisers of `G`-split pairs, and `G` preserves and reflects them, then `G` is monadic — the
comparison functor `D ⥤ T.Algebra` is an equivalence. -/
theorem beck {F : C ⥤ D} {G : D ⥤ C} (h : F ⊣ G) [Monad.HasCoequalizerOfIsSplitPair G]
    [Monad.PreservesColimitOfIsSplitPair G] [Monad.ReflectsColimitOfIsSplitPair G] :
    Nonempty (MonadicRightAdjoint G) :=
  ⟨Monad.monadicOfHasPreservesReflectsGSplitCoequalizers h⟩
-- @endregion

end General

attribute [local instance] endofunctorMonoidalCategory

-- @region monads.monads_are_monoids
-- @provenance library
/-- **A monad is a monoid in the category of endofunctors.** The category of monads on `C` is
equivalent to the category of monoid objects in `(C ⥤ C, ∘, 𝟭)` (Mathlib's
`Monad.monadMonEquiv`). -/
theorem monads_are_monoids (C : Type u) [Category.{v} C] :
    Nonempty (Monad C ≌ Mon (C ⥤ C)) :=
  ⟨Monad.monadMonEquiv C⟩
-- @endregion

end Lumenary.Monads
