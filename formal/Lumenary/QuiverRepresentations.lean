/-
The Lumenary — formal mathematics
Quiver representations: representations as prefunctors, Tits forms, reflections and the
positive roots of the Dynkin diagram D₄.

Mathlib has quivers (`Quiver`), paths and the free category on a quiver
(`CategoryTheory.Paths`) with its universal property, and modules and finite-dimensional linear
algebra. A representation of a quiver `Q` over a field `k` is precisely a prefunctor from `Q` to
`ModuleCat k`, and by the universal property it is the same as a functor out of the path
category — the categorical form of "representations of `Q` = modules over the path algebra
`kQ`". Here we also prove, by hand, the arithmetic half of Gabriel's theorem for `D₄`: its Tits
form is positive definite, reflections preserve it, and exactly twelve non-negative integer
vectors have Tits form `1` (the twelve positive roots, which Gabriel's theorem matches with the
twelve indecomposable representations). The Kronecker quiver's form is only semidefinite.
Not formalised (and not in Mathlib at this version): Gabriel's theorem itself, reflection
functors, Auslander–Reiten theory and Kac's theorem.
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open CategoryTheory

namespace Lumenary.QuiverRepresentations

universe u v w

/-! ### Representations -/

-- @region quiver_representations.quiver_rep
-- @provenance definition
/-- A representation of a quiver `Q` over a field `k`: a `k`-vector space at each vertex and a
linear map along each arrow. In categorical language this is exactly a prefunctor
`Q ⥤q ModuleCat k` — no relations are imposed, because a quiver has none. -/
abbrev QuiverRep (Q : Type u) [Quiver.{w} Q] (k : Type v) [Field k] :=
  Q ⥤q ModuleCat.{v} k
-- @endregion

-- @region quiver_representations.quiver_rep_to_functor
-- @provenance definition
/-- Every representation extends uniquely to a functor out of the path category: a path
`a₁ ⋯ aₙ` acts by the composite of the linear maps along its arrows. (A functor from the path
category to `ModuleCat k` is the same as a module over the path algebra `kQ`.) This uses
Mathlib's `Paths.lift`. -/
noncomputable def QuiverRep.toFunctor {Q : Type u} [Quiver.{w} Q] {k : Type v} [Field k]
    (ρ : QuiverRep Q k) : Paths Q ⥤ ModuleCat.{v} k :=
  Paths.lift ρ
-- @endregion

-- @region quiver_representations.to_functor_restricts
-- @provenance library
/-- Restricting `ρ.toFunctor` to single arrows gives back `ρ`. This applies Mathlib's
`Paths.lift_spec`. -/
theorem toFunctor_restricts {Q : Type u} [Quiver.{w} Q] {k : Type v} [Field k]
    (ρ : QuiverRep Q k) : Paths.of Q ⋙q ρ.toFunctor.toPrefunctor = ρ :=
  Paths.lift_spec ρ
-- @endregion

-- @region quiver_representations.to_functor_unique
-- @provenance library
/-- ... and `ρ.toFunctor` is the only functor with that property: representations of `Q` are
the same as functors `Paths Q ⥤ ModuleCat k`. This applies Mathlib's `Paths.lift_unique`. -/
theorem toFunctor_unique {Q : Type u} [Quiver.{w} Q] {k : Type v} [Field k]
    (ρ : QuiverRep Q k) (Φ : Paths Q ⥤ ModuleCat.{v} k)
    (hΦ : Paths.of Q ⋙q Φ.toPrefunctor = ρ) : Φ = ρ.toFunctor :=
  Paths.lift_unique ρ Φ hΦ
-- @endregion

-- @region quiver_representations.a2_multiplicities
-- @provenance library
/-- Gabriel's theorem for `A₂ = (1 → 2)`, in numbers. A representation is a linear map
`f : V → W`; it decomposes as `rank f` copies of `k --1--> k`, `dim ker f` copies of `k → 0`
and `dim coker f` copies of `0 → k`. The dimension count behind this is rank–nullity and the
dimension of a quotient: Mathlib's `LinearMap.finrank_range_add_finrank_ker` and
`Submodule.finrank_quotient_add_finrank`. -/
theorem A2_multiplicities {k : Type v} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (f : V →ₗ[k] W) :
    Module.finrank k V = Module.finrank k (LinearMap.range f) +
        Module.finrank k (LinearMap.ker f) ∧
      Module.finrank k W = Module.finrank k (LinearMap.range f) +
        Module.finrank k (W ⧸ LinearMap.range f) := by
  refine ⟨(LinearMap.finrank_range_add_finrank_ker f).symm, ?_⟩
  rw [← Submodule.finrank_quotient_add_finrank (LinearMap.range f), add_comm]
-- @endregion

/-! ### Tits forms -/

-- @region quiver_representations.tits_a2
-- @provenance definition
/-- The Tits form of `A₂ = (1 → 2)`: `q(x, y) = x² + y² - xy`. -/
def titsA2 (x y : ℤ) : ℤ := x ^ 2 + y ^ 2 - x * y
-- @endregion

-- @region quiver_representations.tits_a2_pos
-- @provenance independent
/-- The Tits form of `A₂` is positive definite. Completing the square,
`4q(x, y) = (2x - y)² + 3y²`, which vanishes only when `y = 0` and then `x = 0`. -/
theorem titsA2_pos (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : 0 < titsA2 x y := by
  unfold titsA2
  rcases h with hx | hy
  · have : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg (x - y), sq_nonneg y]
  · have : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (x - y), sq_nonneg x]
-- @endregion

-- @region quiver_representations.tits_d4
-- @provenance definition
/-- The Tits form of a quiver with underlying graph `D₄`: a centre `c` joined to three leaves
`a, b, d`. It does not depend on the orientation of the three arrows:
`q = a² + b² + c² + d² - ac - bc - dc`. -/
def titsD4 (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - a * c - b * c - d * c
-- @endregion

-- @region quiver_representations.tits_d4_sum_of_squares
-- @provenance independent
/-- A sum-of-squares identity for the `D₄` form:
`4q = (2c - a - b - d)² + (a - b)² + (a - d)² + (b - d)² + a² + b² + d²`. -/
theorem titsD4_sum_of_squares (a b c d : ℤ) :
    4 * titsD4 a b c d = (2 * c - a - b - d) ^ 2 + (a - b) ^ 2 + (a - d) ^ 2 + (b - d) ^ 2
      + a ^ 2 + b ^ 2 + d ^ 2 := by
  unfold titsD4
  ring
-- @endregion

-- @region quiver_representations.tits_d4_pos
-- @provenance independent
/-- The Tits form of `D₄` is positive definite: by `titsD4_sum_of_squares`, `q ≤ 0` forces
`a = b = d = 0` and then `2c = 0`. (Positive definiteness of the Tits form characterises the
Dynkin diagrams `A`, `D`, `E` among connected graphs.) -/
theorem titsD4_pos (a b c d : ℤ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    0 < titsD4 a b c d := by
  have key := titsD4_sum_of_squares a b c d
  by_contra hq
  replace hq := not_lt.mp hq
  have s₁ := sq_nonneg (2 * c - a - b - d)
  have s₂ := sq_nonneg (a - b)
  have s₃ := sq_nonneg (a - d)
  have s₄ := sq_nonneg (b - d)
  have s₅ := sq_nonneg a
  have s₆ := sq_nonneg b
  have s₇ := sq_nonneg d
  have ha : a ^ 2 = 0 := by linarith
  have hb : b ^ 2 = 0 := by linarith
  have hd : d ^ 2 = 0 := by linarith
  have hc : (2 * c - a - b - d) ^ 2 = 0 := by linarith
  have ha' : a = 0 := pow_eq_zero_iff two_ne_zero |>.mp ha
  have hb' : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb
  have hd' : d = 0 := pow_eq_zero_iff two_ne_zero |>.mp hd
  have hc' : 2 * c - a - b - d = 0 := pow_eq_zero_iff two_ne_zero |>.mp hc
  have hc'' : c = 0 := by omega
  rcases h with h | h | h | h <;> contradiction
-- @endregion

-- @region quiver_representations.tits_d4_reflect_centre
-- @provenance independent
/-- The simple reflection at the centre, `c ↦ a + b + d - c`, preserves the Tits form. On
dimension vectors this is what the reflection functor at a sink or source does to every
indecomposable other than the simple one. -/
theorem titsD4_reflect_centre (a b c d : ℤ) :
    titsD4 a b (a + b + d - c) d = titsD4 a b c d := by
  unfold titsD4
  ring
-- @endregion

-- @region quiver_representations.tits_d4_reflect_leaf
-- @provenance independent
/-- The simple reflection at the leaf `a`, `a ↦ c - a`, also preserves the Tits form. -/
theorem titsD4_reflect_leaf (a b c d : ℤ) :
    titsD4 (c - a) b c d = titsD4 a b c d := by
  unfold titsD4
  ring
-- @endregion

-- @region quiver_representations.d4_roots
-- @provenance definition
/-- The twelve positive roots of `D₄`, written `(a, b, c, d)` with `c` the centre. -/
def D4_roots : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1),
   (1, 0, 1, 0), (0, 1, 1, 0), (0, 0, 1, 1),
   (1, 1, 1, 0), (1, 0, 1, 1), (0, 1, 1, 1),
   (1, 1, 1, 1), (1, 1, 2, 1)]
-- @endregion

-- @region quiver_representations.d4_positive_roots
-- @provenance independent
/-- **The positive roots of `D₄`.** A non-negative integer vector has Tits form `1` exactly
when it is one of the twelve vectors in `D4_roots`. Proof: the sum-of-squares identity bounds
`a, b, d ≤ 2` and `c ≤ 4`, leaving finitely many cases to check. By Gabriel's theorem these are
the dimension vectors of the twelve indecomposable representations of any quiver of type `D₄`
(Gabriel's theorem itself is not formalised here). -/
theorem D4_positive_roots (a b c d : ℕ) :
    titsD4 a b c d = 1 ↔ (a, b, c, d) ∈ D4_roots := by
  constructor
  · intro h
    have key := titsD4_sum_of_squares a b c d
    rw [h] at key
    have s₁ := sq_nonneg ((2 : ℤ) * c - a - b - d)
    have s₂ := sq_nonneg ((a : ℤ) - b)
    have s₃ := sq_nonneg ((a : ℤ) - d)
    have s₄ := sq_nonneg ((b : ℤ) - d)
    have s₅ := sq_nonneg (a : ℤ)
    have s₆ := sq_nonneg (b : ℤ)
    have s₇ := sq_nonneg (d : ℤ)
    have ha : a ≤ 2 := by
      have : (a : ℤ) ^ 2 ≤ 4 := by linarith
      have : (a : ℤ) ≤ 2 := by nlinarith
      exact_mod_cast this
    have hb : b ≤ 2 := by
      have : (b : ℤ) ^ 2 ≤ 4 := by linarith
      have : (b : ℤ) ≤ 2 := by nlinarith
      exact_mod_cast this
    have hd : d ≤ 2 := by
      have : (d : ℤ) ^ 2 ≤ 4 := by linarith
      have : (d : ℤ) ≤ 2 := by nlinarith
      exact_mod_cast this
    have hc : c ≤ 4 := by
      have h₀ : ((2 : ℤ) * c - a - b - d) ^ 2 ≤ 4 := by linarith
      have h₁ : (2 : ℤ) * c - a - b - d ≤ 2 := by nlinarith
      have h₂ : (a : ℤ) ≤ 2 := by exact_mod_cast ha
      have h₃ : (b : ℤ) ≤ 2 := by exact_mod_cast hb
      have h₄ : (d : ℤ) ≤ 2 := by exact_mod_cast hd
      have : (c : ℤ) ≤ 4 := by linarith
      exact_mod_cast this
    unfold titsD4 at h
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      simp_all [D4_roots]
  · intro h
    simp only [D4_roots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      norm_num [titsD4]
-- @endregion

-- @region quiver_representations.d4_roots_length
-- @provenance independent
/-- There are exactly twelve positive roots of `D₄` — the same as the number of positive roots
`n(n - 1) = 12` of the root system `D₄` in Lie theory. -/
theorem D4_roots_length : D4_roots.length = 12 := by decide
-- @endregion

-- @region quiver_representations.tits_kronecker_semidefinite
-- @provenance independent
/-- The Kronecker quiver `1 ⇉ 2` has Tits form `q(x, y) = x² + y² - 2xy = (x - y)²`: never
negative, but zero at `(1, 1)`. So it is not positive definite, and the Kronecker quiver has
infinite representation type: over an infinite field there is a one-parameter family of
indecomposables of dimension vector `(1, 1)`, one for each point of the projective line. -/
theorem titsKronecker_semidefinite :
    (∀ x y : ℤ, 0 ≤ x ^ 2 + y ^ 2 - 2 * x * y) ∧ (1 : ℤ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 = 0 := by
  refine ⟨fun x y => ?_, by norm_num⟩
  nlinarith [sq_nonneg (x - y)]
-- @endregion

end Lumenary.QuiverRepresentations
