/-
The Lumenary — formal mathematics
Quivers and path algebras: paths and their concatenation, the multiplication of the path
algebra on basis elements, when a quiver has finitely many paths, the linearly oriented quiver
`Aₙ`, and representations as functors out of the free category.

What is proved here. Independently: concatenation of paths, extended by `0` when paths do not
compose, is an associative multiplication on "paths or zero" — the multiplication table of the
basis of the path algebra `kQ` — and the trivial paths are orthogonal idempotents; if every arrow
increases a height function `h`, every path from `a` to `b` has length at most `h b - h a` (so a
finite quiver of this kind has finitely many paths); a cycle of positive length has infinitely many
distinct powers (so `kQ` is infinite-dimensional); and in the linearly oriented quiver
`0 → 1 → ⋯ → n-1` every path from `i` to `j` has length exactly `j - i`.

What Mathlib provides. Quivers (`Quiver`), paths (`Quiver.Path`) with associative concatenation
(`Quiver.Path.comp_assoc`) and additive length, and the free category on a quiver
(`CategoryTheory.Paths`) with its universal property (`Paths.lift`, `Paths.lift_unique`), which
says that a representation of `Q` is the same as a functor out of the path category. Not in
Mathlib at this version, and not formalised here: the path algebra `kQ` as a `k`-algebra, the
equivalence between representations of `Q` and `kQ`-modules, and the classification of
indecomposable representations of `Aₙ`.
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Fintype.Basic

open CategoryTheory

namespace Lumenary.PathAlgebras

universe u v w

/-! ### The multiplication table of the path algebra -/

section PathMultiplication

variable {V : Type u} [Quiver.{v + 1} V] [DecidableEq V]

-- @region path_algebras.path_or_zero
-- @provenance definition
/-- The basis of the path algebra together with zero: either a path `p` from some vertex `a` to
some vertex `b` (recorded with its endpoints), or `none`, standing for `0`. -/
abbrev PathOrZero (V : Type u) [Quiver.{v + 1} V] := Option (Σ a b : V, Quiver.Path a b)
-- @endregion

-- @region path_algebras.pmul
-- @provenance definition
/-- The product of basis paths in `kQ`, with the convention used in the lesson: `p · q` means
"first `p`, then `q`", defined when `p` ends where `q` starts, and `0` otherwise. (Many books
use the opposite order; the two conventions give opposite algebras.) -/
def pmul : PathOrZero V → PathOrZero V → PathOrZero V
  | some ⟨a, b, p⟩, some ⟨c, d, q⟩ =>
      if h : b = c then some ⟨a, d, p.comp (h ▸ q)⟩ else none
  | _, _ => none
-- @endregion

-- @region path_algebras.pmul_assoc
-- @provenance independent
/-- **The multiplication of paths is associative**, including the cases where some product is
`0`. Human proof: `(p · q) · r` and `p · (q · r)` are both defined exactly when `p` ends where `q`
starts and `q` ends where `r` starts, and then both equal the concatenation `pqr`, by
associativity of concatenation (`Quiver.Path.comp_assoc`). Extended bilinearly, this makes `kQ`
an associative algebra. -/
theorem pmul_assoc (x y z : PathOrZero V) : pmul (pmul x y) z = pmul x (pmul y z) := by
  rcases x with _ | ⟨a, b, p⟩
  · rfl
  rcases y with _ | ⟨c, d, q⟩
  · simp [pmul]
  rcases z with _ | ⟨e, f, r⟩
  · by_cases h : b = c
    · subst h; simp [pmul]
    · simp [pmul, h]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = e
    · subst h2
      simp [pmul, Quiver.Path.comp_assoc]
    · simp [pmul, h2]
  · by_cases h2 : d = e
    · subst h2
      simp [pmul, h1]
    · simp [pmul, h1, h2]
-- @endregion

-- @region path_algebras.idempotents
-- @provenance independent
/-- **The trivial paths `eₐ` are orthogonal idempotents**: `eₐ · eₐ = eₐ` and `eₐ · e_b = 0` for
`a ≠ b`. (For a finite quiver their sum is the identity of `kQ`.) -/
theorem idempotents (a b : V) :
    pmul (some ⟨a, a, Quiver.Path.nil⟩) (some ⟨b, b, Quiver.Path.nil⟩) =
      if a = b then some ⟨a, a, Quiver.Path.nil⟩ else none := by
  by_cases h : a = b
  · subst h; simp [pmul]
  · simp [pmul, h]
-- @endregion

end PathMultiplication

-- @region path_algebras.concat_assoc
-- @provenance library
/-- Concatenation of paths is associative: Mathlib's `Quiver.Path.comp_assoc`. (Mathlib's
`p.comp q` is "first `p`, then `q`".) -/
theorem concat_assoc {V : Type u} [Quiver.{v + 1} V] {a b c d : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (r : Quiver.Path c d) : (p.comp q).comp r = p.comp (q.comp r) :=
  Quiver.Path.comp_assoc p q r
-- @endregion

/-! ### When is `kQ` finite-dimensional? -/

-- @region path_algebras.path_length_le
-- @provenance independent
/-- **Acyclic quivers have bounded paths.** If every arrow strictly increases a height function
`h : V → ℕ`, then every path from `a` to `b` has length at most `h b - h a`. Such a function exists
for every finite quiver without oriented cycles (number the vertices compatibly with the arrows),
so then paths have length less than the number of vertices, and with finitely many arrows there
are only finitely many paths: `kQ` is finite-dimensional. Proof: induction on the path. -/
theorem path_length_le {V : Type u} [Quiver.{v + 1} V] (h : V → ℕ)
    (hh : ∀ {a b : V}, (a ⟶ b) → h a < h b) {a b : V} (p : Quiver.Path a b) :
    h a + p.length ≤ h b := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.length_cons]
    have := hh e
    omega
-- @endregion

-- @region path_algebras.cycle_pow
-- @provenance definition
/-- The powers `cⁿ = c c ⋯ c` of a cycle `c` at a vertex `a`. -/
def cyclePow {V : Type u} [Quiver.{v + 1} V] {a : V} (c : Quiver.Path a a) : ℕ → Quiver.Path a a
  | 0 => Quiver.Path.nil
  | n + 1 => (cyclePow c n).comp c
-- @endregion

-- @region path_algebras.cycle_infinite
-- @provenance independent
/-- **A cycle makes `kQ` infinite-dimensional.** If `c` is an oriented cycle of positive length,
its powers `cⁿ` have lengths `n · length c`, all different, so there are infinitely many paths
from `a` to `a`. With the previous theorem: a finite quiver has finite-dimensional path algebra
exactly when it has no oriented cycles. -/
theorem cycle_infinite {V : Type u} [Quiver.{v + 1} V] {a : V} (c : Quiver.Path a a)
    (hc : 0 < c.length) : Infinite (Quiver.Path a a) := by
  have hlen : ∀ n : ℕ, (cyclePow c n).length = n * c.length := by
    intro n
    induction n with
    | zero => simp [cyclePow]
    | succ n ih => rw [cyclePow, Quiver.Path.length_comp, ih, Nat.succ_mul]
  refine Infinite.of_injective (cyclePow c) fun m n hmn => ?_
  have := congrArg Quiver.Path.length hmn
  rw [hlen, hlen] at this
  exact Nat.eq_of_mul_eq_mul_right hc this
-- @endregion

/-! ### The linearly oriented quiver `Aₙ` -/

-- @region path_algebras.lin_a
-- @provenance definition
/-- The linearly oriented quiver `Aₙ`: vertices `0, 1, …, n-1` and one arrow `i → i+1`. -/
def LinA (n : ℕ) : Type := Fin n
-- @endregion

-- @region path_algebras.lin_a_quiver
-- @provenance definition
/-- The arrows of `Aₙ`: there is an arrow from `i` to `j` exactly when `j = i + 1`. -/
instance linAQuiver (n : ℕ) : Quiver (LinA n) where
  Hom i j := PLift ((j : Fin n).val = (i : Fin n).val + 1)
-- @endregion

-- @region path_algebras.lin_a_length
-- @provenance independent
/-- **Paths in `Aₙ`.** Every path from `i` to `j` in the linearly oriented quiver has length
exactly `j - i`; in particular paths `i → j` exist only for `i ≤ j`. (There is in fact exactly
one for each `i ≤ j`, so `kAₙ` has dimension `n(n+1)/2` and is isomorphic to the algebra of upper
triangular `n × n` matrices.) Proof: induction on the path, each arrow adding `1`. -/
theorem lin_a_length {n : ℕ} {i j : LinA n} (p : Quiver.Path i j) :
    (i : Fin n).val + p.length = (j : Fin n).val := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.length_cons]
    have := e.down
    omega
-- @endregion

/-! ### Representations are functors out of the free category -/

-- @region path_algebras.rep_extends
-- @provenance library
/-- **Representations of `Q` are functors out of the path category.** A representation — a
prefunctor `ρ : Q ⥤q ModuleCat k` — extends to a functor `F` on the free category `Paths Q`
(paths act by composites of the arrow maps), and `F` is the unique functor that restricts to `ρ`
on arrows. Mathlib: `Paths.lift`, `Paths.lift_spec`, `Paths.lift_unique`. Linearising, a functor
`Paths Q ⥤ ModuleCat k` is the same as a `kQ`-module — the equivalence proved in the lesson. -/
theorem rep_extends {Q : Type u} [Quiver.{w} Q] {k : Type v} [Field k]
    (ρ : Q ⥤q ModuleCat.{v} k) :
    ∃ F : Paths Q ⥤ ModuleCat.{v} k, Paths.of Q ⋙q F.toPrefunctor = ρ ∧
      ∀ G : Paths Q ⥤ ModuleCat.{v} k, Paths.of Q ⋙q G.toPrefunctor = ρ → G = F :=
  ⟨Paths.lift ρ, Paths.lift_spec ρ, fun G hG => Paths.lift_unique ρ G hG⟩
-- @endregion

end Lumenary.PathAlgebras
