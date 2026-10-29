/-
The Lumenary — formal mathematics
Functions and their graphs (precalculus): graphs as sets of points, transformations
y = a f(b(x − h)) + k, inverse functions and their graphs, monotonicity, even and odd functions,
and the end behaviour of a rational function.

Proved here (`@provenance independent`): the graph of `x ↦ f(x − h)` is the graph of `f` moved
`h` to the right, and more generally the transformation rule for `y = a f(b(x − h)) + k`; the
graph of an inverse function is the mirror image of the graph in the line `y = x`; a strictly
increasing function is injective and its inverse is strictly increasing; every function on `ℝ`
splits uniquely into an even and an odd part; composition of real functions is not commutative;
the rational function `(2x + 1)/(x − 3)` and its inverse; and its horizontal asymptote `y = 2`.

From Mathlib (`@provenance library`): a function has a two-sided inverse exactly when it is a
bijection (`Function.bijective_iff_has_inverse`), the strictly monotone case
(`StrictMonoOn.injOn`), and "odd times odd is even" (`Function.Odd.mul_odd`). Mathlib's
`Function.Even f` means `∀ x, f (-x) = f x` and `Function.Odd f` means `∀ x, f (-x) = -f x`.
-/
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Lumenary.FunctionsAndGraphs

open Filter Topology

/-! ### Graphs and transformations -/

-- @region functions_and_graphs.graph
-- @provenance definition
/-- The **graph** of `f : ℝ → ℝ` is the set of points `(x, f x)` in the plane. -/
def graph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p.2 = f p.1}
-- @endregion

-- @region functions_and_graphs.graph_shift
-- @provenance independent
/-- **Shifting right.** The graph of `y = f(x − h)` is the graph of `y = f(x)` moved `h` units to
the **right**: it is the image of `graph f` under `(x, y) ↦ (x + h, y)`. (For `h > 0`, the input
`x − h` reaches the value `x₀` later, at `x = x₀ + h`.) -/
theorem graph_shift (f : ℝ → ℝ) (h : ℝ) :
    graph (fun x => f (x - h)) = (fun p : ℝ × ℝ => (p.1 + h, p.2)) '' graph f := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · intro hy
    exact ⟨x - h, y, hy, by ring, rfl⟩
  · rintro ⟨u, v, hv, rfl, rfl⟩
    simp [hv]
-- @endregion

-- @region functions_and_graphs.graph_transform
-- @provenance independent
/-- **The transformation rule.** For `b ≠ 0`, the graph of `y = a f(b(x − h)) + k` is the image
of the graph of `f` under `(x, y) ↦ (x/b + h, a y + k)`: squeeze horizontally by the factor `b`,
shift right by `h`, stretch vertically by `a`, shift up by `k`. -/
theorem graph_transform (f : ℝ → ℝ) (a b h k : ℝ) (hb : b ≠ 0) :
    graph (fun x => a * f (b * (x - h)) + k) =
      (fun p : ℝ × ℝ => (p.1 / b + h, a * p.2 + k)) '' graph f := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · intro hy
    refine ⟨b * (x - h), f (b * (x - h)), rfl, ?_, hy.symm⟩
    field_simp
    ring
  · rintro ⟨u, v, hv, rfl, rfl⟩
    have hu : b * (u / b + h - h) = u := by field_simp; ring
    rw [hu, hv]
-- @endregion

/-! ### Inverse functions -/

-- @region functions_and_graphs.graph_inverse
-- @provenance independent
/-- **The graph of an inverse is a reflection.** If `g` undoes `f` and `f` undoes `g`, then the
graph of `g` is the graph of `f` with the coordinates swapped, that is, reflected in the line
`y = x`: `(x, y)` lies on the graph of `f` exactly when `(y, x)` lies on the graph of `g`. -/
theorem graph_inverse (f g : ℝ → ℝ) (hgf : Function.LeftInverse g f)
    (hfg : Function.RightInverse g f) : graph g = Prod.swap '' graph f := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  constructor
  · intro hy
    exact ⟨y, x, by rw [hy, hfg x], rfl, rfl⟩
  · rintro ⟨u, v, hv, rfl, rfl⟩
    rw [hv, hgf u]
-- @endregion

-- @region functions_and_graphs.bijective_iff_has_inverse
-- @provenance library
/-- **A function has an inverse exactly when it is a bijection.** This applies Mathlib's
`Function.bijective_iff_has_inverse`. -/
theorem bijective_iff_has_inverse (f : ℝ → ℝ) :
    Function.Bijective f ↔ ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse
-- @endregion

-- @region functions_and_graphs.inj_on_of_strict_mono_on
-- @provenance independent
/-- **A strictly increasing function is injective** on any set where it is strictly increasing.
If `x ≠ y`, one of them is smaller, say `x < y`; then `f x < f y`, so `f x ≠ f y`.
(Mathlib: `StrictMonoOn.injOn`.) -/
theorem injOn_of_strictMonoOn {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictMonoOn f s) : Set.InjOn f s := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (ne_of_lt (hf hx hy hlt))
  · exact heq
  · exact absurd hxy (ne_of_gt (hf hy hx hgt))
-- @endregion

-- @region functions_and_graphs.inj_on_library
-- @provenance library
/-- The same fact, as stated in Mathlib: this applies `StrictMonoOn.injOn`. On the interval
`[0, ∞)` the function `x ↦ x²` is strictly increasing, which is why it has an inverse there
(the square root), although it has none on all of `ℝ`. -/
theorem injOn_library {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictMonoOn f s) : Set.InjOn f s :=
  hf.injOn
-- @endregion

-- @region functions_and_graphs.strict_mono_inverse
-- @provenance independent
/-- **The inverse of a strictly increasing function is strictly increasing.** Suppose `y₁ < y₂`
but `g y₁ ≥ g y₂`. Applying the increasing function `f` gives `f (g y₁) ≥ f (g y₂)`, that is,
`y₁ ≥ y₂` — a contradiction. -/
theorem strictMono_inverse {f g : ℝ → ℝ} (hf : StrictMono f) (hfg : Function.RightInverse g f) :
    StrictMono g := by
  intro y₁ y₂ hy
  by_contra hle
  have h : f (g y₂) ≤ f (g y₁) := hf.monotone (not_lt.mp hle)
  rw [hfg y₁, hfg y₂] at h
  exact absurd hy (not_lt.mpr h)
-- @endregion

/-! ### A rational function and its inverse -/

-- @region functions_and_graphs.mobius_inverse
-- @provenance independent
/-- **An inverse found by algebra.** `f(x) = (2x + 1)/(x − 3)` (for `x ≠ 3`) and
`g(y) = (3y + 1)/(y − 2)` (for `y ≠ 2`) undo each other. To find `g`, solve `y = (2x + 1)/(x − 3)`
for `x`: `y(x − 3) = 2x + 1`, so `x(y − 2) = 3y + 1`. The value `y = 2` is never taken by `f`:
it is the horizontal asymptote. -/
theorem mobius_inverse :
    (∀ x : ℝ, x ≠ 3 → (2 * x + 1) / (x - 3) ≠ 2 ∧
        (3 * ((2 * x + 1) / (x - 3)) + 1) / ((2 * x + 1) / (x - 3) - 2) = x) ∧
      (∀ y : ℝ, y ≠ 2 → (3 * y + 1) / (y - 2) ≠ 3 ∧
        (2 * ((3 * y + 1) / (y - 2)) + 1) / ((3 * y + 1) / (y - 2) - 3) = y) := by
  constructor
  · intro x hx
    have hx3 : x - 3 ≠ 0 := sub_ne_zero.mpr hx
    have hne : (2 * x + 1) / (x - 3) - 2 ≠ 0 := by
      rw [div_sub' hx3]
      exact div_ne_zero (by ring_nf; norm_num) hx3
    refine ⟨fun h => hne (by rw [h]; ring), ?_⟩
    rw [div_eq_iff hne]
    field_simp
    ring
  · intro y hy
    have hy2 : y - 2 ≠ 0 := sub_ne_zero.mpr hy
    have hne : (3 * y + 1) / (y - 2) - 3 ≠ 0 := by
      rw [div_sub' hy2]
      exact div_ne_zero (by ring_nf; norm_num) hy2
    refine ⟨fun h => hne (by rw [h]; ring), ?_⟩
    rw [div_eq_iff hne]
    field_simp
    ring
-- @endregion

-- @region functions_and_graphs.horizontal_asymptote
-- @provenance independent
/-- **End behaviour:** `(2x + 1)/(x − 3) → 2` as `x → ∞`, so `y = 2` is a horizontal asymptote.
For `x ≠ 3`, `(2x + 1)/(x − 3) = 2 + 7/(x − 3)`, and `7/(x − 3) → 0` because `x − 3 → ∞`.
(The small library facts used are `tendsto_inv_atTop_zero` and the limit laws.) -/
theorem horizontal_asymptote :
    Tendsto (fun x : ℝ => (2 * x + 1) / (x - 3)) atTop (𝓝 2) := by
  have hden : Tendsto (fun x : ℝ => x - 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hsmall : Tendsto (fun x : ℝ => 7 * (x - 3)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hden).const_mul 7
  have hsum : Tendsto (fun x : ℝ => 2 + 7 * (x - 3)⁻¹) atTop (𝓝 2) := by
    simpa using hsmall.const_add 2
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 3] with x hx
  have hx3 : x - 3 ≠ 0 := by linarith
  field_simp
  ring
-- @endregion

/-! ### Even and odd functions -/

-- @region functions_and_graphs.even_odd_decomposition
-- @provenance independent
/-- **Every function is even plus odd.** For `f : ℝ → ℝ` put
`e(x) = (f(x) + f(−x))/2` and `o(x) = (f(x) − f(−x))/2`. Then `e` is even, `o` is odd and
`f = e + o`. (For `f(x) = eˣ` this gives `cosh` and `sinh`.) -/
theorem even_odd_decomposition (f : ℝ → ℝ) :
    ∃ e o : ℝ → ℝ, Function.Even e ∧ Function.Odd o ∧ ∀ x, f x = e x + o x := by
  refine ⟨fun x => (f x + f (-x)) / 2, fun x => (f x - f (-x)) / 2, ?_, ?_, ?_⟩
  · intro x
    simp only [neg_neg]
    ring
  · intro x
    simp only [neg_neg]
    ring
  · intro x
    ring
-- @endregion

-- @region functions_and_graphs.even_odd_unique
-- @provenance independent
/-- **The splitting is unique.** If `e₁ + o₁ = e₂ + o₂` with `e₁, e₂` even and `o₁, o₂` odd, then
`d = e₁ − e₂ = o₂ − o₁` is both even and odd, so `d(x) = d(−x) = −d(x)`, forcing `d(x) = 0`. -/
theorem even_odd_unique {e₁ o₁ e₂ o₂ : ℝ → ℝ} (he₁ : Function.Even e₁) (he₂ : Function.Even e₂)
    (ho₁ : Function.Odd o₁) (ho₂ : Function.Odd o₂) (h : ∀ x, e₁ x + o₁ x = e₂ x + o₂ x) :
    e₁ = e₂ ∧ o₁ = o₂ := by
  have hd : ∀ x, e₁ x - e₂ x = 0 := by
    intro x
    have h1 := h x
    have h2 := h (-x)
    rw [he₁ x, he₂ x, ho₁ x, ho₂ x] at h2
    linarith
  constructor
  · funext x
    linarith [hd x]
  · funext x
    linarith [hd x, h x]
-- @endregion

-- @region functions_and_graphs.odd_mul_odd
-- @provenance library
/-- **Odd times odd is even** — like `(−1)·(−1) = 1`. For example `x · x³ = x⁴`. This applies
Mathlib's `Function.Odd.mul_odd`. -/
theorem odd_mul_odd {f g : ℝ → ℝ} (hf : Function.Odd f) (hg : Function.Odd g) :
    Function.Even (f * g) :=
  hf.mul_odd hg
-- @endregion

/-! ### Composition is not commutative -/

-- @region functions_and_graphs.comp_not_comm
-- @provenance independent
/-- **Order matters:** with `f(x) = x + 1` and `g(x) = x²`, `g ∘ f ≠ f ∘ g`, because
`(g ∘ f)(1) = 4` but `(f ∘ g)(1) = 2`. -/
theorem comp_not_comm :
    (fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => x + 1) ≠ (fun x : ℝ => x + 1) ∘ (fun x : ℝ => x ^ 2) := by
  intro h
  have h1 := congrFun h 1
  norm_num at h1
-- @endregion

end Lumenary.FunctionsAndGraphs
