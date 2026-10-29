/-
The Lumenary — formal mathematics
Ordinals and cardinals: rigidity of well-orders, transfinite induction, ordinal arithmetic,
Cantor's theorem, the Schröder–Bernstein theorem and the first facts of cardinal arithmetic.

Proved here (`@provenance independent`): a strictly increasing self-map of a well-order never
moves a point down; hence two well-orders are isomorphic in at most one way and no well-order
embeds into a proper initial segment of itself (the uniqueness half of "every well-order is
isomorphic to exactly one ordinal"); transfinite induction in its zero / successor / limit form;
`1 + ω ≠ ω + 1` and `2 · ω ≠ ω · 2`; `ω + 1` is countable; Cantor's theorem; and the
Schröder–Bernstein theorem by the Knaster–Tarski fixed-point argument of the lesson.

From Mathlib (`@provenance library`): `Ordinal.toZFSetIso` (ordinals in Mathlib's sense —
isomorphism types of well-orders — correspond exactly to von Neumann ordinals in its model of
ZFC), `Ordinal.one_add_omega0`, `Cardinal.cantor`, `Function.Embedding.schroeder_bernstein`, and
Hessenberg's theorem `Cardinal.mul_eq_self` (`κ · κ = κ` for infinite `κ`).

Note: Mathlib *defines* `Ordinal` as the type of well-orders up to isomorphism, and `Cardinal` as
types up to bijection. Lean's logic includes a choice principle, so Mathlib's cardinals are
totally ordered; the ZF subtleties of the lesson are not visible at this level.
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Order.FixedPoints

namespace Lumenary.Cardinals

universe u v

open Ordinal Cardinal

/-! ### Well-orders are rigid -/

-- @region cardinals.le_apply_of_strict_mono
-- @provenance independent
/-- **In a well-order, a strictly increasing map never moves a point down:** `x ≤ f x`.
If not, take the *least* `m` with `f m < m`. Since `f` is strictly increasing, `f (f m) < f m`,
so `f m` is an even smaller counterexample — a contradiction.
(Mathlib: `StrictMono.le_apply`.) -/
theorem le_apply_of_strictMono {α : Type u} [LinearOrder α] [WellFoundedLT α] {f : α → α}
    (hf : StrictMono f) (x : α) : x ≤ f x := by
  by_contra hx
  have hne : ({y | f y < y} : Set α).Nonempty := ⟨x, lt_of_not_ge hx⟩
  obtain ⟨m, hm, hmin⟩ := WellFounded.has_min wellFounded_lt {y | f y < y} hne
  exact hmin (f m) (hf hm) hm
-- @endregion

-- @region cardinals.order_iso_unique
-- @provenance independent
/-- **Two well-orders are isomorphic in at most one way.** If `f, g : α ≃o β`, then
`f⁻¹ ∘ g` and `g⁻¹ ∘ f` are strictly increasing self-maps of `α`, so
`x ≤ f⁻¹ (g x)` and `x ≤ g⁻¹ (f x)`; applying `f` and `g` gives `f x ≤ g x ≤ f x`. -/
theorem orderIso_unique {α : Type u} {β : Type v} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] (f g : α ≃o β) : f = g := by
  ext x
  apply le_antisymm
  · have h1 := le_apply_of_strictMono (f := fun y => f.symm (g y))
      (f.symm.strictMono.comp g.strictMono) x
    have h2 := f.monotone h1
    simpa using h2
  · have h1 := le_apply_of_strictMono (f := fun y => g.symm (f y))
      (g.symm.strictMono.comp f.strictMono) x
    have h2 := g.monotone h1
    simpa using h2
-- @endregion

-- @region cardinals.no_embedding_into_initial_segment
-- @provenance independent
/-- **A well-order does not embed into a proper initial segment of itself.** A strictly increasing
`f : α → α` cannot map everything below a point `a`: we would get `f a < a`, contradicting
`le_apply_of_strictMono`. (For instance `ω` is not isomorphic to `{0, 1, …, n - 1}`, and no
ordinal is isomorphic to a smaller one.) -/
theorem no_embedding_into_initial_segment {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (a : α) {f : α → α} (hf : StrictMono f) : ¬ ∀ x, f x < a :=
  fun h => absurd (h a) (not_lt.mpr (le_apply_of_strictMono hf a))
-- @endregion

-- @region cardinals.von_neumann_iso
-- @provenance library
/-- **Every ordinal is represented by exactly one von Neumann ordinal.** Mathlib's ordinals
(isomorphism types of well-orders) are order-isomorphic to the transitive sets well-ordered by
`∈` inside its model of ZFC. This applies `Ordinal.toZFSetIso`. -/
theorem von_neumann_iso : Nonempty (Ordinal.{u} ≃o {x : ZFSet.{u} // x.IsOrdinal}) :=
  ⟨Ordinal.toZFSetIso⟩
-- @endregion

/-! ### Transfinite induction -/

-- @region cardinals.transfinite_induction
-- @provenance independent
/-- **Transfinite induction.** To prove `P o` for every ordinal it suffices to prove `P 0`, to
pass from `P o` to `P (o + 1)`, and to pass from "`P` holds below a limit `o`" to `P o`.
Proof: strong induction along the well-order of the ordinals (`WellFoundedLT.induction`),
then a case split: every ordinal is `0`, a successor or a limit
(`Ordinal.zero_or_succ_or_isSuccLimit`). -/
theorem transfinite_induction (P : Ordinal.{u} → Prop) (h0 : P 0)
    (hsucc : ∀ o, P o → P (Order.succ o))
    (hlim : ∀ o, Order.IsSuccLimit o → (∀ o' < o, P o') → P o) (o : Ordinal.{u}) : P o := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit o with h | ⟨o', rfl⟩ | h
    · rw [h]; exact h0
    · exact hsucc o' (ih o' (Order.lt_succ o'))
    · exact hlim o h ih
-- @endregion

/-! ### Ordinal arithmetic is not commutative -/

-- @region cardinals.one_add_omega
-- @provenance library
/-- **`1 + ω = ω`**: one extra point *in front* of `0, 1, 2, …` is absorbed.
This applies Mathlib's `Ordinal.one_add_omega0`. -/
theorem one_add_omega : (1 : Ordinal.{u}) + ω = ω :=
  Ordinal.one_add_omega0
-- @endregion

-- @region cardinals.add_not_comm
-- @provenance independent
/-- **Ordinal addition is not commutative:** `1 + ω = ω`, but `ω < ω + 1` (an extra point *after*
all the natural numbers is a new largest element), so `1 + ω ≠ ω + 1`. -/
theorem add_not_comm : (1 : Ordinal.{u}) + ω ≠ ω + 1 := by
  rw [one_add_omega]
  exact ne_of_lt (lt_add_one ω)
-- @endregion

-- @region cardinals.mul_not_comm
-- @provenance independent
/-- **Ordinal multiplication is not commutative:** `2 · ω` is `ω` copies of `2`, which is just
`ω` (`Ordinal.natCast_mul_omega0`), while `ω · 2 = ω + ω` (`Ordinal.mul_two`) is two copies of
`ω`, which is larger than `ω`. -/
theorem mul_not_comm : (2 : Ordinal.{u}) * ω ≠ ω * 2 := by
  have h2 : (2 : Ordinal.{u}) * ω = ω := Ordinal.natCast_mul_omega0 (n := 2) two_pos
  rw [h2, Ordinal.mul_two]
  exact ne_of_lt (lt_add_of_pos_right ω Ordinal.omega0_pos)
-- @endregion

-- @region cardinals.card_omega_add_one
-- @provenance independent
/-- **Same size, different shape:** `ω + 1` is a different ordinal from `ω`, but it has the same
cardinality `ℵ₀`: the cardinality of a sum is the sum of the cardinalities
(`Ordinal.card_add`), and `ℵ₀ + 1 = ℵ₀` (`Cardinal.add_one_eq`). -/
theorem card_omega_add_one : (ω + 1 : Ordinal.{u}).card = ℵ₀ := by
  rw [Ordinal.card_add, Ordinal.card_omega0, Ordinal.card_one]
  exact Cardinal.add_one_eq le_rfl
-- @endregion

/-! ### Comparing sizes -/

-- @region cardinals.cantor_no_surjection
-- @provenance independent
/-- **Cantor's theorem**, in its sharpest form: no function `f : α → Set α` is surjective.
The diagonal set `D = {x | x ∉ f x}` differs from every `f a` at the point `a`. -/
theorem cantor_no_surjection {α : Type u} (f : α → Set α) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf {x | x ∉ f x}
  have key : a ∈ f a ↔ a ∉ f a := by
    constructor
    · intro h; rw [ha] at h; exact h
    · intro h; rw [ha]; exact h
  have hnot : a ∉ f a := fun h => key.mp h h
  exact hnot (key.mpr hnot)
-- @endregion

-- @region cardinals.cantor_card
-- @provenance library
/-- **Cantor's theorem for cardinals:** `κ < 2^κ` for every cardinal `κ`.
This applies Mathlib's `Cardinal.cantor`. -/
theorem cantor_card (κ : Cardinal.{u}) : κ < 2 ^ κ :=
  Cardinal.cantor κ
-- @endregion

-- @region cardinals.schroeder_bernstein
-- @provenance independent
/-- **The Schröder–Bernstein theorem**, by the proof in the lesson. Given injections
`f : α → β` and `g : β → α`, the map `F(S) = α \ g[β \ f[S]]` on subsets of `α` is monotone, so
it has a fixed point `S` (Knaster–Tarski: Mathlib's `OrderHom.lfp`). Then `α \ S = g[β \ f[S]]`,
and `h = f` on `S`, `h = g⁻¹` off `S` is a bijection `α → β`. -/
theorem schroeder_bernstein {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h := by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · -- If `β` is empty, so is `α`, and the empty function is a bijection.
    have : IsEmpty α := Function.isEmpty f
    exact ⟨f, fun a => isEmptyElim a, fun b => isEmptyElim b⟩
  -- The monotone operator `F(S) = α \ g[β \ f[S]]`.
  let F : Set α →o Set α :=
    { toFun := fun S => (g '' (f '' S)ᶜ)ᶜ
      monotone' := fun S T hST =>
        Set.compl_subset_compl.mpr
          (Set.image_mono (Set.compl_subset_compl.mpr (Set.image_mono hST))) }
  -- Knaster–Tarski: a fixed point `S = F(S)`.
  set S : Set α := OrderHom.lfp F with hSdef
  have hS : (g '' (f '' S)ᶜ)ᶜ = S := OrderHom.map_lfp F
  -- Off `S`, every point is `g y` for some `y` outside `f[S]`.
  have hSc : g '' (f '' S)ᶜ = Sᶜ := (compl_compl _).symm.trans (congrArg compl hS)
  have off : ∀ a, a ∉ S → ∃ y, y ∉ f '' S ∧ g y = a := by
    intro a ha
    have : a ∈ g '' (f '' S)ᶜ := by rw [hSc]; exact ha
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨y, hy, rfl⟩
  -- `g'` undoes `g`.
  let g' : α → β := Function.invFun g
  have hg' : ∀ y, g' (g y) = y := Function.leftInverse_invFun hg
  let h : α → β := fun a => if a ∈ S then f a else g' a
  refine ⟨h, ?_, ?_⟩
  · -- `h` is injective.
    intro a b hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · simp only [h, ha, hb, ↓reduceIte] at hab
      exact hf hab
    · simp only [h, ha, hb, ↓reduceIte] at hab
      obtain ⟨y, hy, rfl⟩ := off b hb
      rw [hg'] at hab
      exact absurd ⟨a, ha, hab⟩ hy
    · simp only [h, ha, hb, ↓reduceIte] at hab
      obtain ⟨y, hy, rfl⟩ := off a ha
      rw [hg'] at hab
      exact absurd ⟨b, hb, hab.symm⟩ hy
    · simp only [h, ha, hb, ↓reduceIte] at hab
      obtain ⟨y, -, rfl⟩ := off a ha
      obtain ⟨z, -, rfl⟩ := off b hb
      rw [hg', hg'] at hab
      rw [hab]
  · -- `h` is surjective.
    intro y
    by_cases hy : y ∈ f '' S
    · obtain ⟨a, ha, rfl⟩ := hy
      exact ⟨a, by simp only [h, ha, ↓reduceIte]⟩
    · have hgy : g y ∉ S := by
        have : g y ∈ g '' (f '' S)ᶜ := ⟨y, hy, rfl⟩
        rw [hSc] at this
        exact this
      exact ⟨g y, by simp only [h, hgy, ↓reduceIte, hg']⟩
-- @endregion

-- @region cardinals.schroeder_bernstein_library
-- @provenance library
/-- The same theorem from Mathlib: `Function.Embedding.schroeder_bernstein`. (Mathlib's proof
uses the same Knaster–Tarski fixed point.) -/
theorem schroeder_bernstein_library {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein hf hg
-- @endregion

/-! ### Cardinal arithmetic -/

-- @region cardinals.hessenberg
-- @provenance library
/-- **Hessenberg's theorem:** `κ · κ = κ` for every infinite cardinal `κ`.
This applies Mathlib's `Cardinal.mul_eq_self`. -/
theorem hessenberg {κ : Cardinal.{u}} (h : ℵ₀ ≤ κ) : κ * κ = κ :=
  Cardinal.mul_eq_self h
-- @endregion

-- @region cardinals.add_eq_max
-- @provenance independent
/-- **Infinite sums collapse:** if `κ` is infinite then `κ + λ = max κ λ`. Proof from
Hessenberg: with `μ = max κ λ` (infinite), `μ ≤ κ + λ ≤ μ + μ = 2 · μ ≤ μ · μ = μ`. -/
theorem add_eq_max {κ μ : Cardinal.{u}} (h : ℵ₀ ≤ κ) : κ + μ = max κ μ := by
  have hm : ℵ₀ ≤ max κ μ := le_trans h (le_max_left κ μ)
  apply le_antisymm
  · calc κ + μ ≤ max κ μ + max κ μ := add_le_add (le_max_left κ μ) (le_max_right κ μ)
      _ = 2 * max κ μ := (two_mul (max κ μ)).symm
      _ ≤ max κ μ * max κ μ :=
          mul_le_mul_left (le_trans Cardinal.ofNat_le_aleph0 hm) (max κ μ)
      _ = max κ μ := hessenberg hm
  · exact max_le le_self_add le_add_self
-- @endregion

end Lumenary.Cardinals
