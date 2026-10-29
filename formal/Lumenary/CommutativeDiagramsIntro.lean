/-
The Lumenary — formal mathematics
Diagrams where paths agree: commuting squares and triangles of functions.

A square of functions

    A --top--> B
    |          |
   left      right
    v          v
    C --bottom-> D

*commutes* when both routes from `A` to `D` give the same output for every input:
`right (top a) = bottom (left a)` for all `a`. Here this is a definition about plain functions
between types; category theory uses the same idea for arrows in any category.

What is formalised: commuting and non-commuting squares and triangles; that agreeing at a few
inputs is not enough; "preserving addition" as a commuting square; that `x ↦ 100x` preserves
addition but `x ↦ x + 1` does not, and exactly which `x ↦ mx + c` do; that every
addition-preserving function `ℤ → ℤ` is multiplication by a fixed number; remainders and
weekdays; and pasting two commuting squares into a commuting rectangle (but not conversely).
Core Lean only.
-/

namespace Lumenary.CommutativeDiagramsIntro

/-! ### Squares and triangles -/

-- @region commutative_diagrams_intro.square_commutes
-- @provenance definition
/-- The square with `top : A → B`, `right : B → D`, `left : A → C` and `bottom : C → D`
**commutes** when the two routes from `A` to `D` agree for every input: going along the top and
then down the right gives the same as going down the left and then along the bottom. -/
def SquareCommutes {A B C D : Type} (top : A → B) (right : B → D) (left : A → C)
    (bottom : C → D) : Prop :=
  ∀ a, right (top a) = bottom (left a)
-- @endregion

-- @region commutative_diagrams_intro.triangle_commutes
-- @provenance definition
/-- The triangle with `f : A → B`, `g : B → C` and `h : A → C` **commutes** when the two-step
route equals the direct route: `g (f a) = h a` for every `a`. -/
def TriangleCommutes {A B C : Type} (f : A → B) (g : B → C) (h : A → C) : Prop :=
  ∀ a, g (f a) = h a
-- @endregion

-- @region commutative_diagrams_intro.double_add_square
-- @provenance independent
/-- "Double, then add 2" equals "add 1, then double": `2x + 2 = 2(x + 1)` for every integer. -/
theorem double_add_square :
    SquareCommutes (fun x : Int => 2 * x) (fun x => x + 2) (fun x => x + 1) (fun x => 2 * x) := by
  intro a
  show 2 * a + 2 = 2 * (a + 1)
  omega
-- @endregion

-- @region commutative_diagrams_intro.add_double_not_square
-- @provenance independent
/-- "Add 1, then double" is **not** "double, then add 1": at `0` the routes give `2` and `1`.
One input where the routes disagree is enough to show a square does not commute. -/
theorem add_double_not_square :
    ¬ SquareCommutes (fun x : Int => x + 1) (fun x => 2 * x) (fun x => 2 * x) (fun x => x + 1) := by
  intro h
  have h0 := h 0
  revert h0
  decide
-- @endregion

-- @region commutative_diagrams_intro.agree_twice_not_square
-- @provenance independent
/-- Agreeing at some inputs is not enough. The routes "square" and "double" agree at `0` and at
`2` (`0² = 2·0` and `2² = 2·2`), but the square does not commute: at `1` they give `1` and `2`. -/
theorem agree_twice_not_square :
    (0 * 0 = 2 * 0 ∧ 2 * 2 = 2 * (2 : Int)) ∧
      ¬ SquareCommutes (fun x : Int => x * x) id id (fun x => 2 * x) := by
  refine ⟨by decide, ?_⟩
  intro h
  have h1 := h 1
  revert h1
  decide
-- @endregion

-- @region commutative_diagrams_intro.hours_triangle
-- @provenance independent
/-- Hours to minutes (`× 60`), then minutes to seconds (`× 60`), is hours to seconds (`× 3600`). -/
theorem hours_triangle :
    TriangleCommutes (fun h : Nat => 60 * h) (fun m => 60 * m) (fun h => 3600 * h) := by
  intro h
  show 60 * (60 * h) = 3600 * h
  omega
-- @endregion

/-! ### Preserving addition -/

-- @region commutative_diagrams_intro.preserves_add
-- @provenance definition
/-- `f` **preserves addition** if `f (a + b) = f a + f b` for all `a` and `b`. -/
def PreservesAdd (f : Int → Int) : Prop := ∀ a b, f (a + b) = f a + f b
-- @endregion

-- @region commutative_diagrams_intro.preserves_add_iff_square
-- @provenance independent
/-- Preserving addition **is** a commuting square. Its corners hold pairs of numbers on the left
and single numbers on the right: along the top, add the pair, then apply `f`; down the left,
apply `f` to both numbers, then add. -/
theorem preserves_add_iff_square (f : Int → Int) :
    PreservesAdd f ↔
      SquareCommutes (fun p : Int × Int => p.1 + p.2) f (fun p => (f p.1, f p.2))
        (fun p => p.1 + p.2) := by
  constructor
  · intro h p
    exact h p.1 p.2
  · intro h a b
    exact h (a, b)
-- @endregion

-- @region commutative_diagrams_intro.cm_preserves_add
-- @provenance library
/-- Converting metres to centimetres, `x ↦ 100x`, preserves addition: `100(a + b) = 100a + 100b`.
This is the distributive law, core Lean's `Int.mul_add`. -/
theorem cm_preserves_add : PreservesAdd (fun x => 100 * x) :=
  fun a b => Int.mul_add 100 a b
-- @endregion

-- @region commutative_diagrams_intro.add_one_not_preserves
-- @provenance independent
/-- `x ↦ x + 1` does **not** preserve addition: with `a = b = 0`, the routes give
`(0 + 0) + 1 = 1` and `(0 + 1) + (0 + 1) = 2`. -/
theorem add_one_not_preserves : ¬ PreservesAdd (fun x => x + 1) := by
  intro h
  have h00 := h 0 0
  revert h00
  decide
-- @endregion

-- @region commutative_diagrams_intro.affine_preserves_add_iff
-- @provenance independent
/-- Exactly which functions `x ↦ mx + c` preserve addition? Those with `c = 0`.
The two routes give `m(a + b) + c` and `(ma + c) + (mb + c)`, which differ by `c`. -/
theorem affine_preserves_add_iff (m c : Int) : PreservesAdd (fun x => m * x + c) ↔ c = 0 := by
  constructor
  · intro h
    have h00 : m * (0 + 0) + c = (m * 0 + c) + (m * 0 + c) := h 0 0
    rw [Int.zero_add, Int.mul_zero, Int.zero_add] at h00
    omega
  · intro hc a b
    show m * (a + b) + c = (m * a + c) + (m * b + c)
    rw [hc, Int.mul_add, Int.add_zero, Int.add_zero, Int.add_zero]
-- @endregion

-- @region commutative_diagrams_intro.square_not_preserves
-- @provenance independent
/-- Squaring does not preserve addition: `(1 + 1)² = 4`, but `1² + 1² = 2`. -/
theorem square_not_preserves : ¬ PreservesAdd (fun x => x * x) := by
  intro h
  have h11 := h 1 1
  revert h11
  decide
-- @endregion

-- @region commutative_diagrams_intro.cm_not_preserves_mul
-- @provenance independent
/-- `x ↦ 100x` preserves addition but **not** multiplication: `100 · (1 · 1) = 100`, while
`(100 · 1) · (100 · 1) = 10000`. This is why `1 m² = 10 000 cm²`, not `100 cm²`. -/
theorem cm_not_preserves_mul : ¬ ∀ a b : Int, 100 * (a * b) = (100 * a) * (100 * b) := by
  intro h
  have h11 := h 1 1
  revert h11
  decide
-- @endregion

-- @region commutative_diagrams_intro.preserves_add_is_mul
-- @provenance independent
/-- **Every addition-preserving function `ℤ → ℤ` is multiplication by a fixed number**, namely
by `f 1`. Steps: `f 0 = 0` (from `f (0 + 0) = f 0 + f 0`); `f (n + 1) = f n + f 1`, so by induction
`f n = f 1 · n` for every natural number `n`; and `f (−x) = −f x` (because
`f x + f (−x) = f 0 = 0`), which handles the negative numbers. -/
theorem preserves_add_is_mul (f : Int → Int) (h : PreservesAdd f) : ∀ x, f x = f 1 * x := by
  have h0 : f 0 = 0 := by
    have e := h 0 0
    rw [Int.add_zero] at e
    omega
  have hnat : ∀ n : Nat, f n = f 1 * n := by
    intro n
    induction n with
    | zero =>
      show f 0 = f 1 * 0
      rw [h0, Int.mul_zero]
    | succ k ih =>
      have hk : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hk, h, ih, Int.mul_add, Int.mul_one]
  have hneg : ∀ x, f (-x) = -f x := by
    intro x
    have e := h x (-x)
    rw [Int.add_right_neg, h0] at e
    omega
  intro x
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg x
  · rw [hn, hnat]
  · rw [hn, hneg, hnat, Int.mul_neg]
-- @endregion

/-! ### Remainders and weekdays -/

-- @region commutative_diagrams_intro.remainder_preserves_add
-- @provenance library
/-- Taking remainders on division by `7` turns `+` into "add, then take the remainder":
`(a + b) % 7 = (a % 7 + b % 7) % 7`. This applies core Lean's `Nat.add_mod`. -/
theorem remainder_preserves_add (a b : Nat) : (a + b) % 7 = (a % 7 + b % 7) % 7 :=
  Nat.add_mod a b 7
-- @endregion

-- @region commutative_diagrams_intro.weekday_square
-- @provenance independent
/-- **What day is it in 100 days?** Number the days, and let a day's remainder on division by `7`
be its weekday. The square "add 100 days, then take the weekday" = "take the weekday, then move
on 2 weekdays" commutes, because `100 = 14 · 7 + 2`. -/
theorem weekday_square :
    SquareCommutes (fun n : Nat => n + 100) (fun n => n % 7) (fun n => n % 7)
      (fun r => (r + 2) % 7) := by
  intro n
  show (n + 100) % 7 = (n % 7 + 2) % 7
  omega
-- @endregion

-- @region commutative_diagrams_intro.pow_turns_add_into_mul
-- @provenance library
/-- A square that turns addition into multiplication: `2^(a + b) = 2^a · 2^b`. This applies core
Lean's `Nat.pow_add`. -/
theorem pow_turns_add_into_mul (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b :=
  Nat.pow_add 2 a b
-- @endregion

/-! ### Pasting squares -/

-- @region commutative_diagrams_intro.paste
-- @provenance independent
/-- **Pasting.** Put two commuting squares side by side, sharing the middle arrow `b`:

    A --f--> B --g--> C
    |a       |b       |c
    v        v        v
    D --f'-> E --g'-> F

If the left square (`b (f x) = f' (a x)`) and the right square (`c (g y) = g' (b y)`) commute,
then so does the outer rectangle: `c (g (f x)) = g' (b (f x)) = g' (f' (a x))`. -/
theorem paste {A B C D E F : Type} {f : A → B} {g : B → C} {f' : D → E} {g' : E → F}
    {a : A → D} {b : B → E} {c : C → F}
    (hleft : SquareCommutes f b a f') (hright : SquareCommutes g c b g') :
    SquareCommutes (fun x => g (f x)) c a (fun x => g' (f' x)) := by
  intro x
  calc c (g (f x)) = g' (b (f x)) := hright (f x)
    _ = g' (f' (a x)) := by rw [hleft x]
-- @endregion

-- @region commutative_diagrams_intro.paste_converse_false
-- @provenance independent
/-- The converse fails: the outer rectangle can commute although the left square does not.
Take every map to be the identity, except `b = (· + 1)` and `c = g' = 0` (constant). The outer
routes both give `0`, but the left square needs `x + 1 = x`. -/
theorem paste_converse_false :
    ∃ f g f' g' a b c : Int → Int,
      SquareCommutes (fun x => g (f x)) c a (fun x => g' (f' x)) ∧ ¬ SquareCommutes f b a f' := by
  refine ⟨id, id, id, fun _ => 0, id, fun x => x + 1, fun _ => 0, ?_, ?_⟩
  · intro x
    rfl
  · intro h
    have h0 := h 0
    revert h0
    decide
-- @endregion

end Lumenary.CommutativeDiagramsIntro
