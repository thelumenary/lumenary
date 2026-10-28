/-
The Lumenary — formal mathematics
Collections: lists as collections ("for grown-ups" companion to the K–2 lesson on collections).

A *list* is an ordered collection: it remembers the order of its members and how often each
appears. That makes it different from a *set* (see `Lumenary/Sets.lean`), which only cares
about which things are members. The facts below make that difference precise.

Core Lean 4 only. Mathlib analogue: Mathlib also uses core's `List`; its `Finset` and
`Multiset` are the order-free versions.
-/

namespace Lumenary.Collections

-- @region collections.basket
-- @provenance definition
/-- A basket of fruit, written as a list. Lists keep their members in order. -/
def basket : List String := ["mango", "orange", "banana"]
-- @endregion

-- @region collections.mango_in_basket
-- @provenance independent
/-- There is a mango in the basket: it is the very first thing in the list. -/
theorem mango_in_basket : "mango" ∈ basket :=
  List.Mem.head ["orange", "banana"]
-- @endregion

-- @region collections.basket_count
-- @provenance independent
/-- The basket holds three pieces of fruit. Lean counts them itself, so `rfl` is enough. -/
theorem basket_count : basket.length = 3 := rfl
-- @endregion

-- @region collections.order_matters_for_lists
-- @provenance independent
/-- For lists, order matters: `[1, 2]` and `[2, 1]` are different lists.
`decide` asks Lean to compare the two lists element by element. -/
theorem order_matters_for_lists : ([1, 2] : List Nat) ≠ [2, 1] := by decide
-- @endregion

-- @region collections.same_members
-- @provenance independent
/-- …but `[1, 2]` and `[2, 1]` have exactly the same members. As *sets* they would be equal;
as *lists* they are not (see `order_matters_for_lists`). -/
theorem same_members : ∀ x : Nat, x ∈ [1, 2] ↔ x ∈ [2, 1] := by
  intro x
  -- Being in a list means being equal to one of its entries:
  -- `x ∈ [1, 2]` unfolds to `x = 1 ∨ x = 2`, and `x ∈ [2, 1]` to `x = 2 ∨ x = 1`.
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  -- "or" does not care about order.
  exact Or.comm
-- @endregion

-- @region collections.nothing_in_empty
-- @provenance independent
/-- The empty list has no members at all. -/
theorem nothing_in_empty : ∀ x : String, x ∉ ([] : List String) := by
  intro x h
  -- A proof of `x ∈ []` would have to come from one of the ways of building membership,
  -- but none of them produces an empty list, so there is no case left to consider.
  cases h
-- @endregion

end Lumenary.Collections
