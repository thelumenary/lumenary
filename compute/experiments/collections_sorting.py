"""Sorting and counting a market basket.

A *collection* here is a basket of items. Two mangoes are two different items
that happen to share a name, so the basket is a list (order and repeats are
recorded), not a set. We sort the basket by a property, count each group, and
check that the counts do not depend on the order in which the items were
picked.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from collections import Counter
from itertools import permutations
from math import factorial
import textwrap

EXPERIMENT = {
    "id": "collections_sorting",
    "title": "Sorting and counting a market basket",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["collections"],
    "summary": (
        "Sorts a fixed basket of market items by kind and by colour and counts "
        "each group exactly, then checks every one of the 720 orders of a "
        "6-item basket gives the same counts. This proves order-independence "
        "for that basket only; why it holds for every finite collection is "
        "explained in the lesson, not by this program."
    ),
    "packages": [],
}

#: The basket, in the order the items were picked. Each item is
#: (name, kind, colour). Repeated names are separate items.
BASKET = (
    ("mango", "fruit", "yellow"),
    ("okra", "vegetable", "green"),
    ("banana", "fruit", "yellow"),
    ("lime", "fruit", "green"),
    ("carrot", "vegetable", "orange"),
    ("mango", "fruit", "yellow"),
    ("aubergine", "vegetable", "purple"),
    ("orange", "fruit", "orange"),
    ("lime", "fruit", "green"),
    ("yam", "vegetable", "brown"),
)

#: Positions of each property inside an item tuple.
PROPERTIES = {"name": 0, "kind": 1, "colour": 2}


def value(item, prop):
    """Return the value of property ``prop`` ("name", "kind" or "colour") of an item."""
    try:
        return item[PROPERTIES[prop]]
    except KeyError:
        raise ValueError(f"unknown property {prop!r}; expected one of {sorted(PROPERTIES)}") from None


def sort_by(items, *props):
    """Return a new list of the items sorted by the given properties, in priority order.

    The original collection is not changed. With no properties, items are sorted
    by (name, kind, colour) as plain tuples.
    """
    if not props:
        return sorted(items)
    return sorted(items, key=lambda item: tuple(value(item, p) for p in props))


def group_by(items, prop):
    """Group items by a property: return {value: [items with that value]} with keys sorted."""
    groups = {}
    for item in items:
        groups.setdefault(value(item, prop), []).append(item)
    return {key: groups[key] for key in sorted(groups)}


def count_by(items, prop):
    """Count how many items have each value of ``prop``: {value: count}, keys sorted."""
    counts = Counter(value(item, prop) for item in items)
    return {key: counts[key] for key in sorted(counts)}


def distinct_values(items, prop):
    """Return the set of different values of ``prop`` that occur in the collection."""
    return {value(item, prop) for item in items}


def counts_same_in_every_order(items, prop):
    """Check every ordering of ``items``: do the group counts by ``prop`` ever change?

    Returns ``(orders_checked, all_same)``. The number of orders is n!, so this
    is only practical for small collections (n <= 8 or so).
    """
    items = list(items)
    reference = count_by(items, prop)
    checked = 0
    for order in permutations(items):
        checked += 1
        if count_by(order, prop) != reference:
            return checked, False
    return checked, True


def format_counts(counts):
    """Format {value: count} as 'a 2, b 3' with the total in brackets."""
    parts = ", ".join(f"{key} {n}" for key, n in counts.items())
    return f"{parts}   (total {sum(counts.values())})"


def main():
    basket = list(BASKET)
    print(f"A market basket of {len(basket)} items, in the order they were picked:")
    print("  " + ", ".join(value(item, "name") for item in basket))
    print()
    print("Sorted by kind, then colour, then name:")
    print(f"  {'kind':<10} {'colour':<8} name")
    for item in sort_by(basket, "kind", "colour", "name"):
        print(f"  {value(item, 'kind'):<10} {value(item, 'colour'):<8} {value(item, 'name')}")
    print()
    by_kind = count_by(basket, "kind")
    by_colour = count_by(basket, "colour")
    print("Counts by kind:   " + format_counts(by_kind))
    print("Counts by colour: " + format_counts(by_colour))
    sums = " + ".join(str(n) for n in by_kind.values())
    print(f"Every item lands in exactly one group, so the groups add up: {sums} = {len(basket)}.")
    names = distinct_values(basket, "name")
    print(f"Different names: {len(names)} (two mangoes are two items with one name).")
    print()
    small = basket[:6]
    n_orders = factorial(len(small))
    print(f"Does order matter? Take the first {len(small)} items and try all {len(small)}! = {n_orders} orders:")
    for prop in ("kind", "colour"):
        checked, same = counts_same_in_every_order(small, prop)
        print(f"  counts by {prop:<6} identical in all {checked} orders: {same}")
    print()
    print(textwrap.fill(
        "Epistemic status: the counts above are exact, and all "
        f"{n_orders} orders of the 6-item basket were checked, which proves "
        "order-independence for that basket only. Why it holds for every finite "
        "collection (counting pairs items with 1, 2, 3, ...) is explained in the "
        "lesson, not by this program.",
        width=78,
    ))


if __name__ == "__main__":
    main()
