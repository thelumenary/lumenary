"""Predicting patterns: remainders, growing rules, and patterns that fool us.

A repeating pattern such as red, blue, green, red, blue, green, ... is
decided by its unit. To find the 100th bead we need not draw 100 beads: the
remainder when 100 is divided by 3 tells us. We check this shortcut against
drawing every bead, find the length of the repeating unit, compare two
descriptions of the growing pattern 2, 4, 6, 8, ..., and finally show three
different rules that all begin 1, 2, 4 but then go their own ways - one of
them (regions of a circle) looks like doubling for five items and then
breaks the pattern.

The checks are exact and cover the first 1,000 positions (or 50 steps).
The circle-region counts come from a formula proved in combinatorics; this
program only evaluates it.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from math import comb
import textwrap

EXPERIMENT = {
    "id": "patterns_predict",
    "title": "Predicting patterns, and patterns that fool us",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["patterns"],
    "summary": (
        "Predicts items of a repeating pattern from remainders and checks the "
        "shortcut against listing every item for 1,000 positions, finds the "
        "length of the repeating unit, compares 'add 2 each time' with '2 times "
        "the step', and shows three rules that all start 1, 2, 4 but continue "
        "differently, including circle regions (1, 2, 4, 8, 16, 31)."
    ),
    "packages": [],
}

UNIT = ("red", "blue", "green")


def item(unit, n):
    """Item n (counting from 1) of the pattern that repeats ``unit``."""
    if n < 1:
        raise ValueError("positions start at 1")
    return unit[(n - 1) % len(unit)]


def draw(unit, count):
    """List the first ``count`` items by repeating the unit again and again."""
    items = []
    while len(items) < count:
        items.extend(unit)
    return items[:count]


def smallest_unit_length(items):
    """Smallest k such that every item equals the item k places further on."""
    for k in range(1, len(items) + 1):
        if all(items[i] == items[i + k] for i in range(len(items) - k)):
            return k
    return len(items)


def add_two(steps):
    """The growing pattern 'start at 2 and add 2 each time', as a list."""
    values, value = [], 0
    for _ in range(steps):
        value += 2
        values.append(value)
    return values


def doubling(n):
    """1, 2, 4, 8, ...: each item is double the one before."""
    return 2 ** (n - 1)


def add_more(n):
    """1, 2, 4, 7, 11, ...: add 1, then 2, then 3, and so on."""
    return 1 + (n - 1) * n // 2


def circle_regions(n):
    """Most regions a circle is cut into by joining n points on it.

    The formula C(n, 4) + C(n, 2) + 1 is a theorem of combinatorics
    (Moser's circle problem); here it is only evaluated.
    """
    return comb(n, 4) + comb(n, 2) + 1


def main():
    first = draw(UNIT, 12)
    print("Repeating pattern, unit red-blue-green:")
    print("  " + " ".join(colour[0].upper() for colour in first) + " ...")
    q, r = divmod(100, len(UNIT))
    print(f"  item 100: 100 = 3 x {q} + {r}, so it matches item "
          f"{r or len(UNIT)}: {item(UNIT, 100)}")
    drawn = draw(UNIT, 1000)
    agree = sum(item(UNIT, n) == drawn[n - 1] for n in range(1, 1001))
    print(f"  remainder shortcut agrees with drawing every bead: "
          f"{agree} of 1000")
    same = sum(item(UNIT, n + 3) == item(UNIT, n) for n in range(1, 1001))
    print(f"  item n + 3 equals item n for {same} of 1000 positions")
    print(f"  smallest repeating unit: {smallest_unit_length(drawn[:60])} "
          "items (not 1)")
    print()
    steps = add_two(50)
    match = sum(v == 2 * n for n, v in enumerate(steps, start=1))
    print("Growing pattern 2, 4, 6, 8, ...:")
    print(f"  'add 2 each time' equals '2 x step' for {match} of 50 steps")
    print()
    print("Three rules that all start 1, 2, 4:")
    rules = [("doubling", doubling), ("add 1, 2, 3, ...", add_more),
             ("circle regions", circle_regions)]
    for name, rule in rules:
        values = ", ".join(str(rule(n)) for n in range(1, 8))
        print(f"  {name:<17} {values}, ...")
    print("  Circle regions look like doubling for five items, then: 31!")
    print()
    print(textwrap.fill(
        "Epistemic status: exact checks of the first 1,000 positions and 50 "
        "steps, which is evidence, not a proof, for later positions (the "
        "lesson gives the proof). The three rules are a counterexample to "
        "'the first few items decide a pattern'; the circle-region numbers "
        "come from a known formula that this program evaluates but does not "
        "prove.",
        width=78,
    ))


if __name__ == "__main__":
    main()
