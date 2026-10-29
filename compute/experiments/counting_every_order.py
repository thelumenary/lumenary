"""Counting a small herd in every possible order.

Counting pairs each object with exactly one number word: one, two, three, ...
We count a herd of five goats in all 5! = 120 orders and record the last
number word said each time. Then we show what a counting slip (skipping a
goat, or touching one twice) does to the answer, and compare two collections
by pairing them up, without counting at all.

The checks are exact and cover every order of this one herd; they do not
prove anything about other collections. The lesson explains why the last
word is the same for every collection and every order.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from collections import Counter
from itertools import permutations
from math import factorial
import textwrap

EXPERIMENT = {
    "id": "counting_every_order",
    "title": "Counting a herd of goats in every order",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["counting"],
    "summary": (
        "Counts a herd of five goats in all 120 possible orders and records the "
        "last number word said each time (always 'five'), shows how skipping a "
        "goat or touching one twice changes the answer, and compares children "
        "with cups by pairing. Exhaustive for this herd only; why the count "
        "never depends on the order, for any collection, is explained in the "
        "lesson."
    ),
    "packages": [],
}

#: Number words in counting order.
NUMBER_WORDS = (
    "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
    "ten", "eleven", "twelve",
)

#: Five of Nomin's goats.
HERD = ("Snowy", "Patch", "Socks", "Star", "Pebble")

#: Tomás's friends (served first) and Tomás, and the cups on the shelf.
CHILDREN = ("Lina", "Kofi", "Mei", "Arjun", "Tomás")
CUPS = ("red", "blue", "green", "yellow")


def count_aloud(items):
    """Pair each item with a number word, in order: [(word, item), ...]."""
    items = list(items)
    if len(items) > len(NUMBER_WORDS):
        raise ValueError(f"can only count up to {len(NUMBER_WORDS)} items")
    return list(zip(NUMBER_WORDS, items))


def last_word(items):
    """The last number word said when counting ``items`` ("zero" if empty)."""
    pairs = count_aloud(items)
    return pairs[-1][0] if pairs else "zero"


def last_words_in_every_order(items):
    """Count ``items`` in every order; return a Counter of the last words."""
    return Counter(last_word(order) for order in permutations(items))


def touches(items, skip=None, twice=None):
    """The objects touched by a counter who may slip.

    ``skip`` is the position of an item that is missed out, and ``twice`` the
    position of an item that is touched a second time straight away.
    """
    touched = []
    for position, item in enumerate(items):
        if position == skip:
            continue
        touched.append(item)
        if position == twice:
            touched.append(item)
    return touched


def pair_up(first, second):
    """Line two collections up side by side.

    Returns (pairs, left over from first, left over from second); at most one
    of the two left-over lists is non-empty.
    """
    first, second = list(first), list(second)
    n = min(len(first), len(second))
    return list(zip(first, second)), first[n:], second[n:]


def main():
    herd = list(HERD)
    said = ", ".join(f"{goat} {word}" for word, goat in count_aloud(herd))
    print("Counting the herd once:")
    print(f"  {said}")
    orders = factorial(len(herd))
    tally = last_words_in_every_order(herd)
    print(f"Counting in all {orders} orders, the last word said was:")
    for word, times in tally.items():
        print(f"  '{word}' in {times} of the {orders} orders")
    print()
    print("Counting slips:")
    slips = [("skip Socks", touches(herd, skip=2)),
             ("touch Star twice", touches(herd, twice=3)),
             ("both slips at once", touches(herd, skip=2, twice=3))]
    for label, touched in slips:
        print(f"  {label:<18} -> last word '{last_word(touched)}'")
    print("  Two slips can cancel out: a right answer from wrong counting!")
    print()
    pairs, kids_left, cups_left = pair_up(CHILDREN, CUPS)
    print("Pairing children with cups, without counting:")
    print("  " + ", ".join(f"{kid}-{cup}" for kid, cup in pairs))
    print(f"  children left without a cup: {', '.join(kids_left) or 'none'}")
    print(f"  cups left over: {', '.join(cups_left) or 'none'}")
    print("  So there are fewer cups than children.")
    print()
    print("How many different orders are there to try?")
    cells = [f"{n} goat{'s' if n > 1 else ''}: {factorial(n):,}"
             for n in (1, 2, 3, 4, 5, 6, 7, 10)]
    print("  " + ", ".join(cells[:4]))
    print("  " + ", ".join(cells[4:]))
    print()
    print(textwrap.fill(
        f"Epistemic status: exact and exhaustive for this herd: all {orders} "
        "orders of these five goats were counted. That is not a proof for "
        "other collections, and the number of orders grows far too fast to "
        "try them all for a big herd. Why every order of every collection "
        "ends on the same word is explained in the lesson.",
        width=78,
    ))


if __name__ == "__main__":
    main()
