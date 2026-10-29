"""Undoing chains of actions: reverse order versus the same order.

Six actions that can be undone (add 3, subtract 2, add 5, double, halve,
triple) are chained together in every possible way: 36 chains of two steps
and 216 chains of three. Each chain is run on the starting numbers 0 to 10,
then undone in two ways - undoing the steps in reverse order (last step
first), and undoing them in the same order as they were done. Fractions are
used, so halving is exact. Undoing in reverse order always gets back to the
start; undoing in the same order often does not.
"""

import textwrap
from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "chaining_actions_undo",
    "title": "Undoing a chain: reverse order or same order?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["chaining-actions"],
    "summary": (
        "Builds all 36 two-step and 216 three-step chains from six "
        "undoable actions, runs each on the starting numbers 0 to 10 with "
        "exact fractions, and undoes it either in reverse order or in the "
        "same order. Reverse order always returns to the start (the "
        "socks-and-shoes rule); the same order works only for some chains."
    ),
    "packages": [],
}

# name: (do it, undo it)
ACTIONS = {
    "add 3": (lambda x: x + 3, lambda x: x - 3),
    "subtract 2": (lambda x: x - 2, lambda x: x + 2),
    "add 5": (lambda x: x + 5, lambda x: x - 5),
    "double": (lambda x: 2 * x, lambda x: x / 2),
    "halve": (lambda x: x / 2, lambda x: 2 * x),
    "triple": (lambda x: 3 * x, lambda x: x / 3),
}
STARTS = [Fraction(n) for n in range(11)]


def run(names, x):
    """Do the named actions one after another, first to last."""
    for name in names:
        x = ACTIONS[name][0](x)
    return x


def undo_reverse(names, x):
    """Undo the steps in reverse order: the last step first."""
    for name in reversed(names):
        x = ACTIONS[name][1](x)
    return x


def undo_same_order(names, x):
    """Undo the steps in the order they were done (the mistake)."""
    for name in names:
        x = ACTIONS[name][1](x)
    return x


def always_back(names, undo):
    """Does this way of undoing return every start to where it began?"""
    return all(undo(names, run(names, x)) == x for x in STARTS)


def count_successes(length):
    """Number of chains of this length, and how many each method undoes."""
    chains = list(product(ACTIONS, repeat=length))
    reverse = sum(always_back(c, undo_reverse) for c in chains)
    same = sum(always_back(c, undo_same_order) for c in chains)
    return len(chains), reverse, same


def show(x):
    """A fraction as 5 or 11/2."""
    return str(x)


def main():
    chain = ("add 5", "double")
    start = Fraction(3)
    end = run(chain, start)
    print(f"From {start}: add 5, then double, reaches {end}.")
    print(f"Undo in reverse order (halve, then subtract 5):"
          f" {end} -> {show(undo_reverse(chain, end))}. Back at the start.")
    print(f"Undo in the same order (subtract 5, then halve):"
          f" {end} -> {show(undo_same_order(chain, end))}. Not {start}!")
    print()
    print("Every chain of the six actions, run on the starts 0 to 10:")
    print("steps  chains  undone in reverse order  undone in the same order")
    for length in (2, 3):
        total, reverse, same = count_successes(length)
        print(f"{length:>5}  {total:>6}  {reverse:>23}  {same:>24}")
    print("The same order works only for special chains: for example when")
    print("every step is an addition, or every step is a multiplication.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact (fractions) and exhaustive for these six "
        "actions, chains of two and three steps, and starting numbers 0 to "
        "10. It is strong evidence, not a proof; the socks-and-shoes rule "
        "is proved in the lesson for every chain of actions that can be "
        "undone.",
        width=78,
    ))


if __name__ == "__main__":
    main()
