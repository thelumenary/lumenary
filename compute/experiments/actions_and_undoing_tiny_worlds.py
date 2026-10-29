"""Every action in a tiny world: which ones can be undone?

A tiny world has a few things in it, say a red, a blue and a green counter in
three boxes. An action says, for each thing, what it becomes. With n things
there are n^n actions. For worlds of 1 to 4 things this program lists every
action, searches all n^n candidates for an action that undoes it, and checks
the lesson's rule: an action can be undone exactly when it never sends two
different things to the same result. It also counts the actions that are
undone by simply doing them again, like flipping a card, and finds how many
quarter turns undo one quarter turn of an arrow.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
from math import factorial
import textwrap

EXPERIMENT = {
    "id": "actions_and_undoing_tiny_worlds",
    "title": "Every action in a tiny world: which can be undone?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["actions-and-undoing"],
    "summary": (
        "Lists all n^n actions on a world of n things (n = 1 to 4), searches "
        "every candidate undo for each, and confirms that an action can be "
        "undone exactly when no two things end up the same; counts the actions "
        "undone by repeating them. Exhaustive for these tiny worlds only; the "
        "lesson proves one direction of the rule for every world."
    ),
    "packages": [],
}


def all_actions(n):
    """Every action on the things 0..n-1, as a tuple: thing i becomes a[i]."""
    return list(product(range(n), repeat=n))


def then(a, b):
    """Do action a, then action b."""
    return tuple(b[a[i]] for i in range(len(a)))


def do_nothing(n):
    """The action that leaves every thing as it was."""
    return tuple(range(n))


def undoes(u, a):
    """Does u undo a, i.e. does doing a then u put everything back?"""
    return then(a, u) == do_nothing(len(a))


def find_undo(a):
    """Search every action for one that undoes a; return it, or None."""
    for u in all_actions(len(a)):
        if undoes(u, a):
            return u
    return None


def no_two_the_same(a):
    """True when the action never sends two different things to one result."""
    return len(set(a)) == len(a)


def turns_to_undo(turn, start):
    """How many more times must `turn` be done to undo one `turn`?"""
    count, state = 0, turn(start)
    while state != start:
        state = turn(state)
        count += 1
    return count


def describe(a):
    """Write an action as 'thing -> result' pairs, e.g. '0->1, 1->2, 2->0'."""
    return ", ".join(f"{i}->{j}" for i, j in enumerate(a))


ARROWS = ["up", "right", "down", "left"]


def quarter_turn(arrow):
    """Turn an arrow a quarter turn clockwise."""
    return ARROWS[(ARROWS.index(arrow) + 1) % 4]


def main():
    print("Tiny worlds: every action, and every possible undo, checked.")
    print("  things  actions  can be undone  undone by doing it again")
    rule_holds, counts = True, []
    for n in range(1, 5):
        acts = all_actions(n)
        undoable = [a for a in acts if find_undo(a) is not None]
        rule_holds &= all((a in undoable) == no_two_the_same(a) for a in acts)
        self_undo = sum(1 for a in acts if undoes(a, a))
        counts.append(len(undoable))
        print(f"  {n:6d} {len(acts):8d} {len(undoable):14d} {self_undo:25d}")
    print()
    print("Can be undone exactly when no two things end up the same:",
          rule_holds)
    shuffles = [factorial(n) for n in range(1, 5)]
    print("Undoable counts are the numbers of shuffles 1, 1x2, 1x2x3, 1x2x3x4:",
          counts == shuffles)
    print()
    print("Three things, an action that goes round: 0->1, 1->2, 2->0.")
    go_round = (1, 2, 0)
    print(f"  undone by doing it again? {undoes(go_round, go_round)}")
    print(f"  undone by:                {describe(find_undo(go_round))}"
          "  (round the other way)")
    extra = turns_to_undo(quarter_turn, "up")
    print(f"A quarter turn of an arrow is undone by {extra} more quarter turns.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive for worlds of 1 to 4 things "
        "(every action and every candidate undo was tried), so these counts "
        "are certain. It is not a proof for bigger worlds. The lesson proves, "
        "for every world, that an action sending two things to the same "
        "result can never be undone.",
        width=78,
    ))


if __name__ == "__main__":
    main()
