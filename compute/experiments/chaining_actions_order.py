"""When does the order of two actions matter?

For every pair of number actions (add 2, add 5, double, triple, square, do
nothing) the program checks whether 'f, then g' and 'g, then f' give the
same result for every starting number from 0 to 20. Then it does the same
for four moves of an L-shaped tile on a grid (quarter turn, half turn, and
two flips), comparing the positions the tile ends up in. The tables show
that swapping the order usually matters, and pick out the special pairs
for which it does not.
"""

import textwrap

EXPERIMENT = {
    "id": "chaining_actions_order",
    "title": "Does the order of two actions matter?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["chaining-actions"],
    "summary": (
        "Checks every pair of six number actions on the starting numbers "
        "0 to 20, and every pair of four moves of an L-shaped tile, to see "
        "whether doing them in either order gives the same result. Two "
        "additions, two multiplications, two turns or two flips can be "
        "swapped; an addition and a multiplication, or a quarter turn and a "
        "flip, cannot."
    ),
    "packages": [],
}

NUMBER_ACTIONS = {
    "add 2": lambda n: n + 2,
    "add 5": lambda n: n + 5,
    "double": lambda n: 2 * n,
    "triple": lambda n: 3 * n,
    "square": lambda n: n * n,
    "do nothing": lambda n: n,
}
SHORT = ["+2", "+5", "x2", "x3", "sq", "id"]
STARTS = range(0, 21)

MOVES = {
    "quarter turn": lambda p: (p[1], -p[0]),
    "half turn": lambda p: (-p[0], -p[1]),
    "flip left-right": lambda p: (-p[0], p[1]),
    "flip up-down": lambda p: (p[0], -p[1]),
}
L_SHAPE = [(0, 2), (0, 1), (0, 0), (1, 0)]


def chain(f, g):
    """The chain 'f, then g'."""
    return lambda x: g(f(x))


def first_difference(f, g, starts=STARTS):
    """First start where 'f, then g' and 'g, then f' differ, or None."""
    for n in starts:
        if chain(f, g)(n) != chain(g, f)(n):
            return n
    return None


def place(move, shape=L_SHAPE):
    """Where the tile is after a move: the set of grid points it covers."""
    return frozenset(move(p) for p in shape)


def moves_commute(f, g, shape=L_SHAPE):
    """Do 'f, then g' and 'g, then f' put the tile in the same place?"""
    return place(chain(f, g), shape) == place(chain(g, f), shape)


def main():
    print("Number actions: is 'f, then g' the same as 'g, then f' for every")
    print("start from 0 to 20?   (= same, x different)")
    print(" " * 12 + "".join(f"{s:>5}" for s in SHORT))
    for name, f in NUMBER_ACTIONS.items():
        marks = ["=" if first_difference(f, g) is None else "x"
                 for g in NUMBER_ACTIONS.values()]
        print(f"{name:<12}" + "".join(f"{m:>5}" for m in marks))
    add5, double = NUMBER_ACTIONS["add 5"], NUMBER_ACTIONS["double"]
    n = first_difference(add5, double)
    print(f"add 5 and double, from {n}: add 5 first gives"
          f" {chain(add5, double)(n)}, double first gives"
          f" {chain(double, add5)(n)}.")
    print()
    print("Moves of an L-shaped tile: same place in either order?")
    names = list(MOVES)
    print(" " * 16 + "".join(f"{m.split()[0]:>11}" for m in names))
    print(" " * 16 + "".join(f"{m.split()[1]:>11}" for m in names))
    for name, f in MOVES.items():
        marks = ["=" if moves_commute(f, g) else "x" for g in MOVES.values()]
        print(f"{name:<16}" + "".join(f"{m:>11}" for m in marks))
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive for what was checked - the "
        "starting numbers 0 to 20, and the four moves of one tile. An 'x' is "
        "a proof that the order matters (a counterexample was found). An '=' "
        "for numbers is evidence only; the lesson explains why, for example, "
        "two additions can always be swapped.",
        width=78,
    ))


if __name__ == "__main__":
    main()
