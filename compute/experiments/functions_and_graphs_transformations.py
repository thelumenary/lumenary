"""Transformations of graphs and the even/odd splitting, checked exactly.

The lesson proves that the graph of y = a f(b(x - h)) + k is the graph of f
moved by the rule (x, y) -> (x/b + h, a y + k). Here we test that rule with
exact fractions on sample points, see which way y = f(x - 2) moves, and split
functions into even and odd parts, checking the parts on a grid of points.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "functions_and_graphs_transformations",
    "title": "Moving graphs and splitting functions into even and odd parts",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["functions-and-graphs"],
    "summary": (
        "Checks with exact fractions that points of y = f(x) move to points of "
        "y = a f(b(x - h)) + k by (x, y) -> (x/b + h, ay + k), shows that "
        "y = f(x - 2) moves the graph right, and splits several functions into "
        "even and odd parts, testing parity on a finite grid of rational points."
    ),
    "packages": [],
}


def transform(f, a, b, h, k):
    """The function x -> a f(b(x - h)) + k."""
    return lambda x: a * f(b * (x - h)) + k


def move_point(point, a, b, h, k):
    """Where the transformation rule sends the point (x, y)."""
    x, y = point
    return (x / b + h, a * y + k)


def rule_holds(f, a, b, h, k, xs):
    """True if every moved point (x/b + h, a f(x) + k) lies on the new graph."""
    g = transform(f, a, b, h, k)
    for x in xs:
        u, v = move_point((x, f(x)), a, b, h, k)
        if g(u) != v:
            return False
    return True


def even_part(f):
    """x -> (f(x) + f(-x)) / 2."""
    return lambda x: (f(x) + f(-x)) / 2


def odd_part(f):
    """x -> (f(x) - f(-x)) / 2."""
    return lambda x: (f(x) - f(-x)) / 2


def parity(f, xs):
    """'even', 'odd', 'zero' or 'neither', judged on the points xs only.

    A function that is both even and odd is 0 at every checked point.
    """
    is_even = all(f(-x) == f(x) for x in xs)
    is_odd = all(f(-x) == -f(x) for x in xs)
    if is_even and is_odd:
        return "zero"
    return "even" if is_even else ("odd" if is_odd else "neither")


GRID = [Fraction(n, 4) for n in range(-12, 13)]


def main():
    def f(x):
        return x ** 3 - x

    a, b, h, k = Fraction(-1), Fraction(2), Fraction(1), Fraction(3)
    print("f(x) = x^3 - x and g(x) = -f(2(x - 1)) + 3; rule (x, y) ->"
          " (x/2 + 1, -y + 3)")
    for x in [-2, -1, 0, 1, 2]:
        x = Fraction(x)
        u, v = move_point((x, f(x)), a, b, h, k)
        g = transform(f, a, b, h, k)
        print(f"  ({x}, {f(x)}) -> ({u}, {v});  g({u}) = {g(u)}")
    print(f"rule holds on all {len(GRID)} grid points:",
          rule_holds(f, a, b, h, k, GRID))
    print()

    def square(x):
        return x * x

    right = transform(square, 1, 1, 2, 0)
    zeros = ", ".join(str(x) for x in GRID if right(x) == 0)
    print(f"y = x^2 has its zero at x = 0; y = (x - 2)^2 has it at x = {zeros}:")
    print("  replacing x by x - 2 moves the graph 2 units to the RIGHT.")
    print()
    print(f"parity on the grid {GRID[0]}..{GRID[-1]} (steps of 1/4):")
    examples = [
        ("x^4 - 3x^2", lambda x: x ** 4 - 3 * x ** 2),
        ("x^3 - 5x", lambda x: x ** 3 - 5 * x),
        ("x^2 + x", lambda x: x ** 2 + x),
        ("1/(1 + x^2)", lambda x: 1 / (1 + x ** 2)),
        ("x/(1 + x^2) + 1", lambda x: x / (1 + x ** 2) + 1),
    ]
    for name, fn in examples:
        e, o = even_part(fn), odd_part(fn)
        two = Fraction(2)
        odd2 = f"({o(two)})" if o(two) < 0 else f"{o(two)}"
        print(f"  {name:16s} {parity(fn, GRID):8s} even part {parity(e, GRID):5s}"
              f" odd part {parity(o, GRID):5s} f(2) = {e(two)} + {odd2}")
    print()
    print("Epistemic status: every value above is exact rational arithmetic, but")
    print("only finitely many points are checked. A function could pass on the")
    print("grid and fail elsewhere; the lesson's proofs (and the Lean versions)")
    print("establish the transformation rule and the even/odd splitting for all")
    print("real numbers.")


if __name__ == "__main__":
    main()
