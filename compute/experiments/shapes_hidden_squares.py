"""How many squares hide on a dot grid, if tilted squares count too?

A square stays a square when it is turned, so a dot grid hides more squares
than the upright ones children usually find first. This program lists every
set of four dots that are the corners of a square, using whole numbers only:
from each pair of dots it builds the square on that side by a quarter turn,
exactly like the lesson's Lean file. It counts upright and tilted squares on
grids of 2 x 2 up to 6 x 6 dots, checks that a quarter turn of the grid sends
every square to a square, and compares the totals with the formula
n^2 (n^2 - 1) / 12 for an n x n grid of dots.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "shapes_hidden_squares",
    "title": "Hidden squares on a dot grid, upright and tilted",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["shapes"],
    "summary": (
        "Finds every square whose corners are dots of an n x n dot grid "
        "(n = 2 to 6), upright or tilted, by exhaustive search with whole-number "
        "arithmetic, checks that a quarter turn of the grid maps squares to "
        "squares, and compares the counts with n^2(n^2 - 1)/12. This is exact "
        "for these grids only; the lesson explains why the formula always holds."
    ),
    "packages": [],
}


def grid(n):
    """All dots (x, y) of an n x n grid, with 0 <= x, y < n."""
    if n < 1:
        raise ValueError("a grid needs at least one dot per side")
    return [(x, y) for y in range(n) for x in range(n)]


def quarter_turn(v):
    """Turn the arrow v = (dx, dy) a quarter turn anticlockwise: (-dy, dx)."""
    dx, dy = v
    return (-dy, dx)


def squares_on_grid(n):
    """Return the set of squares on an n x n dot grid.

    Each square is a frozenset of its four corners. From every ordered pair
    of different dots p, q we turn the side p -> q a quarter turn to find the
    other two corners; each square is found four times, and the set keeps it
    once.
    """
    dots = set(grid(n))
    found = set()
    for p in dots:
        for q in dots:
            if p == q:
                continue
            dx, dy = quarter_turn((q[0] - p[0], q[1] - p[1]))
            r = (q[0] + dx, q[1] + dy)
            s = (p[0] + dx, p[1] + dy)
            if r in dots and s in dots:
                found.add(frozenset((p, q, r, s)))
    return found


def is_upright(square):
    """A square is upright when its sides run along the grid lines."""
    xs = {x for x, _ in square}
    return len(xs) == 2


def side_squared(square):
    """The squared side length of a square (the smallest squared distance)."""
    pts = sorted(square)
    return min(
        (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2
        for i, a in enumerate(pts)
        for b in pts[i + 1:]
    )


def turn_grid(square, n):
    """Turn a whole n x n grid a quarter turn about its centre."""
    return frozenset((n - 1 - y, x) for x, y in square)


def turned_squares_are_squares(n):
    """Check that turning the grid sends every square on it to a square."""
    found = squares_on_grid(n)
    return all(turn_grid(sq, n) in found for sq in found)


def formula(n):
    """The number of squares on an n x n dot grid: n^2 (n^2 - 1) / 12."""
    return n * n * (n * n - 1) // 12


def count_by_bounding_box(n):
    """Count squares as in the lesson's proof: a k x k box holds k squares.

    An upright k x k box fits in (n - k)^2 places, and inside it there are
    k squares with corners on its sides (side arrows (a, k - a), a < k).
    """
    return sum(k * (n - k) ** 2 for k in range(1, n))


def main():
    print("Squares with corners on the dots of an n x n dot grid:")
    print("  dots    upright  tilted  total  n^2(n^2-1)/12")
    for n in range(2, 7):
        found = squares_on_grid(n)
        up = sum(1 for sq in found if is_upright(sq))
        print(f"  {n} x {n}  {up:7d} {len(found) - up:7d} {len(found):6d}"
              f" {formula(n):9d}")
    print()
    found = squares_on_grid(4)
    tilted = sorted((side_squared(sq), sorted(sq)) for sq in found
                    if not is_upright(sq))
    print(f"The {len(tilted)} tilted squares on the 4 x 4 grid (corners):")
    for _, corners in tilted:
        print("  " + " ".join(f"({x},{y})" for x, y in corners))
    print()
    ok = all(turned_squares_are_squares(n) for n in range(2, 7))
    print(f"A quarter turn of the grid sends every square to a square: {ok}")
    same = all(count_by_bounding_box(n) == formula(n) for n in range(2, 51))
    print(f"Box count sum k(n-k)^2 equals the formula for n = 2..50: {same}")
    print()
    print(textwrap.fill(
        "Epistemic status: the counts are exact and come from checking every "
        "pair of dots, so they are certain for grids of 2 x 2 to 6 x 6 dots. "
        "Agreement with n^2(n^2-1)/12 for these sizes, and of the box count "
        "up to n = 50, is evidence, not a proof for every grid; the lesson's "
        "bounding-box argument is the proof.",
        width=78,
    ))


if __name__ == "__main__":
    main()
