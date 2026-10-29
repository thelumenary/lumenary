"""Counting the symmetries of shapes by trying every way to move the corners.

A symmetry of a polygon sends corners to corners and keeps every distance
between corners the same. So the program tries *every* way of sending the
corners to the corners (every permutation) and keeps those that preserve all
distances. Each one it keeps is a symmetry: a turn if the corners keep their
order round the shape, a flip (a line of symmetry) if the order is reversed.

Regular polygons: the distance between two corners depends only on how many
steps apart they are round the polygon, so we compare steps exactly.
Quadrilaterals: corners have whole-number coordinates, so squared distances
are exact whole numbers.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math
import textwrap
from itertools import combinations, permutations

EXPERIMENT = {
    "id": "symmetry_transformations_polygons",
    "title": "Counting symmetries: every way to move the corners",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["symmetry-transformations"],
    "summary": (
        "Tries every permutation of the corners of regular polygons with 3 to "
        "7 sides and of six quadrilaterals, keeping those that preserve all "
        "corner-to-corner distances, and sorts them into turns and flips. "
        "Regular n-gons give n turns and n lines of symmetry; the rectangle "
        "gives 2 and 2. Exhaustive for these shapes only."
    ),
    "packages": [],
}

#: Quadrilaterals with whole-number corners, listed in order round the shape.
QUADRILATERALS = {
    "square": [(1, 1), (-1, 1), (-1, -1), (1, -1)],
    "rectangle": [(2, 1), (-2, 1), (-2, -1), (2, -1)],
    "rhombus": [(0, 2), (-1, 0), (0, -2), (1, 0)],
    "kite": [(0, 3), (-1, 0), (0, -1), (1, 0)],
    "parallelogram": [(0, 0), (3, 0), (4, 1), (1, 1)],
    "isosceles trapezium": [(-2, 0), (2, 0), (1, 2), (-1, 2)],
}


def steps_apart(n, i, j):
    """How many steps apart corners i and j are, round a regular n-gon."""
    k = (i - j) % n
    return min(k, n - k)


def cross(o, a, b):
    """Positive if o, a, b go anticlockwise, negative if clockwise."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def sq_dist(p, q):
    """Squared distance between two points with whole-number coordinates."""
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def symmetries(n, dist, orientation):
    """All distance-preserving permutations, split into (turns, flips).

    `dist(i, j)` is the distance between corners i and j (or anything that
    determines it), and `orientation(i, j, k)` is +1 or -1 according to
    whether corners i, j, k go anticlockwise or clockwise.
    """
    turns, flips = [], []
    pairs = list(combinations(range(n), 2))
    for perm in permutations(range(n)):
        if all(dist(perm[i], perm[j]) == dist(i, j) for i, j in pairs):
            same = orientation(*perm[:3]) == orientation(0, 1, 2)
            (turns if same else flips).append(perm)
    return turns, flips


def regular_polygon_symmetries(n):
    """Turns and flips of a regular polygon with n corners."""
    def orientation(i, j, k):
        return 1 if (j - i) % n < (k - i) % n else -1
    return symmetries(n, lambda i, j: steps_apart(n, i, j), orientation)


def quadrilateral_symmetries(corners):
    """Turns and flips of a quadrilateral given by its corners."""
    def orientation(i, j, k):
        return 1 if cross(corners[i], corners[j], corners[k]) > 0 else -1
    return symmetries(len(corners),
                      lambda i, j: sq_dist(corners[i], corners[j]),
                      orientation)


def main():
    names = {3: "equilateral triangle", 4: "regular 4-gon (square)",
             5: "regular pentagon",
             6: "regular hexagon", 7: "regular heptagon"}
    print("Shape                   tried   symmetries   turns   flips")
    for n in range(3, 8):
        tried = math.factorial(n)
        turns, flips = regular_polygon_symmetries(n)
        print(f"{names[n]:<22} {tried:>6}   {len(turns) + len(flips):>10}"
              f"   {len(turns):>5}   {len(flips):>5}")
    for name, corners in QUADRILATERALS.items():
        turns, flips = quadrilateral_symmetries(corners)
        print(f"{name:<22} {24:>6}   {len(turns) + len(flips):>10}"
              f"   {len(turns):>5}   {len(flips):>5}")
    print()
    print("turns = order of rotational symmetry (the 'no move' counts);")
    print("flips = number of lines of symmetry.")
    print("A regular polygon with n sides: n turns and n lines of symmetry.")
    print("A rectangle has only 2 lines of symmetry: its diagonals are not.")
    print()
    print(textwrap.fill(
        "Epistemic status: exhaustive and exact for these eleven shapes - "
        "every way of moving the corners was tried. It is evidence for the "
        "rule about regular polygons, not a proof for every n; the lesson "
        "explains why a regular n-gon always has 2n symmetries.",
        width=78,
    ))


if __name__ == "__main__":
    main()
