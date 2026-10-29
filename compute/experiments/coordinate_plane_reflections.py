"""Reflections and grid distances on every point of a small grid.

The experiment takes all 121 points (a, b) with whole-number coordinates from
-5 to 5, plus a few points with fraction coordinates, and checks: reflecting
twice returns each point; reflection in the x-axis swaps quadrants 1 and 4 and
2 and 3; the points it leaves fixed are exactly those on the x-axis; and the
reflections, the half turn and the coordinate swap (a, b) -> (b, a) keep the
grid ("taxicab") distance |a - c| + |b - d| between every pair of points. It
also counts grid lines against unit steps. Exact arithmetic over a finite
grid: exhaustive evidence for these points, not a proof for all points.
"""

from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "coordinate_plane_reflections",
    "title": "Reflections and grid distances, point by point",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["coordinate-plane"],
    "summary": (
        "Checks on all 121 whole-number points from -5 to 5 (and some fraction "
        "points) that reflecting twice in an axis returns each point, that "
        "reflection in the x-axis swaps quadrants 1 and 4 and 2 and 3, which "
        "points it fixes, and that reflections, the half turn and swapping the "
        "coordinates keep grid distances between all 14,641 pairs of points."
    ),
    "packages": [],
}


def reflect_x(p):
    """Reflection in the x-axis: (a, b) -> (a, -b)."""
    return (p[0], -p[1])


def reflect_y(p):
    """Reflection in the y-axis: (a, b) -> (-a, b)."""
    return (-p[0], p[1])


def half_turn(p):
    """Half turn about the origin: (a, b) -> (-a, -b)."""
    return (-p[0], -p[1])


def swap(p):
    """Swap the coordinates: (a, b) -> (b, a), reflection in y = x."""
    return (p[1], p[0])


def stretch_x(p):
    """A non-example: stretch horizontally, (a, b) -> (2a, b)."""
    return (2 * p[0], p[1])


def quadrant(p):
    """1, 2, 3 or 4, or 0 for a point on an axis."""
    a, b = p
    if a > 0 and b > 0:
        return 1
    if a < 0 < b:
        return 2
    if a < 0 and b < 0:
        return 3
    if a > 0 > b:
        return 4
    return 0


def grid_distance(p, q):
    """Distance along grid lines: |a - c| + |b - d|."""
    return abs(p[0] - q[0]) + abs(p[1] - q[1])


def grid_points(radius):
    """All points with whole-number coordinates from -radius to radius."""
    r = range(-radius, radius + 1)
    return [(a, b) for a, b in product(r, r)]


def keeps_distance(move, points):
    """Number of pairs (p, q) whose grid distance changes under ``move``."""
    return sum(grid_distance(move(p), move(q)) != grid_distance(p, q)
               for p in points for q in points)


def lines_and_steps(a, c):
    """(unit steps, grid lines crossed) walking from a to c on a number line."""
    lo, hi = min(a, c), max(a, c)
    return hi - lo, len(range(lo, hi + 1))


def main():
    pts = grid_points(5)
    fracs = [(Fraction(1, 2), Fraction(-7, 3)), (Fraction(-5, 4), Fraction(2))]
    every = pts + fracs
    print(f"Points checked: {len(pts)} whole-number points and {len(fracs)} "
          "fraction points")
    twice = all(reflect_x(reflect_x(p)) == p and reflect_y(reflect_y(p)) == p
                for p in every)
    print(f"Reflecting twice returns every point: {twice}")
    moves = {}
    for p in every:
        key = (quadrant(p), quadrant(reflect_x(p)))
        moves[key] = moves.get(key, 0) + 1
    print("Quadrant before -> after reflecting in the x-axis (number of points):")
    print("  " + ", ".join(f"{a}->{b}: {n}" for (a, b), n in sorted(moves.items())))
    fixed = [p for p in pts if reflect_x(p) == p]
    print(f"Points fixed by the x-axis reflection: {len(fixed)}, all with y = 0:"
          f" {all(b == 0 for _, b in fixed)}")
    same = [p for p in pts if swap(p) == p]
    print(f"Points with (a, b) = (b, a): {len(same)}, all on the line y = x")
    print()
    print(f"Grid distance changes among all {len(pts) ** 2} pairs of points:")
    for name, move in [("reflect in x-axis", reflect_x),
                       ("reflect in y-axis", reflect_y),
                       ("half turn", half_turn), ("swap (a, b)", swap)]:
        print(f"  {name:<18} {keeps_distance(move, pts)} pairs changed")
    print(f"  {'stretch x by 2':<18} {keeps_distance(stretch_x, pts)} pairs"
          " changed (a non-example)")
    print()
    steps, lines = lines_and_steps(-3, 4)
    print(f"From x = -3 to x = 4: {steps} unit steps, but {lines} grid lines.")
    print()
    print("Epistemic status: exact, exhaustive checks on the points listed. They")
    print("cannot cover every point of the plane; the lesson's proofs (and the")
    print("Lean proofs) show the same facts for all points with any rational")
    print("coordinates.")


if __name__ == "__main__":
    main()
