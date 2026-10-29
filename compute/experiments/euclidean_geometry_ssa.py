"""Why SSA is not a congruence criterion: counting the triangles it allows.

Fix the angle at A by a ray from A = (0, 0) through a lattice point (p, q)
with p^2 + q^2 = r^2 a perfect square (so all coordinates stay rational),
put B on that ray with AB = c, and look for C on the positive x-axis with
BC = a. Then C = (t, 0) with (t - cp/r)^2 = a^2 - (cq/r)^2, a quadratic in t
with zero, one or two positive roots. We count them with exact rational
arithmetic (comparing squares, never square roots) and check the classical
rule for the "ambiguous case" on every case of a finite grid.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "euclidean_geometry_ssa",
    "title": "SSA: zero, one or two triangles",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["euclidean-geometry"],
    "summary": (
        "Counts, with exact rational arithmetic, the triangles with given AB = c, "
        "BC = a and angle A, for 4,000 integer cases and ten rational directions "
        "of the ray AB. It exhibits two non-congruent triangles with the same "
        "SSA data and checks the classical rule for when this happens on every "
        "case of the grid. A finite check of the rule; the lesson proves it."
    ),
    "packages": [],
}

#: Rays from A through (p, q) with p^2 + q^2 a perfect square, q > 0.
DIRECTIONS = [(4, 3), (3, 4), (12, 5), (5, 12), (15, 8), (8, 15), (0, 1),
              (-3, 4), (-4, 3), (-12, 5)]


def count_triangles(a_sq, c, p, q):
    """Number of points C = (t, 0), t > 0, with BC^2 = a_sq, B = c(p, q)/r.

    Exact: u = cp/r is the foot of the perpendicular from B, h = cq/r its
    height, and t = u +- sqrt(D) with D = a_sq - h^2.
    """
    r = math.isqrt(p * p + q * q)
    if r * r != p * p + q * q or q <= 0 or c <= 0 or a_sq <= 0:
        raise ValueError("need q > 0, c > 0, a_sq > 0 and p^2 + q^2 square")
    u, h = Fraction(c * p, r), Fraction(c * q, r)
    d = a_sq - h * h
    if d < 0:
        return 0
    if d == 0:
        return 1 if u > 0 else 0
    larger_positive = u >= 0 or u * u < d    # u + sqrt(d) > 0
    smaller_positive = u > 0 and u * u > d   # u - sqrt(d) > 0
    return int(larger_positive) + int(smaller_positive)


def predicted_count(a_sq, c, p, q):
    """The classical rule, written with the height h = c sin A."""
    r = math.isqrt(p * p + q * q)
    h_sq = Fraction(c * q, r) ** 2
    if p > 0:  # angle A is acute
        if a_sq < h_sq:
            return 0
        if a_sq == h_sq or a_sq >= c * c:
            return 1
        return 2
    return 1 if a_sq > c * c else 0  # A is right or obtuse


def third_sides(a_sq, c, p, q):
    """The possible lengths AC = t, as floats (for display only)."""
    r = math.isqrt(p * p + q * q)
    u, d = c * p / r, a_sq - (c * q / r) ** 2
    roots = sorted({u - math.sqrt(max(d, 0)), u + math.sqrt(max(d, 0))})
    return [t for t in roots if t > 1e-12] if d >= 0 else []


def main():
    print("Example: A = (0, 0), B = (4, 3), so AB = 5; we want BC^2 = 10.")
    print(f"  triangles: {count_triangles(10, 5, 4, 3)}, AC = "
          f"{third_sides(10, 5, 4, 3)}  (C = (3, 0) or C = (5, 0))")
    print("Same angle A (ray through (4, 3)), AB = c = 10, height h = 6:")
    for a in range(5, 12):
        n = count_triangles(a * a, 10, 4, 3)
        sides = ", ".join(f"{t:.3f}" for t in third_sides(a * a, 10, 4, 3))
        print(f"  BC = {a:2d}: {n} triangle(s)   AC = {sides or '-'}")
    cases, twos, mismatches = 0, 0, []
    for p, q in DIRECTIONS:
        for c in range(1, 21):
            for a in range(1, 21):
                got = count_triangles(a * a, c, p, q)
                cases += 1
                twos += got == 2
                if got != predicted_count(a * a, c, p, q):
                    mismatches.append((a, c, p, q))
    print(f"Grid: a, c in 1..20, {len(DIRECTIONS)} directions: {cases} cases")
    print(f"  cases with two different triangles: {twos}")
    print(f"  disagreements with the classical rule (0, 1 or 2 triangles): "
          f"{len(mismatches)}")
    print()
    print("Epistemic status: the counts are exact (rational arithmetic, no")
    print("square roots are compared), so the example is a genuine")
    print("counterexample to 'SSA implies congruence'. The agreement with the")
    print("rule is an exhaustive check of 4,000 cases only; the proof that the")
    print("rule always holds is the circle-meets-line argument in the lesson.")


if __name__ == "__main__":
    main()
