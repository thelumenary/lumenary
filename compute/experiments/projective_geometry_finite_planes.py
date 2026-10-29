"""Finite projective planes PG(2, p): counting, incidence, Desargues, Pappus.

Over the field F_p of integers mod a prime p, the projective plane PG(2, p)
has as points the non-zero vectors of F_p^3 up to non-zero scalars, and lines
likewise (a line l contains the point x when l . x = 0 mod p). The program

* counts points and lines (p^2 + p + 1 each) and points per line (p + 1);
* checks exhaustively that two distinct points lie on exactly one line and
  two distinct lines meet in exactly one point;
* counts the points of the conic x^2 + y^2 = z^2 (p + 1 for odd p);
* tests the theorems of Desargues and Pappus on seeded random configurations
  in PG(2, 7), computing joins and meets with cross products mod p.

Incidence checks are exhaustive for the listed p; the theorem checks are
random samples, i.e. evidence for that plane only.
"""

import random
from itertools import combinations, product

EXPERIMENT = {
    "id": "projective_geometry_finite_planes",
    "title": "Finite projective planes: incidence, conics, Desargues, Pappus",
    "evidence": ["exhaustive-finite", "experimental"],
    "lessons": ["projective-geometry"],
    "summary": (
        "Builds PG(2, p) over the integers mod p for p = 2, 3, 5, 7, verifies by "
        "exhaustion that it has p^2 + p + 1 points and lines with p + 1 points on "
        "each line, that two points determine one line and two lines meet in one "
        "point, counts the p + 1 points of a conic, and tests Desargues' and "
        "Pappus' theorems on seeded random configurations in PG(2, 7)."
    ),
    "packages": [],
}


def normalise(v, p):
    """Scale a non-zero vector mod p so that its first non-zero entry is 1."""
    v = [x % p for x in v]
    for x in v:
        if x:
            inv = pow(x, p - 2, p)
            return tuple(y * inv % p for y in v)
    raise ValueError("zero vector")


def points(p):
    """All points of PG(2, p), as normalised triples."""
    return sorted({normalise(v, p) for v in product(range(p), repeat=3)
                   if any(v)})


def dot(u, v, p):
    return sum(a * b for a, b in zip(u, v)) % p


def cross(u, v, p):
    """The cross product mod p: the line through two points (or the meet)."""
    return ((u[1] * v[2] - u[2] * v[1]) % p, (u[2] * v[0] - u[0] * v[2]) % p,
            (u[0] * v[1] - u[1] * v[0]) % p)


def collinear(u, v, w, p):
    """True when the three points lie on one line (determinant zero mod p)."""
    return dot(u, cross(v, w, p), p) == 0


def incidence_report(p):
    """(#points, set of points-per-line counts, axioms hold) for PG(2, p)."""
    pts = points(p)
    lines = pts  # by duality the lines are the same triples
    on = {l: [x for x in pts if dot(l, x, p) == 0] for l in lines}
    per_line = {len(v) for v in on.values()}
    two_points = all(sum(1 for l in lines if dot(l, x, p) == 0 and
                         dot(l, y, p) == 0) == 1
                     for x, y in combinations(pts, 2))
    two_lines = all(sum(1 for x in pts if dot(l, x, p) == 0 and
                        dot(m, x, p) == 0) == 1
                    for l, m in combinations(lines, 2))
    return len(pts), per_line, two_points and two_lines


def conic_points(p):
    """Number of points of x^2 + y^2 = z^2 in PG(2, p)."""
    return sum(1 for (x, y, z) in points(p) if (x * x + y * y - z * z) % p == 0)


def desargues_trial(rng, p):
    """Random triangles perspective from a point; are the meets collinear?"""
    while True:
        o, a, b, c = (rng.choices(range(p), k=3) for _ in range(4))
        s, t, u = (rng.randrange(1, p) for _ in range(3))
        a2 = [(o[i] + s * a[i]) % p for i in range(3)]
        b2 = [(o[i] + t * b[i]) % p for i in range(3)]
        c2 = [(o[i] + u * c[i]) % p for i in range(3)]
        tri = [a, b, c, a2, b2, c2, o]
        if any(not any(v) for v in tri):
            continue
        if collinear(a, b, c, p) or collinear(a2, b2, c2, p):
            continue
        meets = [cross(cross(a, b, p), cross(a2, b2, p), p),
                 cross(cross(b, c, p), cross(b2, c2, p), p),
                 cross(cross(c, a, p), cross(c2, a2, p), p)]
        if any(not any(m) for m in meets):
            continue
        return collinear(*meets, p)


def pappus_trial(rng, p):
    """Three points on each of two lines; are the cross-joins collinear?"""
    while True:
        l, m = (rng.choices(range(p), k=3) for _ in range(2))
        if not any(cross(l, m, p)):
            continue
        pts = points(p)
        on_l = [x for x in pts if dot(l, x, p) == 0 and dot(m, x, p) != 0]
        on_m = [x for x in pts if dot(m, x, p) == 0 and dot(l, x, p) != 0]
        a, b, c = rng.sample(on_l, 3)
        a2, b2, c2 = rng.sample(on_m, 3)
        meets = [cross(cross(a, b2, p), cross(a2, b, p), p),
                 cross(cross(a, c2, p), cross(a2, c, p), p),
                 cross(cross(b, c2, p), cross(b2, c, p), p)]
        return collinear(*meets, p)


def main():
    print(" p   points  points/line  2 pts -> 1 line, 2 lines -> 1 pt"
          "  conic pts")
    for p in (2, 3, 5, 7):
        n, per_line, axioms = incidence_report(p)
        conic = conic_points(p) if p > 2 else "-"
        print(f"{p:2d}   {n:6d}  {sorted(per_line)!s:>11}  {axioms!s:>31}"
              f"  {conic!s:>9}")
    print("(p^2 + p + 1 points, p + 1 per line; a conic has p + 1 points)")
    print()
    rng = random.Random(2024)
    trials = 300
    des = sum(desargues_trial(rng, 7) for _ in range(trials))
    pap = sum(pappus_trial(rng, 7) for _ in range(trials))
    print(f"PG(2, 7): Desargues held in {des} of {trials} random "
          "configurations")
    print(f"PG(2, 7): Pappus held in {pap} of {trials} random configurations")
    print()
    print("Epistemic status: the counts and incidence axioms are exhaustive\n"
          "checks for p = 2, 3, 5, 7. The Desargues and Pappus results are\n"
          "random samples in one finite plane: evidence, not proof. The\n"
          "proofs (valid over every field) are in the lesson and in Lean.")


if __name__ == "__main__":
    main()
