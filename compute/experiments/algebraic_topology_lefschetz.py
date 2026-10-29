"""The Lefschetz fixed-point theorem on the torus, checked by exact counting.

A 2x2 integer matrix A induces a map f(x) = A x (mod 1) of the torus
T^2 = R^2/Z^2. On homology it acts by 1 on H_0, by A on H_1 and by det A on
H_2, so its Lefschetz number is L(f) = 1 - tr A + det A = det(I - A). We count
the fixed points exactly with fractions: x is fixed when (A - I) x is an
integer vector, and all such x lie on the grid (1/d) Z^2 with d = |det(A - I)|.
Exact enumeration for a handful of matrices; the general theorem is proved by
other means.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "algebraic_topology_lefschetz",
    "title": "Lefschetz numbers and fixed points of maps of the torus",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["algebraic-topology"],
    "summary": (
        "For linear maps x -> Ax of the torus R^2/Z^2 it computes the Lefschetz "
        "number det(I - A) from the action on homology and counts fixed points "
        "exactly with rational arithmetic, confirming |L| = number of fixed points "
        "when L is nonzero. Exact for the listed matrices; it illustrates the "
        "Lefschetz theorem, it does not prove it."
    ),
    "packages": [],
}

MATRICES = {
    "rotation by 90 deg": ((0, -1), (1, 0)),
    "x -> -x": ((-1, 0), (0, -1)),
    "cat map": ((2, 1), (1, 1)),
    "doubling": ((2, 0), (0, 2)),
    "A = [[3,1],[1,0]]": ((3, 1), (1, 0)),
    "shear [[1,1],[0,1]]": ((1, 1), (0, 1)),
}


def lefschetz_number(a):
    """L(f) = sum (-1)^k tr(f_* on H_k) = 1 - tr A + det A."""
    (p, q), (r, s) = a
    return 1 - (p + s) + (p * s - q * r)


def fixed_points(a):
    """Exact fixed points of x -> A x (mod 1) in [0,1)^2, or None if infinite."""
    (p, q), (r, s) = a
    m = ((p - 1, q), (r, s - 1))
    d = abs(m[0][0] * m[1][1] - m[0][1] * m[1][0])
    if d == 0:
        return None
    points = []
    for i in range(d):
        for j in range(d):
            x, y = Fraction(i, d), Fraction(j, d)
            u = m[0][0] * x + m[0][1] * y
            v = m[1][0] * x + m[1][1] * y
            if u.denominator == 1 and v.denominator == 1:
                points.append((x, y))
    return points


def show(point):
    """Format a point with fractional coordinates."""
    return "(" + ", ".join(str(c) for c in point) + ")"


def main():
    print("Maps x -> A x (mod 1) of the torus: Lefschetz number vs fixed points")
    print()
    print(f"{'map':<22}{'L = det(I-A)':<14}{'#fixed':<8}fixed points")
    for name, a in MATRICES.items():
        lef = lefschetz_number(a)
        pts = fixed_points(a)
        if pts is None:
            print(f"{name:<22}{lef:<14}{'inf':<8}a whole circle (L = 0)")
            continue
        shown = " ".join(show(p) for p in pts[:3])
        if len(pts) > 3:
            shown += " ..."
        print(f"{name:<22}{lef:<14}{len(pts):<8}{shown}")
    print()
    print("Whenever L is nonzero, the number of fixed points is |L|: every fixed")
    print("point of a linear map has index sign det(I - A). A translation by a")
    print("small vector is homotopic to the identity, has L = 0 and no fixed")
    print("points at all: L = 0 gives no information.")
    print()
    print("Epistemic status: exact rational arithmetic, exhaustive over the")
    print("grid (1/d)Z^2 that must contain every fixed point, for six matrices.")
    print("It illustrates the Lefschetz fixed-point theorem; the theorem itself")
    print("is proved with simplicial approximation and homology.")


if __name__ == "__main__":
    main()
