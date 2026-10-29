"""Unit quaternions as rotations, checked in exact rational arithmetic.

A unit quaternion q acts on pure quaternions v = xi + yj + zk by v -> q v q*,
and the lesson shows this is a rotation rho(q) of R^3 with rho(q) = rho(-q).
For quaternions with rational coordinates everything is exact, so the program
can verify, with no rounding at all, that

* rho(q) is orthogonal with determinant 1 for several rational unit q;
* rho(-q) = rho(q) and rho(pq) = rho(p) rho(q) (a two-to-one homomorphism);
* rho(p) rho(q) != rho(q) rho(p): rotations of space do not commute;
* q = (1 + i + j + k)/2 is a 120-degree turn permuting the coordinate axes;
* the 24 Hurwitz units (+-1, +-i, +-j, +-k, (+-1 +-i +-j +-k)/2) are closed
  under multiplication and map onto exactly 12 rotations - the rotation group
  of a regular tetrahedron - each hit by exactly two quaternions.

These are exact, exhaustive checks of finitely many cases.
"""

import math
from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "matrix_groups_quaternions",
    "title": "Unit quaternions as rotations, in exact arithmetic",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["matrix-groups"],
    "summary": (
        "Multiplies quaternions with rational coordinates exactly, builds the "
        "rotation matrix of v -> q v q*, and verifies orthogonality, determinant "
        "1, rho(-q) = rho(q), the homomorphism property and non-commutativity; "
        "then checks exhaustively that the 24 Hurwitz units form a group mapping "
        "two-to-one onto the 12 rotations of a tetrahedron."
    ),
    "packages": [],
}


def qmul(p, q):
    """Hamilton's product of quaternions given as (a, b, c, d) = a+bi+cj+dk."""
    a1, b1, c1, d1 = p
    a2, b2, c2, d2 = q
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
            a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
            a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def conj(q):
    """The quaternion conjugate a - bi - cj - dk."""
    return (q[0], -q[1], -q[2], -q[3])


def norm_sq(q):
    """|q|^2 = a^2 + b^2 + c^2 + d^2."""
    return sum(x * x for x in q)


def rho(q):
    """The 3 x 3 matrix (rows) of v -> q v q* on pure quaternions."""
    cols = []
    for e in [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]:
        cols.append(qmul(qmul(q, e), conj(q))[1:])
    return tuple(tuple(cols[j][i] for j in range(3)) for i in range(3))


def matmul(a, b):
    """Product of 3 x 3 matrices given as tuples of rows."""
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def transpose(a):
    return tuple(tuple(a[j][i] for j in range(3)) for i in range(3))


def det3(a):
    """Determinant of a 3 x 3 matrix."""
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


IDENTITY = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def frac_q(*xs, den=1):
    return tuple(Fraction(x, den) for x in xs)


def show(q):
    """Compact text for a rational quaternion, e.g. '(1, 2, 2, 4)/5'."""
    den = 1
    for x in q:
        den = den * x.denominator // math.gcd(den, x.denominator)
    body = ", ".join(str(int(x * den)) for x in q)
    return f"({body})" + (f"/{den}" if den > 1 else "")


def hurwitz_units():
    """The 24 unit quaternions with all coordinates in Z or all in Z + 1/2."""
    units = []
    for i in range(4):
        for s in (1, -1):
            q = [Fraction(0)] * 4
            q[i] = Fraction(s)
            units.append(tuple(q))
    for signs in product((1, -1), repeat=4):
        units.append(tuple(Fraction(s, 2) for s in signs))
    return units


def main():
    samples = [frac_q(1, 1, 1, 1, den=2), frac_q(3, 4, 0, 0, den=5),
               frac_q(1, 2, 2, 4, den=5), frac_q(2, 1, 4, 2, den=5)]
    print("Rational unit quaternions q = (a, b, c, d) = a + bi + cj + dk:")
    print("   " + ", ".join(show(q) for q in samples))
    ok = all(norm_sq(q) == 1 and
             matmul(transpose(rho(q)), rho(q)) == IDENTITY and
             det3(rho(q)) == 1 and
             rho(tuple(-x for x in q)) == rho(q) for q in samples)
    print("rho(q) orthogonal, det 1, and rho(-q) = rho(q) for all:", ok)
    hom = all(rho(qmul(p, q)) == matmul(rho(p), rho(q))
              for p in samples for q in samples)
    print("rho(pq) = rho(p) rho(q) for all 16 pairs:", hom)
    p, q = samples[1], samples[2]
    print("rho(p) rho(q) = rho(q) rho(p) for p, q above:",
          matmul(rho(p), rho(q)) == matmul(rho(q), rho(p)))
    r = rho(samples[0])
    print("rho((1 + i + j + k)/2) =", [[int(x) for x in row] for row in r])
    print("   (x -> y -> z -> x: a 120-degree turn about (1, 1, 1))")
    print()
    units = hurwitz_units()
    closed = all(qmul(a, b) in units for a in units for b in units)
    rotations = {}
    for u in units:
        rotations.setdefault(rho(u), []).append(u)
    print(f"Hurwitz units: {len(units)} quaternions,"
          f" closed under multiplication: {closed}")
    print(f"distinct rotations rho(u): {len(rotations)};"
          " quaternions per rotation:",
          sorted({len(v) for v in rotations.values()}))
    print()
    print("Epistemic status: exact rational arithmetic, so each 'True' is an\n"
          "exact verification for the quaternions listed (and an exhaustive\n"
          "check over the 24 Hurwitz units). That rho is a two-to-one\n"
          "homomorphism from all unit quaternions onto SO(3) is the theorem\n"
          "proved in the lesson.")


if __name__ == "__main__":
    main()
