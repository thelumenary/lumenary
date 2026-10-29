"""Shadows of a ball: linear non-squeezing, tested on random matrices.

Coordinates on R^4 are (x1, y1, x2, y2) and w = dx1^dy1 + dx2^dy2. For a
matrix A, the image of the unit ball projected to a coordinate plane is an
ellipse (its "shadow"). If the plane is the symplectic plane (x1, y1) and A
is symplectic, the shadow always has area at least pi (the area of a unit
disc): this is linear non-squeezing, in the strong form proved in the lesson.
Volume-preserving matrices can make the same shadow as small as we like, and
even symplectic matrices can shrink the shadow on the Lagrangian plane
(x1, x2).

Evidence: numerical. Finitely many random matrices are sampled with a fixed
seed; the inequality itself is a theorem (see the lesson and the Lean file).
"""

import math
import random

EXPERIMENT = {
    "id": "symplectic_geometry_shadows",
    "title": "Shadows of a ball under symplectic and volume-preserving maps",
    "evidence": ["numerical", "experimental"],
    "lessons": ["symplectic-geometry"],
    "summary": (
        "Samples random 4 x 4 symplectic matrices (products of elementary "
        "symplectic maps) and random volume-preserving matrices, and computes "
        "the area of the shadow of the unit ball on the symplectic plane "
        "(x1, y1) and on the Lagrangian plane (x1, x2). Symplectic shadows on "
        "(x1, y1) never drop below pi, as the theorem predicts; the others do. "
        "Sampling is evidence, not proof."
    ),
    "packages": [],
}

J4 = [[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]]


def matmul(a, b):
    """Product of two square matrices given as lists of rows."""
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def transpose(a):
    """Transpose of a matrix given as a list of rows."""
    return [list(r) for r in zip(*a)]


def omega(u, v):
    """The standard symplectic form on R^4 in the order (x1, y1, x2, y2)."""
    return u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]


def symplectic_defect(a):
    """Largest entry of |A J A^T - J|; zero exactly when A is symplectic."""
    m = matmul(matmul(a, J4), transpose(a))
    return max(abs(m[i][j] - J4[i][j]) for i in range(4) for j in range(4))


def det4(a):
    """Determinant by cofactor expansion along the first row."""
    def det3(m):
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
    total = 0.0
    for j in range(4):
        minor = [row[:j] + row[j + 1:] for row in a[1:]]
        total += (-1) ** j * a[0][j] * det3(minor)
    return total


def shadow_area(a, i, j):
    """Area of the image of the unit ball under A projected to (coord i, j).

    The shadow is the ellipse {(r_i . u, r_j . u) : |u| <= 1} for the rows
    r_i, r_j of A; its area is pi * sqrt(det G) for their Gram matrix G.
    """
    ri, rj = a[i], a[j]
    gii = sum(x * x for x in ri)
    gjj = sum(x * x for x in rj)
    gij = sum(x * y for x, y in zip(ri, rj))
    return math.pi * math.sqrt(max(gii * gjj - gij * gij, 0.0))


def elementary_symplectic(rng):
    """A random elementary symplectic map of one of three kinds."""
    kind = rng.randrange(3)
    eye = [[float(i == j) for j in range(4)] for i in range(4)]
    if kind == 0:  # an SL(2) map on one of the two symplectic planes
        a, b, c = (rng.uniform(-2, 2) for _ in range(3))
        while abs(a) < 0.2:
            a = rng.uniform(-2, 2)
        d = (1 + b * c) / a
        k = 2 * rng.randrange(2)
        eye[k][k], eye[k][k + 1], eye[k + 1][k], eye[k + 1][k + 1] = a, b, c, d
    elif kind == 1:  # y <- y + S x with S symmetric (couples the planes)
        s11, s12, s22 = (rng.uniform(-2, 2) for _ in range(3))
        eye[1][0], eye[1][2], eye[3][0], eye[3][2] = s11, s12, s12, s22
    else:  # the same rotation of (x1, x2) and of (y1, y2)
        t = rng.uniform(0, 2 * math.pi)
        c, s = math.cos(t), math.sin(t)
        eye[0][0], eye[0][2], eye[2][0], eye[2][2] = c, -s, s, c
        eye[1][1], eye[1][3], eye[3][1], eye[3][3] = c, -s, s, c
    return eye


def random_symplectic(rng, factors=6):
    """A product of several random elementary symplectic maps."""
    a = elementary_symplectic(rng)
    for _ in range(factors - 1):
        a = matmul(a, elementary_symplectic(rng))
    return a


def random_volume_preserving(rng):
    """A random matrix with determinant 1 (Gaussian entries, rescaled)."""
    while True:
        a = [[rng.gauss(0, 1) for _ in range(4)] for _ in range(4)]
        d = det4(a)
        if abs(d) > 1e-3:
            if d < 0:
                a[0] = [-x for x in a[0]]
                d = -d
            s = d ** -0.25
            return [[s * x for x in row] for row in a]


def main():
    rng = random.Random(2024)
    trials = 2000
    sym = [random_symplectic(rng) for _ in range(trials)]
    vol = [random_volume_preserving(rng) for _ in range(trials)]
    defect = max(symplectic_defect(a) for a in sym)
    w = min(omega(a[0], a[1]) for a in sym)
    print(f"{trials} random symplectic matrices: max |A J A^T - J| = "
          f"{defect:.1e}")
    print(f"  smallest w(row x1, row y1) = {w:.12f} (theory: exactly 1)")
    print(f"  smallest det A = {min(det4(a) for a in sym):.9f} (theory: 1)")
    print()
    print("Shadow of the unit ball, as a multiple of pi (unit disc = 1):")
    print(f"{'':30}{'plane (x1, y1)':>16}{'plane (x1, x2)':>16}")
    for label, mats in [("symplectic, smallest", sym),
                        ("volume-preserving, smallest", vol)]:
        s1 = min(shadow_area(a, 0, 1) for a in mats) / math.pi
        s2 = min(shadow_area(a, 0, 2) for a in mats) / math.pi
        print(f"{label:<30}{s1:>16.4f}{s2:>16.4f}")
    squeeze = [[0.5, 0, 0, 0], [0, 0.5, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]
    print(f"{'the squeeze diag(1/2,1/2,2,2)':<30}"
          f"{shadow_area(squeeze, 0, 1) / math.pi:>16.4f}"
          f"{shadow_area(squeeze, 0, 2) / math.pi:>16.4f}")
    print()
    print("Symplectic maps never shrink the (x1, y1) shadow below a unit disc,")
    print("but they can shrink the shadow on the Lagrangian plane (x1, x2).")
    print()
    print("Epistemic status: numerical sampling of finitely many matrices with")
    print("a fixed seed. It agrees with the theorem (shadow area >= pi on a")
    print("symplectic plane, proved in the lesson and formalised in Lean for")
    print("the cylinder version) but proves nothing by itself.")


if __name__ == "__main__":
    main()
