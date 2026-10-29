"""Hyperbolic triangles in the upper half-plane: angle defect versus area.

Distances come from cosh d(z, w) = 1 + |z - w|^2 / (2 Im z Im w). The angles of
a triangle are computed in two independent ways: from the side lengths by the
hyperbolic law of cosines, and from the Euclidean tangent directions of the
circular arcs (the model is conformal, so Euclidean angles are hyperbolic
angles). The area, the integral of dx dy / y^2 over the triangle, is estimated
by Monte Carlo and compared with the defect pi - (alpha + beta + gamma). The
experiment also applies random Moebius maps z -> (az + b)/(cz + d) with
ad - bc = 1 and checks that side lengths and angles do not change, and it
pushes the vertices towards the boundary to watch the defect approach pi.
Numerical and statistical evidence, not proof.
"""

import cmath
import math

import numpy as np

EXPERIMENT = {
    "id": "non_euclidean_geometry_hyperbolic",
    "title": "Hyperbolic triangles: angle defect, area and Moebius invariance",
    "evidence": ["numerical", "statistical"],
    "lessons": ["non-euclidean-geometry"],
    "summary": (
        "Computes the angles of hyperbolic triangles in the upper half-plane by "
        "the law of cosines and, independently, from tangent directions; compares "
        "the defect with the Monte Carlo area (integral of dx dy / y^2); checks "
        "that random Moebius maps preserve lengths and angles; and shows the "
        "defect approaching pi as the triangle approaches an ideal triangle."
    ),
    "packages": ["numpy"],
}


def hyp_dist(z, w):
    """Hyperbolic distance in the upper half-plane."""
    return math.acosh(1 + abs(z - w) ** 2 / (2 * z.imag * w.imag))


def angles_by_cosine_law(z1, z2, z3):
    """The three angles from the side lengths (hyperbolic law of cosines)."""
    a, b, c = hyp_dist(z2, z3), hyp_dist(z1, z3), hyp_dist(z1, z2)

    def ang(opp, s1, s2):
        num = math.cosh(s1) * math.cosh(s2) - math.cosh(opp)
        return math.acos(max(-1.0, min(1.0, num / (math.sinh(s1) * math.sinh(s2)))))

    return ang(a, b, c), ang(b, a, c), ang(c, a, b)


def geodesic(z, w):
    """('vertical', x) or ('circle', centre, radius) for the line through z, w."""
    if abs(z.real - w.real) < 1e-12:
        return ("vertical", z.real)
    c = (abs(w) ** 2 - abs(z) ** 2) / (2 * (w.real - z.real))
    return ("circle", c, abs(z - c))


def tangent(z, w):
    """Unit Euclidean tangent at z of the geodesic arc from z towards w."""
    g = geodesic(z, w)
    if g[0] == "vertical":
        t = 1j if w.imag > z.imag else -1j
    else:
        t = 1j * (z - g[1])  # perpendicular to the radius
        if ((w - z) * t.conjugate()).real < 0:
            t = -t
    return t / abs(t)


def angles_by_tangents(z1, z2, z3):
    """The three angles as Euclidean angles between tangent vectors."""
    out = []
    for p, q, r in ((z1, z2, z3), (z2, z3, z1), (z3, z1, z2)):
        out.append(abs(cmath.phase(tangent(p, r) / tangent(p, q))))
    return tuple(out)


def same_side(points, g, ref):
    """Boolean array: which points lie on the same side of geodesic g as ref."""
    if g[0] == "vertical":
        return np.sign(points.real - g[1]) == np.sign(ref.real - g[1])
    s = np.abs(points - g[1]) ** 2 - g[2] ** 2
    return np.sign(s) == np.sign(abs(ref - g[1]) ** 2 - g[2] ** 2)


def area_monte_carlo(z1, z2, z3, n, rng):
    """(estimate, standard error) of the hyperbolic area of the triangle."""
    verts = (z1, z2, z3)
    sides = [(verts[i], verts[(i + 1) % 3], verts[(i + 2) % 3]) for i in range(3)]
    xs = [v.real for v in verts]
    top = max(v.imag for v in verts)
    for p, q, _ in sides:
        g = geodesic(p, q)
        if g[0] == "circle" and min(p.real, q.real) < g[1] < max(p.real, q.real):
            top = max(top, g[2])
    x0, x1, y0 = min(xs), max(xs), min(v.imag for v in verts)
    pts = rng.uniform(x0, x1, n) + 1j * rng.uniform(y0, top, n)
    inside = np.ones(n, dtype=bool)
    for p, q, r in sides:
        inside &= same_side(pts, geodesic(p, q), r)
    f = np.where(inside, 1 / pts.imag ** 2, 0.0) * (x1 - x0) * (top - y0)
    return float(f.mean()), float(f.std() / math.sqrt(n))


def mobius(m, z):
    """Apply z -> (az + b) / (cz + d)."""
    a, b, c, d = m
    return (a * z + b) / (c * z + d)


def random_sl2(rng):
    """A random real 2 x 2 matrix with determinant 1."""
    while True:
        a, b, c = rng.uniform(-2, 2, 3)
        if abs(a) > 0.2:
            return a, b, c, (1 + b * c) / a


TRIANGLES = {
    "i, 1+2i, -1+1.5i": (1j, 1 + 2j, -1 + 1.5j),
    "2i, 3i, 1+2i": (2j, 3j, 1 + 2j),
    "0.2i, 2+0.3i, 1+3i": (0.2j, 2 + 0.3j, 1 + 3j),
}


def main():
    rng = np.random.default_rng(1868)
    print("Hyperbolic triangles (curvature -1), angles in radians")
    print(f"{'vertices':<20}{'angle sum':>10}{'defect':>9}{'MC area':>18}"
          f"{'tangent':>10}")
    for label, (z1, z2, z3) in TRIANGLES.items():
        law = angles_by_cosine_law(z1, z2, z3)
        tan = angles_by_tangents(z1, z2, z3)
        gap = max(abs(x - y) for x, y in zip(law, tan))
        area, se = area_monte_carlo(z1, z2, z3, 400_000, rng)
        print(f"{label:<20}{sum(law):10.5f}{math.pi - sum(law):9.5f}"
              f"{area:10.4f} +- {se:.4f}{gap:10.1e}")
    print("'tangent' = largest gap between the two angle computations.")
    print()
    worst_len = worst_ang = 0.0
    z = TRIANGLES["i, 1+2i, -1+1.5i"]
    for _ in range(200):
        m = random_sl2(rng)
        w = [mobius(m, v) for v in z]
        for i in range(3):
            j = (i + 1) % 3
            worst_len = max(worst_len, abs(hyp_dist(z[i], z[j]) -
                                           hyp_dist(w[i], w[j])))
        worst_ang = max(worst_ang, max(abs(p - q) for p, q in zip(
            angles_by_cosine_law(*z), angles_by_tangents(*w))))
    print("200 random Moebius maps with ad - bc = 1:")
    print(f"  largest change in a side length: {worst_len:.1e}")
    print(f"  largest change in an angle:      {worst_ang:.1e}")
    print()
    print("Towards an ideal triangle: vertices -1 + ei, 1 + ei, i/e")
    for e in (0.5, 0.1, 0.01, 0.001):
        s = sum(angles_by_cosine_law(-1 + e * 1j, 1 + e * 1j, 1j / e))
        print(f"  e = {e:<6} angle sum {s:.6f}, defect {math.pi - s:.6f}")
    print("The defect creeps up to pi but never reaches it: area < pi.")
    print()
    print("Epistemic status: floating-point computation and a Monte Carlo")
    print("estimate with its standard error; agreement on a few triangles is")
    print("evidence. The lesson proves area = defect and Moebius invariance.")


if __name__ == "__main__":
    main()
