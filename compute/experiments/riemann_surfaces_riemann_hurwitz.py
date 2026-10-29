"""Branched covers: Riemann-Hurwitz and the monodromy of square roots.

Part 1 checks the Riemann-Hurwitz formula 2g_X - 2 = n(2g_Y - 2) + sum(e_p - 1)
for rational maps of the Riemann sphere to itself (g_X = g_Y = 0). The
ramification index e_p at each critical point is measured numerically, by
counting how many solutions of f(z) = f(p) + eps lie close to p.

Part 2 computes genera of curves from branched covers of the sphere: the
hyperelliptic curves w^2 = f(z), branched over the roots of f (and over
infinity when deg f is odd), and the Fermat curves x^d + y^d = 1, branched
over the d-th roots of unity.

Part 3 continues a square root along loops numerically: w^2 = z flips sign
round the origin; w^2 = z^3 - z flips sign round a loop enclosing one branch
point but not round a loop enclosing two.
"""

import cmath
import math

import numpy as np

EXPERIMENT = {
    "id": "riemann_surfaces_riemann_hurwitz",
    "title": "Riemann-Hurwitz and the monodromy of square roots",
    "evidence": ["numerical", "exact"],
    "lessons": ["riemann-surfaces"],
    "summary": (
        "Verifies the Riemann-Hurwitz formula for polynomial and rational maps of "
        "the Riemann sphere, measuring each ramification index by counting nearby "
        "preimages, "
        "computes the genus of hyperelliptic curves w^2 = f(z) and of Fermat "
        "curves from their branch data, and continues square roots numerically "
        "along loops to show the sign change round a branch point."
    ),
    "packages": ["numpy"],
}


def critical_points(num, den, tol=1e-3):
    """Distinct finite critical points of f = num/den: roots of num' den - num den'."""
    p, q = np.poly1d(num), np.poly1d(den)
    wronskian = np.polyder(p) * q - p * np.polyder(q)
    points = []
    for r in np.roots(wronskian.coeffs):
        if all(abs(r - c) > tol for c in points):
            points.append(complex(r))
    return points


def local_degree(num, den, c, eps=1e-12, radius=0.05):
    """e_c: the number of solutions of f(z) = f(c) + eps lying close to c."""
    p, q = np.poly1d(num), np.poly1d(den)
    target = p(c) / q(c) + eps
    roots = np.roots((p - target * q).coeffs)
    return sum(1 for r in roots if abs(r - c) < radius)


def total_ramification(num, den):
    """R = sum of (e_p - 1): local degrees counted numerically at the finite
    critical points, plus the ramification at infinity, |deg num - deg den| - 1."""
    finite = sum(local_degree(num, den, c) - 1 for c in critical_points(num, den))
    gap = abs(len(num) - len(den))
    return finite + max(gap - 1, 0)


def riemann_hurwitz_genus(degree, genus_y, total_ramification):
    """Solve 2g_X - 2 = n(2g_Y - 2) + R for g_X."""
    twice = degree * (2 * genus_y - 2) + total_ramification + 2
    if twice % 2:
        raise ValueError("Riemann-Hurwitz gives a half-integer genus")
    return twice // 2


def hyperelliptic_genus(deg_f):
    """Genus of w^2 = f(z), f squarefree of degree deg_f >= 1."""
    branch_points = deg_f if deg_f % 2 == 0 else deg_f + 1
    return riemann_hurwitz_genus(2, 0, branch_points)


def fermat_genus(d):
    """Genus of x^d + y^d = 1 via (x, y) -> x: degree d, d points with e = d."""
    return riemann_hurwitz_genus(d, 0, d * (d - 1))


def continue_sqrt(f, centre, radius, turns=1, steps=2000):
    """Follow a continuous branch of sqrt(f(z)) round a circle; return end/start."""
    z0 = centre + radius
    w = cmath.sqrt(f(z0))
    start = w
    for k in range(1, turns * steps + 1):
        z = centre + radius * cmath.exp(2j * math.pi * k / steps)
        root = cmath.sqrt(f(z))
        w = root if abs(root - w) <= abs(root + w) else -root
    return w / start


def main():
    print("1. Riemann-Hurwitz for maps P^1 -> P^1: -2 = n(-2) + R")
    cases = [("z^3 - 3z", 3, total_ramification([1, 0, -3, 0], [1])),
             ("z^4", 4, total_ramification([1, 0, 0, 0, 0], [1])),
             ("(z^2 + 1)/(z - 2)", 2, total_ramification([1, 0, 1], [1, -2])),
             ("(z^3 - 1)/(z^2 + 3)", 3,
              total_ramification([1, 0, 0, -1], [1, 0, 3]))]
    for name, n, r in cases:
        print(f"   {name:<20} degree {n}: R = {r}, n(-2) + R = {-2 * n + r}")
    print("2. Genus from branch data")
    for deg in [3, 4, 5, 6]:
        print(f"   w^2 = f(z), deg f = {deg}: genus {hyperelliptic_genus(deg)}")
    for d in [2, 3, 4, 5]:
        print(f"   Fermat x^{d} + y^{d} = 1: genus {fermat_genus(d)}"
              f" (plane curve formula (d-1)(d-2)/2 = {(d - 1) * (d - 2) // 2})")
    print("3. Continuing a square root once round a loop (end / start):")
    loops = [("sqrt(z), circle round 0", lambda z: z, 0, 1.0, 1),
             ("sqrt(z), twice round 0", lambda z: z, 0, 1.0, 2),
             ("sqrt(z^3 - z), round 1 only", lambda z: z**3 - z, 1, 0.5, 1),
             ("sqrt(z^3 - z), round 0 and 1", lambda z: z**3 - z, 0.5, 0.8, 1),
             ("sqrt(z^3 - z), round all three", lambda z: z**3 - z, 0, 2.0, 1)]
    for name, f, c, r, turns in loops:
        ratio = continue_sqrt(f, c, r, turns)
        print(f"   {name:<32} {ratio.real:+.6f}")
    print()
    print("Epistemic status: numerical root-finding and path-following for a few")
    print("maps and loops, plus exact integer arithmetic for the genus formulas.")
    print("Evidence for Riemann-Hurwitz and for the monodromy of branch points;")
    print("the proofs are in the lesson.")


if __name__ == "__main__":
    main()
