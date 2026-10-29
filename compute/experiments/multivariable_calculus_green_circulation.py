"""Green's theorem, numerically: circulation around a circle versus curl inside.

Green's theorem says the circulation of a C^1 field F = (P, Q) around the
boundary of a region D equals the double integral of curl F = Q_x - P_y over
D. We compute both sides numerically for circles. For the smooth field
(-y^3, x^3) they agree. For the vortex (-y, x)/(x^2 + y^2) they disagree on a
circle around the origin (2 pi versus 0): the field is singular at the
origin, so the hypothesis "C^1 on all of D" fails - and the circulation
measures the hole.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "multivariable_calculus_green_circulation",
    "title": "Green's theorem: circulation versus integrated curl",
    "evidence": ["numerical", "counterexample"],
    "lessons": ["multivariable-calculus"],
    "summary": (
        "Computes the circulation of a planar vector field around circles (by "
        "the trapezoid rule in the angle) and the double integral of its curl "
        "over the discs (midpoint rule in polar coordinates). For a smooth field "
        "both are 3 pi / 2; for the vortex field around the origin they are 2 pi "
        "and 0, showing why Green's theorem needs F to be C^1 on the whole disc."
    ),
    "packages": [],
}


def circulation(P, Q, centre, radius, n=2000):
    """Approximate the circulation of (P, Q) counterclockwise around a circle.

    Uses the trapezoid rule in the angle t, which is very accurate for smooth
    periodic integrands.
    """
    cx, cy = centre
    total = 0.0
    for i in range(n):
        t = 2 * math.pi * i / n
        x, y = cx + radius * math.cos(t), cy + radius * math.sin(t)
        dx, dy = -radius * math.sin(t), radius * math.cos(t)
        total += P(x, y) * dx + Q(x, y) * dy
    return total * 2 * math.pi / n


def disc_integral(g, centre, radius, n_r=200, n_t=200):
    """Approximate the integral of g over a disc, in polar coordinates.

    Midpoint rule in r and t; the factor r is the Jacobian of polar coordinates.
    """
    cx, cy = centre
    hr, ht = radius / n_r, 2 * math.pi / n_t
    total = 0.0
    for i in range(n_r):
        r = (i + 0.5) * hr
        for j in range(n_t):
            t = (j + 0.5) * ht
            total += g(cx + r * math.cos(t), cy + r * math.sin(t)) * r
    return total * hr * ht


def smooth_P(x, y):
    """First component of the smooth field (-y^3, x^3)."""
    return -y**3


def smooth_Q(x, y):
    """Second component of the smooth field (-y^3, x^3)."""
    return x**3


def smooth_curl(x, y):
    """curl (-y^3, x^3) = Q_x - P_y = 3x^2 + 3y^2."""
    return 3 * x**2 + 3 * y**2


def vortex_P(x, y):
    """First component of the vortex field -y / (x^2 + y^2)."""
    return -y / (x**2 + y**2)


def vortex_Q(x, y):
    """Second component of the vortex field x / (x^2 + y^2)."""
    return x / (x**2 + y**2)


def vortex_curl(x, y):
    """curl of the vortex field, which is 0 wherever it is defined."""
    return 0.0


def main():
    rows = [
        ("(-y^3, x^3)", smooth_P, smooth_Q, smooth_curl, (0, 0), 1),
        ("(-y^3, x^3)", smooth_P, smooth_Q, smooth_curl, (1, 0.5), 0.8),
        ("vortex", vortex_P, vortex_Q, vortex_curl, (0, 0), 1),
        ("vortex", vortex_P, vortex_Q, vortex_curl, (0, 0), 0.01),
        ("vortex", vortex_P, vortex_Q, vortex_curl, (2, 0), 1),
    ]
    print("Circulation around a circle versus the integral of curl inside")
    print("field         centre       radius   circulation   integral of curl")
    for name, P, Q, curl, c, r in rows:
        circ = circulation(P, Q, c, r)
        inner = disc_integral(curl, c, r)
        centre = f"({c[0]}, {c[1]})"
        print(f"{name:<13} {centre:<12} {r:<7}  {circ:11.6f}   {inner:11.6f}")
    print(f"For reference: 3 pi / 2 = {1.5 * math.pi:.6f}, 2 pi = {2 * math.pi:.6f}")
    print("Smooth field: the two columns agree, as Green's theorem says.")
    print("Vortex around the origin: circulation 2 pi on every circle, however")
    print("small, but curl 0 wherever the field is defined. Around (2, 0), away")
    print("from the singularity, both sides are 0.")
    print()
    print("Epistemic status: numerical quadrature (trapezoid and midpoint rules),")
    print("accurate here to many digits but not a proof. That the circulation of")
    print("the vortex around the unit circle is exactly 2 pi is a short exact")
    print("computation (formalised in the lesson's Lean file); Green's theorem")
    print("itself is proved in the lesson for rectangles.")


if __name__ == "__main__":
    main()
