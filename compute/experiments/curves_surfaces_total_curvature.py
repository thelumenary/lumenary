"""Total curvature of closed curves: Hopf, Fenchel and Fary-Milnor.

For a closed plane curve, the signed curvature integrated along the curve,
the integral of kappa ds, is 2 pi times the turning number (Hopf's
Umlaufsatz: +-1 for a simple closed curve). For a closed space curve the
total curvature, the integral of |kappa| ds, is at least 2 pi (Fenchel), and
more than 4 pi if the curve is knotted (Fary-Milnor). We compute these
integrals numerically: derivatives by central differences, integrals by the
midpoint rule. We also check the curvature of a helix against the exact value
a / (a^2 + b^2). Evidence: numerical, for these curves only.
"""

import math

EXPERIMENT = {
    "id": "curves_surfaces_total_curvature",
    "title": "Total curvature of closed curves: Hopf, Fenchel, Fary-Milnor",
    "evidence": ["numerical"],
    "lessons": ["curves-surfaces"],
    "summary": (
        "Integrates the curvature of closed curves numerically. Plane curves "
        "(circle, ellipse, limacon, figure eight) give 2 pi times their turning "
        "numbers 1, 1, 2, 0; space curves give total curvature 2 pi for a convex "
        "plane curve and more than 4 pi for a trefoil knot, as the theorems of "
        "Fenchel and Fary-Milnor predict; a helix's curvature matches a/(a^2+b^2)."
        " Numerical evidence for these curves only."
    ),
    "packages": [],
}

H = 1e-4
N = 4000


def derivatives(curve, t):
    """First and second derivatives of a curve R -> R^n by central differences."""
    p_minus, p, p_plus = curve(t - H), curve(t), curve(t + H)
    d1 = [(b - a) / (2 * H) for a, b in zip(p_minus, p_plus)]
    d2 = [(a - 2 * c + b) / H ** 2 for a, c, b in zip(p_minus, p, p_plus)]
    return d1, d2


def cross(u, v):
    """Cross product in R^3."""
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def norm(u):
    """Euclidean length."""
    return math.sqrt(sum(x * x for x in u))


def signed_curvature(curve, t):
    """kappa = (x'y'' - y'x'') / |gamma'|^3 for a plane curve."""
    (x1, y1), (x2, y2) = derivatives(curve, t)
    return (x1 * y2 - y1 * x2) / (x1 * x1 + y1 * y1) ** 1.5


def curvature(curve, t):
    """kappa = |gamma' x gamma''| / |gamma'|^3 for a space curve."""
    d1, d2 = derivatives(curve, t)
    return norm(cross(d1, d2)) / norm(d1) ** 3


def integrate_over_period(f, curve, period=2 * math.pi, n=N):
    """Midpoint rule for the integral of f(curve, t) |gamma'(t)| dt."""
    dt = period / n
    total = 0.0
    for k in range(n):
        t = (k + 0.5) * dt
        speed = norm(derivatives(curve, t)[0])
        total += f(curve, t) * speed * dt
    return total


PLANE = {
    "circle": lambda t: (math.cos(t), math.sin(t)),
    "ellipse 3 x 1": lambda t: (3 * math.cos(t), math.sin(t)),
    "limacon r=1+2cos": lambda t: ((1 + 2 * math.cos(t)) * math.cos(t),
                                   (1 + 2 * math.cos(t)) * math.sin(t)),
    "figure eight": lambda t: (math.sin(t), math.sin(t) * math.cos(t)),
}

SPACE = {
    "circle in a plane": lambda t: (math.cos(t), math.sin(t), 0.0),
    "tilted ellipse": lambda t: (2 * math.cos(t), math.sin(t),
                                 math.sin(t)),
    "bent loop (unknot)": lambda t: (math.cos(t), math.sin(t),
                                     0.8 * math.cos(2 * t)),
    "trefoil knot": lambda t: (math.sin(t) + 2 * math.sin(2 * t),
                               math.cos(t) - 2 * math.cos(2 * t),
                               -math.sin(3 * t)),
}


def helix(a, b):
    """The helix t -> (a cos t, a sin t, b t)."""
    return lambda t: (a * math.cos(t), a * math.sin(t), b * t)


def main():
    print("Plane curves: integral of signed curvature / 2 pi = turning number")
    for name, c in PLANE.items():
        total = integrate_over_period(signed_curvature, c)
        print(f"  {name:<18} {round(total / (2 * math.pi), 5) + 0.0:9.5f}")
    print()
    print("Space curves: total curvature / pi (Fenchel: >= 2; knotted: > 4)")
    for name, c in SPACE.items():
        total = integrate_over_period(curvature, c)
        print(f"  {name:<18} {total / math.pi:9.5f}")
    print()
    a, b = 2.0, 1.0
    k = curvature(helix(a, b), 0.7)
    print(f"Helix a = {a}, b = {b}: kappa = {k:.6f}, exact a/(a^2+b^2) = "
          f"{a / (a * a + b * b):.6f}")
    print()
    print("The figure eight turns 0 times (it is not simple); the limacon with")
    print("its inner loop turns twice. Only the planar convex curves reach")
    print("Fenchel's bound 2 pi exactly, and the knotted curve exceeds 4 pi.")
    print()
    print("Epistemic status: numerical (central differences with h = 1e-4 and")
    print("a 4000-point midpoint rule), for these particular curves. The")
    print("theorems of Hopf, Fenchel and Fary-Milnor are proved in the")
    print("literature cited in the lesson, not here.")


if __name__ == "__main__":
    main()
