"""Stokes's theorem on a disc, and periods of closed 1-forms.

Part 1 checks Stokes's theorem numerically for the 1-form x^3 dy on the unit
disc: the line integral round the circle and the area integral of
d(x^3 dy) = 3x^2 dx^dy both approximate 3*pi/4.

Part 2 integrates the closed form dtheta = (x dy - y dx)/(x^2 + y^2) on the
punctured plane round several loops. Its periods are 2*pi times winding
numbers, never anything else, and round a loop that misses the puncture the
period is 0, as Stokes predicts. With two punctures, a closed form is
determined up to exact forms by its two periods: H^1 of the twice-punctured
plane is R^2. All integrals are computed by quadrature (numerical evidence).
"""

import math

EXPERIMENT = {
    "id": "smooth_manifolds_stokes_periods",
    "title": "Stokes's theorem and the periods of closed forms",
    "evidence": ["numerical"],
    "lessons": ["smooth-manifolds"],
    "summary": (
        "Checks Stokes's theorem for x^3 dy on the unit disc by quadrature (both "
        "sides approximate 3*pi/4), then computes periods of the closed form "
        "dtheta round circles, an ellipse and a double loop in the punctured "
        "plane, and of a combination of two angle forms in the twice-punctured "
        "plane. Numerical evidence, with the quadrature error reported."
    ),
    "packages": [],
}


def line_integral(form, curve, n=4000):
    """Integral of the 1-form P dx + Q dy along a closed curve on [0, 2*pi].

    ``form(x, y)`` returns (P, Q); ``curve(t)`` returns (x, y, dx/dt, dy/dt).
    The trapezoid rule on a periodic integrand is very accurate.
    """
    h = 2 * math.pi / n
    total = 0.0
    for k in range(n):
        x, y, dx, dy = curve(k * h)
        p, q = form(x, y)
        total += p * dx + q * dy
    return total * h


def disc_integral(density, n_r=400, n_t=400):
    """Integral of a function over the unit disc, midpoint rule in polar form."""
    hr, ht = 1.0 / n_r, 2 * math.pi / n_t
    total = 0.0
    for i in range(n_r):
        r = (i + 0.5) * hr
        for j in range(n_t):
            t = (j + 0.5) * ht
            total += density(r * math.cos(t), r * math.sin(t)) * r
    return total * hr * ht


def angle_form(a=0.0, b=0.0):
    """dtheta measured from the point (a, b): ((x-a) dy - (y-b) dx) / r^2."""
    def form(x, y):
        dx, dy = x - a, y - b
        r2 = dx * dx + dy * dy
        return (-dy / r2, dx / r2)
    return form


def circle(cx, cy, radius, turns=1):
    """A circle traversed ``turns`` times anticlockwise, as (x, y, x', y')."""
    def curve(t):
        s = turns * t
        return (cx + radius * math.cos(s), cy + radius * math.sin(s),
                -radius * turns * math.sin(s), radius * turns * math.cos(s))
    return curve


def ellipse(a, b):
    """The ellipse (a cos t, b sin t), anticlockwise."""
    return lambda t: (a * math.cos(t), b * math.sin(t),
                      -a * math.sin(t), b * math.cos(t))


def combine(c1, f1, c2, f2):
    """The 1-form c1 f1 + c2 f2."""
    def form(x, y):
        p1, q1 = f1(x, y)
        p2, q2 = f2(x, y)
        return (c1 * p1 + c2 * p2, c1 * q1 + c2 * q2)
    return form


def main():
    exact = 3 * math.pi / 4
    lhs = line_integral(lambda x, y: (0.0, x**3), circle(0, 0, 1))
    rhs = disc_integral(lambda x, y: 3 * x * x)
    print("1. Stokes for w = x^3 dy on the unit disc (exact value 3*pi/4):")
    print(f"   boundary integral  {lhs:.10f}   error {abs(lhs - exact):.1e}")
    print(f"   integral of dw     {rhs:.10f}   error {abs(rhs - exact):.1e}")
    print()
    print("2. Periods of dtheta = (x dy - y dx)/(x^2 + y^2), divided by 2*pi:")
    loops = [
        ("unit circle round 0", circle(0, 0, 1)),
        ("circle of radius 0.01 round 0", circle(0, 0, 0.01)),
        ("ellipse 3 x 0.2 round 0", ellipse(3, 0.2)),
        ("circle round 0, twice", circle(0, 0, 1, turns=2)),
        ("circle centred at (3, 0)", circle(3, 0, 1)),
    ]
    for name, loop in loops:
        ratio = round(line_integral(angle_form(), loop) / (2 * math.pi), 8)
        print(f"   {name:<32} {ratio + 0.0:+.8f}")
    print("   Annulus 0.01 < r < 1: outer minus inner period = 0 = integral of")
    print("   d(dtheta), so Stokes holds although dtheta is not exact.")
    print()
    form = combine(2.0, angle_form(-1, 0), -0.5, angle_form(1, 0))
    print("3. Two punctures at (-1, 0) and (1, 0); w = 2 dth_left - 0.5 dth_right:")
    for name, loop in [("loop round (-1, 0)", circle(-1, 0, 0.5)),
                       ("loop round (1, 0)", circle(1, 0, 0.5)),
                       ("loop round both", circle(0, 0, 3))]:
        print(f"   {name:<20} period / 2*pi = "
              f"{line_integral(form, loop) / (2 * math.pi):+.6f}")
    print("   The two periods (2, -0.5) pin down the class of w: H^1 = R^2.")
    print()
    print("Epistemic status: numerical quadrature. The agreement in part 1 is")
    print("evidence for one form on one disc; the integer periods in part 2 are")
    print("evidence for the theorem that periods of dtheta are 2*pi times winding")
    print("numbers. The proofs are Stokes's theorem and the lesson's argument.")


if __name__ == "__main__":
    main()
