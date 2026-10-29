"""Line integrals of 1-forms: closed, exact, and the angle form.

We integrate 1-forms P dx + Q dy along sampled paths by pulling them back:
the integral of w over gamma is the integral of P(gamma) x' + Q(gamma) y' dt,
computed with the midpoint rule and exact derivatives of the paths. An exact
form df integrates to f(end) - f(start) along every path, so to 0 around
every loop. The angle form d theta = (x dy - y dx)/(x^2 + y^2) is closed, yet
its integral around a loop is 2 pi times the winding number about the origin,
and from (1, 0) to (-1, 0) it gives +pi along the upper half circle and -pi
along the lower one: path dependence, so d theta is not exact on the punctured
plane. A non-closed form, x dy - y dx, measures twice the enclosed area, as
Green's theorem says. Evidence: numerical.
"""

import math

EXPERIMENT = {
    "id": "differential_forms_line_integrals",
    "title": "Line integrals: exact forms, the angle form and Green's theorem",
    "evidence": ["numerical"],
    "lessons": ["differential-forms"],
    "summary": (
        "Integrates 1-forms along paths by pulling them back to [0, 1]. An exact "
        "form gives 0 around every loop; the closed angle form d theta gives 2 pi "
        "times the winding number, and +pi or -pi between the same endpoints "
        "along different half circles, so it is not exact; x dy - y dx gives "
        "twice the enclosed area, as Green's theorem predicts. Numerical evidence "
        "on sample paths."
    ),
    "packages": [],
}

STEPS = 4000


def line_integral(form, path, velocity, steps=STEPS):
    """Midpoint rule for the integral of form = (P, Q) along a path on [0, 1]."""
    total = 0.0
    for k in range(steps):
        t = (k + 0.5) / steps
        x, y = path(t)
        dx, dy = velocity(t)
        p, q = form(x, y)
        total += (p * dx + q * dy) / steps
    return total


def dtheta(x, y):
    """The angle form (-y dx + x dy) / (x^2 + y^2)."""
    r2 = x * x + y * y
    return -y / r2, x / r2


def exact_form(x, y):
    """d f for f(x, y) = x^2 y + sin(x y)."""
    return 2 * x * y + y * math.cos(x * y), x * x + x * math.cos(x * y)


def area_form(x, y):
    """x dy - y dx, with d(x dy - y dx) = 2 dx ^ dy."""
    return -y, x


def circle(cx, cy, r, turns=1):
    """Loop around a circle (path, velocity), parametrised on [0, 1]."""
    w = 2 * math.pi * turns

    def path(t):
        return cx + r * math.cos(w * t), cy + r * math.sin(w * t)

    def velocity(t):
        return -r * w * math.sin(w * t), r * w * math.cos(w * t)
    return path, velocity


def half_circle(upper=True):
    """From (1, 0) to (-1, 0) along the upper or lower unit half circle."""
    s = 1 if upper else -1

    def path(t):
        return math.cos(math.pi * t), s * math.sin(math.pi * t)

    def velocity(t):
        return -math.pi * math.sin(math.pi * t), s * math.pi * math.cos(math.pi * t)
    return path, velocity


def square_loop():
    """The boundary of the square [-1, 2] x [-1, 2], anticlockwise."""
    corners = [(-1, -1), (2, -1), (2, 2), (-1, 2), (-1, -1)]

    def side(t):
        k = min(int(4 * t), 3)
        return k, 4 * t - k

    def path(t):
        k, u = side(t)
        (x0, y0), (x1, y1) = corners[k], corners[k + 1]
        return x0 + u * (x1 - x0), y0 + u * (y1 - y0)

    def velocity(t):
        k, _ = side(t)
        (x0, y0), (x1, y1) = corners[k], corners[k + 1]
        return 4 * (x1 - x0), 4 * (y1 - y0)
    return path, velocity


def main():
    loops = [
        ("unit circle", circle(0, 0, 1)),
        ("circle twice round", circle(0, 0, 1, turns=2)),
        ("circle centre (3, 0)", circle(3, 0, 1)),
        ("square [-1, 2]^2", square_loop()),
    ]
    print("Loop                    d theta / 2 pi    exact df    x dy - y dx")
    for name, (p, v) in loops:
        a = line_integral(dtheta, p, v) / (2 * math.pi)
        b = line_integral(exact_form, p, v)
        c = line_integral(area_form, p, v)
        a, b, c = (round(val, 6) + 0.0 for val in (a, b, c))
        print(f"  {name:<22} {a:12.6f} {b:12.6f} {c:12.6f}")
    print("  (x dy - y dx gives twice the area swept: 2 pi, 2 x 2 pi for the")
    print("  doubled loop, 2 pi, and 2 x 9 for the square)")
    print()
    up = line_integral(dtheta, *half_circle(True))
    down = line_integral(dtheta, *half_circle(False))
    print("From (1, 0) to (-1, 0):")
    print(f"  d theta along the upper half circle: {up / math.pi:9.6f} pi")
    print(f"  d theta along the lower half circle: {down / math.pi:9.6f} pi")
    print("  The integral depends on the path, so d theta = df is impossible:")
    print("  an exact form would give f(-1, 0) - f(1, 0) both times.")
    print()
    print("Epistemic status: numerical (4000-point midpoint rule on each path).")
    print("That d theta is closed but not exact, and Green's and Stokes'")
    print("theorems, are proved in the lesson (and the non-exactness in Lean).")


if __name__ == "__main__":
    main()
