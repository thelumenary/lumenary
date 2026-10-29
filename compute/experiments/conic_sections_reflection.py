"""Ray tracing in a parabolic dish and an elliptical room.

Parabola y = x^2 / (4p): rays come straight down, hit the curve, and are
reflected by the law of reflection (reverse the component along the normal).
We find where each reflected ray crosses the axis x = 0; the theorem says it
is always the focus (0, p). Ellipse x^2/a^2 + y^2/b^2 = 1: rays leave one
focus in many directions; after one reflection we measure how far each ray
passes from the other focus, and check that the distances to the foci add up
to 2a at every point hit. Floating-point evidence for finitely many rays.
"""

import math

EXPERIMENT = {
    "id": "conic_sections_reflection",
    "title": "Ray tracing: the reflective properties of conics",
    "evidence": ["numerical"],
    "lessons": ["conic-sections"],
    "summary": (
        "Traces 9 vertical rays into the parabola y = x^2/4 and 12 rays from "
        "one focus of the ellipse x^2/25 + y^2/9 = 1, reflecting each by the "
        "law of reflection, and measures how close the reflected rays come to "
        "the focus (parabola) or the other focus (ellipse). Numerical evidence "
        "for finitely many rays; the lesson proves the property for all rays."
    ),
    "packages": [],
}


def reflect(v, n):
    """Reflect the direction v in a mirror with normal vector n."""
    k = 2 * (v[0] * n[0] + v[1] * n[1]) / (n[0] ** 2 + n[1] ** 2)
    return (v[0] - k * n[0], v[1] - k * n[1])


def parabola_axis_crossing(p, x0):
    """Where the vertical ray at x = x0 crosses x = 0 after reflection."""
    point = (x0, x0 * x0 / (4 * p))
    normal = (x0, -2 * p)  # perpendicular to the tangent direction (2p, x0)
    d = reflect((0.0, -1.0), normal)
    t = -point[0] / d[0]  # requires x0 != 0
    return point[1] + t * d[1]


def ellipse_hit(a, b, start, direction):
    """First point where the ray start + t*direction (t > 0) meets the ellipse."""
    (x, y), (u, v) = start, direction
    qa = (u / a) ** 2 + (v / b) ** 2
    qb = 2 * (x * u / a ** 2 + y * v / b ** 2)
    qc = (x / a) ** 2 + (y / b) ** 2 - 1
    t = (-qb + math.sqrt(qb * qb - 4 * qa * qc)) / (2 * qa)
    return (x + t * u, y + t * v)


def distance_to_line(point, start, direction):
    """Distance from a point to the line through start with this direction."""
    dx, dy = point[0] - start[0], point[1] - start[1]
    return abs(dx * direction[1] - dy * direction[0]) / math.hypot(*direction)


def main():
    p = 1.0
    print(f"Parabola y = x^2/4, focus (0, {p:g}): reflected vertical rays cross")
    worst = 0.0
    for x0 in (-4, -3, -2, -1, 0.5, 1, 2, 3, 4):
        y = parabola_axis_crossing(p, x0)
        worst = max(worst, abs(y - p))
        print(f"  ray at x = {x0:4g} crosses the axis at y = {y:.15f}")
    print(f"  largest miss: {worst:.1e}")
    a, b = 5.0, 3.0
    c = math.sqrt(a * a - b * b)
    f1, f2 = (-c, 0.0), (c, 0.0)
    miss = sum_err = 0.0
    for k in range(12):
        angle = 2 * math.pi * (k + 0.5) / 12
        hit = ellipse_hit(a, b, f1, (math.cos(angle), math.sin(angle)))
        normal = (hit[0] / a ** 2, hit[1] / b ** 2)
        out = reflect((hit[0] - f1[0], hit[1] - f1[1]), normal)
        miss = max(miss, distance_to_line(f2, hit, out))
        sum_err = max(sum_err, abs(math.dist(hit, f1) + math.dist(hit, f2) - 2 * a))
    print("Ellipse x^2/25 + y^2/9 = 1, foci (-4, 0) and (4, 0), 12 rays from")
    print(f"(-4, 0): largest distance of a reflected ray from (4, 0): {miss:.1e}")
    print(f"  largest error in PF1 + PF2 = 2a = 10 at the points hit: "
          f"{sum_err:.1e}")
    print()
    print("Epistemic status: numerical evidence. Each ray is traced in floating")
    print("point, so 'through the focus' means within about 1e-15; only 21 rays")
    print("were traced. The reflective properties are theorems proved in the")
    print("lesson (and, for the parabola, checked in Lean).")


if __name__ == "__main__":
    main()
