"""Measuring angles with a computer: triangles, quadrilaterals and long arms.

The program draws many random triangles with corners on a square grid and
measures each angle (in degrees) from the coordinates, the way a very
careful protractor would. It adds up the three angles of every triangle and
the four angles of random convex quadrilaterals. It also lengthens the arms
of an angle to show the angle does not change, and sorts the triangles into
acute, right and obtuse exactly, using whole-number arithmetic.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math
import random
import textwrap

EXPERIMENT = {
    "id": "area_angles_triangle_sums",
    "title": "Measuring the angles of many triangles",
    "evidence": ["numerical", "experimental"],
    "lessons": ["area-angles"],
    "summary": (
        "Measures the angles of 1000 random grid triangles and 300 random "
        "convex quadrilaterals from their coordinates. The sums are 180 and "
        "360 degrees up to rounding errors of about 1e-12 degrees. Also shows "
        "that longer arms do not change an angle. Numerical evidence for "
        "these shapes only; the proof is in the lesson."
    ),
    "packages": [],
}


def angle_at(corner, p, q):
    """The angle at `corner` between the arms towards p and q, in degrees."""
    ux, uy = p[0] - corner[0], p[1] - corner[1]
    vx, vy = q[0] - corner[0], q[1] - corner[1]
    cos = (ux * vx + uy * vy) / (math.hypot(ux, uy) * math.hypot(vx, vy))
    return math.degrees(math.acos(max(-1.0, min(1.0, cos))))


def triangle_angles(a, b, c):
    """The three angles of triangle abc, in degrees."""
    return angle_at(a, b, c), angle_at(b, c, a), angle_at(c, a, b)


def cross(o, p, q):
    """Twice the signed area of triangle opq (0 means the points line up)."""
    return (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0])


def is_convex(quad):
    """True if the corners go round a convex quadrilateral in order."""
    signs = [cross(quad[i], quad[(i + 1) % 4], quad[(i + 2) % 4])
             for i in range(4)]
    return all(s > 0 for s in signs) or all(s < 0 for s in signs)


def kind(a, b, c):
    """'acute', 'right' or 'obtuse', decided exactly with whole numbers.

    The angle at a corner is more than 90 degrees exactly when the dot
    product of its two arms is negative, and exactly 90 when it is zero.
    """
    dots = []
    for o, p, q in ((a, b, c), (b, c, a), (c, a, b)):
        dots.append((p[0] - o[0]) * (q[0] - o[0])
                    + (p[1] - o[1]) * (q[1] - o[1]))
    if min(dots) < 0:
        return "obtuse"
    return "right" if min(dots) == 0 else "acute"


def random_point(rng):
    """A random point on the 21 x 21 grid of whole-number points."""
    return (rng.randint(0, 20), rng.randint(0, 20))


def random_triangles(rng, n):
    """n random triangles whose corners do not lie on one line."""
    out = []
    while len(out) < n:
        a, b, c = (random_point(rng) for _ in range(3))
        if cross(a, b, c) != 0:
            out.append((a, b, c))
    return out


def random_convex_quads(rng, n):
    """n random convex quadrilaterals with corners in order."""
    out = []
    while len(out) < n:
        quad = [random_point(rng) for _ in range(4)]
        if is_convex(quad):
            out.append(quad)
    return out


def main():
    rng = random.Random(2024)
    triangles = random_triangles(rng, 1000)
    sums = [sum(triangle_angles(*t)) for t in triangles]
    print("Three of the 1000 random triangles:")
    for t in triangles[:3]:
        angles = triangle_angles(*t)
        shown = " + ".join(f"{x:5.1f}" for x in angles)
        print(f"  corners {t}: {shown} = {sum(angles):.1f}")
    worst = max(abs(s - 180) for s in sums)
    print(f"All 1000 sums lie within {worst:.1e} degrees of 180.")
    kinds = [kind(*t) for t in triangles]
    print("Sorted exactly: " + ", ".join(
        f"{k} {kinds.count(k)}" for k in ("acute", "right", "obtuse")))
    print()
    quads = random_convex_quads(rng, 300)
    q_sums = [sum(angle_at(q[i], q[i - 1], q[(i + 1) % 4]) for i in range(4))
              for q in quads]
    worst_q = max(abs(s - 360) for s in q_sums)
    print(f"300 convex quadrilaterals: sums within {worst_q:.1e} of 360.")
    print()
    print("Longer arms, same angle (corner at (0, 0)):")
    for k in (1, 2, 10, 100):
        a = angle_at((0, 0), (3 * k, 1 * k), (1 * k, 2 * k))
        print(f"  arms {k:>3} times as long: {a:.6f} degrees")
    print()
    print(textwrap.fill(
        "Epistemic status: numerical evidence. Each angle is computed in "
        "floating-point arithmetic, so sums are off by tiny rounding errors; "
        "1300 shapes are not all shapes. The sorting into acute, right and "
        "obtuse is exact. Why every flat triangle has angle sum 180 degrees "
        "is explained by the proof in the lesson, not by this program.",
        width=78,
    ))


if __name__ == "__main__":
    main()
