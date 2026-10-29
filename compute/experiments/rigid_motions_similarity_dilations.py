"""Dilations: what changes and what stays the same, measured on 200 triangles.

The experiment makes 200 triangles with seeded random whole-number vertices
and applies dilations with scale factors 1/2, 2 and 3 (centre the origin, and
also centre (2, -1)). With exact fractions it checks that every squared side
length is multiplied by k^2, every area by k^2, and every side keeps its
direction (its slope). It also measures the angles numerically and checks they
do not change. A horizontal-only stretch is the non-example: it changes
angles. Finally it uses similar triangles to measure a tree from its shadow.
"""

import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "rigid_motions_similarity_dilations",
    "title": "Dilations change sizes, not shapes",
    "evidence": ["exact", "numerical"],
    "lessons": ["rigid-motions-similarity"],
    "summary": (
        "Applies dilations with k = 1/2, 2 and 3 to 200 seeded random triangles "
        "and checks with exact fractions that squared lengths and areas are "
        "multiplied by k^2 and that side directions are kept; angles are measured "
        "numerically and do not change, unlike under a horizontal-only stretch. "
        "Evidence for these triangles; the lesson proves the general facts."
    ),
    "packages": [],
}


def dilate(p, k, centre=(0, 0)):
    """Dilation with the given centre and scale factor k."""
    cx, cy = centre
    return (cx + k * (p[0] - cx), cy + k * (p[1] - cy))


def stretch_x(p, k):
    """Non-example: stretch horizontally only, (x, y) -> (kx, y)."""
    return (k * p[0], p[1])


def sq_len(p, q):
    """Squared distance between two points."""
    return (q[0] - p[0]) ** 2 + (q[1] - p[1]) ** 2


def area(tri):
    """Area of a triangle by the shoelace formula (exact for fractions)."""
    (ax, ay), (bx, by), (cx, cy) = tri
    return Fraction(abs((bx - ax) * (cy - ay) - (cx - ax) * (by - ay))) / 2


def angles(tri):
    """The three angles of a triangle in degrees (numerical)."""
    out = []
    for i in range(3):
        a, b, c = tri[i], tri[(i + 1) % 3], tri[(i + 2) % 3]
        u = (b[0] - a[0], b[1] - a[1])
        v = (c[0] - a[0], c[1] - a[1])
        dot = u[0] * v[0] + u[1] * v[1]
        cos = dot / math.sqrt((u[0] ** 2 + u[1] ** 2) * (v[0] ** 2 + v[1] ** 2))
        out.append(math.degrees(math.acos(max(-1.0, min(1.0, float(cos))))))
    return out


def parallel(p, q, p2, q2):
    """True if segment p2q2 is parallel to (has the same direction as) pq."""
    return (q[0] - p[0]) * (q2[1] - p2[1]) == (q[1] - p[1]) * (q2[0] - p2[0])


def random_triangles(count, seed=1872):
    """Non-degenerate triangles with whole-number vertices from -9 to 9."""
    rng = random.Random(seed)
    tris = []
    while len(tris) < count:
        tri = [(rng.randint(-9, 9), rng.randint(-9, 9)) for _ in range(3)]
        if area(tri) != 0:
            tris.append(tri)
    return tris


def check(tris, k, centre):
    """Counts of triangles passing each test for one dilation."""
    lengths = areas = directions = angle_ok = 0
    for tri in tris:
        img = [dilate(p, k, centre) for p in tri]
        sides = [(i, (i + 1) % 3) for i in range(3)]
        lengths += all(sq_len(img[i], img[j]) == k * k * sq_len(tri[i], tri[j])
                       for i, j in sides)
        areas += area(img) == k * k * area(tri)
        directions += all(parallel(tri[i], tri[j], img[i], img[j])
                          for i, j in sides)
        angle_ok += all(abs(x - y) < 1e-9
                        for x, y in zip(angles(tri), angles(img)))
    return lengths, areas, directions, angle_ok


def main():
    tris = random_triangles(200)
    print("200 random triangles; dilation results (number of triangles passing)")
    print(f"{'k':>4} {'centre':>8} {'len^2 x k^2':>12} {'area x k^2':>11}"
          f" {'parallel':>9} {'angles':>7}")
    for k in (Fraction(1, 2), Fraction(2), Fraction(3)):
        for centre in ((0, 0), (2, -1)):
            res = check(tris, k, centre)
            print(f"{str(k):>4} {str(centre):>8}" + f"{res[0]:>13}{res[1]:>12}"
                  f"{res[2]:>10}{res[3]:>8}")
    changed = sum(any(abs(x - y) > 1e-6 for x, y in
                      zip(angles(t), angles([stretch_x(p, 2) for p in t])))
                  for t in tris)
    print(f"Non-example: stretching x by 2 changed the angles of {changed} of"
          " 200 triangles.")
    print()
    pole, pole_shadow, tree_shadow = 1.5, 2.0, 12.0
    k = tree_shadow / pole_shadow
    print(f"Shadows: a {pole} m pole casts {pole_shadow} m, a tree {tree_shadow} m;"
          f" k = {k:g},")
    print(f"so the tree is {k:g} x {pole} = {k * pole:g} m tall (similar triangles).")
    print()
    print("Epistemic status: lengths, areas and directions are checked exactly")
    print("for these 1200 triangle-dilation pairs; angles are compared")
    print("numerically. This is evidence, not proof; the lesson proves that every")
    print("dilation behaves this way.")


if __name__ == "__main__":
    main()
