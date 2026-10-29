"""Testing the converse: build every whole-number triangle and measure it.

For every triangle with whole-number sides a <= b <= c <= 20, the experiment
builds it in the coordinate plane: C = (0, 0), B = (a, 0), and A = (x, y)
with CA = b and BA = c. Subtracting the two distance equations gives the exact
value x = (a^2 + b^2 - c^2) / (2a), computed with fractions. The angle at C is
then measured numerically (like a protractor) and compared with the test
"compare a^2 + b^2 with c^2". The sign of x is the whole story: x = 0 means a
right angle at C, x > 0 an acute one, x < 0 an obtuse one.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "pythagorean_theorem_converse",
    "title": "Right, acute or obtuse? Every triangle with sides up to 20",
    "evidence": ["exact", "numerical", "exhaustive-finite"],
    "lessons": ["pythagorean-theorem"],
    "summary": (
        "Builds every triangle with whole-number sides up to 20 in coordinates, "
        "finds the exact x-coordinate (a^2 + b^2 - c^2) / (2a) of its top vertex, "
        "measures the angle opposite the longest side numerically, and checks "
        "that the angle is 90, under 90 or over 90 degrees exactly when a^2 + b^2 "
        "equals, exceeds or falls short of c^2. Exhaustive for these triangles."
    ),
    "packages": [],
}


def triangles(limit):
    """All (a, b, c) with a <= b <= c <= limit satisfying a + b > c."""
    return [(a, b, c) for c in range(1, limit + 1) for b in range(1, c + 1)
            for a in range(1, b + 1) if a + b > c]


def apex(a, b, c):
    """Exact x and approximate y of A, where C = (0, 0) and B = (a, 0)."""
    x = Fraction(a * a + b * b - c * c, 2 * a)
    y = math.sqrt(b * b - x * x)
    return x, y


def angle_at_c(a, b, c):
    """The angle ACB in degrees, measured from the coordinates."""
    x, y = apex(a, b, c)
    return math.degrees(math.atan2(y, float(x)))


def pythagoras_test(a, b, c):
    """'right', 'acute' or 'obtuse' by comparing a^2 + b^2 with c^2."""
    s, t = a * a + b * b, c * c
    return "right" if s == t else ("acute" if s > t else "obtuse")


def measured_type(a, b, c, tol=1e-9):
    """'right', 'acute' or 'obtuse' from the measured angle at C."""
    ang = angle_at_c(a, b, c)
    if abs(ang - 90) < tol:
        return "right"
    return "acute" if ang < 90 else "obtuse"


def main():
    tris = triangles(20)
    counts = {"right": 0, "acute": 0, "obtuse": 0}
    agree = 0
    for t in tris:
        kind = pythagoras_test(*t)
        counts[kind] += 1
        agree += kind == measured_type(*t)
    print(f"Triangles with whole-number sides a <= b <= c <= 20: {len(tris)}")
    print(f"  by the test a^2 + b^2 vs c^2: {counts['right']} right, "
          f"{counts['acute']} acute, {counts['obtuse']} obtuse")
    print(f"  measured angle at C agrees with the test: {agree} of {len(tris)}")
    rights = [t for t in tris if pythagoras_test(*t) == "right"]
    print("  the right ones:")
    print("    " + ", ".join(str(t) for t in rights))
    print()
    print("Three examples (x is exact, the angle is measured):")
    for t in [(3, 4, 5), (5, 6, 8), (4, 5, 6)]:
        x, _ = apex(*t)
        print(f"  sides {t}: x = {str(x):>6}, angle at C = "
              f"{angle_at_c(*t):7.3f} degrees ({pythagoras_test(*t)})")
    smallest = min((abs(angle_at_c(*t) - 90), t) for t in tris
                   if pythagoras_test(*t) != "right")
    print(f"Closest to 90 degrees without being right: {smallest[1]}, off by "
          f"{smallest[0]:.3f} degrees")
    print()
    print("Epistemic status: exhaustive over these 825 triangles. The x-coordinate")
    print("is exact (x = 0 exactly for the right triangles); the angles are")
    print("floating-point measurements, and an angle within 1e-9 degrees of 90")
    print("counts as right. Evidence for these triangles only: the converse is")
    print("proved in the lesson for every triangle.")


if __name__ == "__main__":
    main()
