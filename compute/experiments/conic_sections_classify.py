"""Classify second-degree equations Ax^2 + Bxy + Cy^2 + Dx + Ey + F = 0.

Uses three integer invariants: the discriminant B^2 - 4AC of the quadratic
part, the determinant of the 3 x 3 symmetric matrix of the equation (zero
exactly for degenerate cases such as pairs of lines), and, for degenerate
parabolic cases, a 2 x 2 invariant that separates parallel lines, a double
line and the empty set. Everything is exact integer arithmetic. We classify
some famous examples and then every equation with coefficients from -2 to 2.
"""

import itertools
from collections import Counter

EXPERIMENT = {
    "id": "conic_sections_classify",
    "title": "Which curve is this second-degree equation?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["conic-sections"],
    "summary": (
        "Classifies equations Ax^2 + Bxy + Cy^2 + Dx + Ey + F = 0 as ellipse, "
        "circle, parabola, hyperbola or a degenerate case (point, lines, empty) "
        "from exact integer invariants, for named examples and for all 15,500 "
        "equations with coefficients in -2..2 and a non-zero quadratic part. "
        "Exact computation of a standard classification, not a proof of it."
    ),
    "packages": [],
}


def det3(m):
    """Determinant of a 3 x 3 matrix given as a list of rows."""
    (a, b, c), (d, e, f), (g, h, i) = m
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def classify(A, B, C, D, E, F):
    """Name the set of real solutions of Ax^2+Bxy+Cy^2+Dx+Ey+F = 0.

    Works with twice the symmetric matrix, so every entry is an integer.
    """
    if A == B == C == 0:
        raise ValueError("not a second-degree equation")
    disc = B * B - 4 * A * C
    delta = det3([[2 * A, B, D], [B, 2 * C, E], [D, E, 2 * F]])
    if delta != 0:
        if disc < 0:
            if (A + C) * delta > 0:
                return "empty"
            return "circle" if A == C and B == 0 else "ellipse"
        return "parabola" if disc == 0 else "hyperbola"
    if disc < 0:
        return "point"
    if disc > 0:
        return "two crossing lines"
    k = (4 * A * F - D * D) + (4 * C * F - E * E)
    if k < 0:
        return "two parallel lines"
    return "one line" if k == 0 else "empty"


EXAMPLES = [
    ("x^2 + y^2 - 2x + 4y + 1 = 0", (1, 0, 1, -2, 4, 1)),
    ("3x^2 + 2xy + 3y^2 - 8 = 0", (3, 2, 3, 0, 0, -8)),
    ("x^2 - 4y = 0", (1, 0, 0, 0, -4, 0)),
    ("xy - 1 = 0", (0, 1, 0, 0, 0, -1)),
    ("x^2 + y^2 + 1 = 0", (1, 0, 1, 0, 0, 1)),
    ("x^2 + y^2 = 0", (1, 0, 1, 0, 0, 0)),
    ("x^2 - y^2 = 0", (1, 0, -1, 0, 0, 0)),
    ("x^2 - 1 = 0", (1, 0, 0, 0, 0, -1)),
    ("x^2 - 2xy + y^2 = 0", (1, -2, 1, 0, 0, 0)),
    ("x^2 + 1 = 0", (1, 0, 0, 0, 0, 1)),
]


def main():
    print("Named examples:")
    for text, coeffs in EXAMPLES:
        print(f"  {text:<30} {classify(*coeffs)}")
    counts = Counter()
    for coeffs in itertools.product(range(-2, 3), repeat=6):
        if coeffs[:3] != (0, 0, 0):
            counts[classify(*coeffs)] += 1
    total = sum(counts.values())
    print(f"All {total} equations with coefficients in -2..2:")
    for name, n in counts.most_common():
        print(f"  {name:<20} {n:6d}  ({100 * n / total:4.1f}%)")
    print("Parabolas need B^2 = 4AC exactly, a borderline case, so they are")
    print("rare; a random small change turns one into an ellipse or hyperbola.")
    print()
    print("Epistemic status: exact integer computation of the standard")
    print("classification by invariants. The classification itself (that")
    print("these invariants decide the type) is a theorem explained in the")
    print("lesson; this program applies it, it does not prove it.")


if __name__ == "__main__":
    main()
