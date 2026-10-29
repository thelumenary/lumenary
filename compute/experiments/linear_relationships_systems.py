"""Linear relationships in tables, and systems of two linear equations.

Part 1 decides, with exact fractions, whether a table of values comes from a
linear relationship y = m*x + b (constant slope between all pairs of
consecutive points) and whether it is proportional (b = 0). Part 2 solves
the lesson's systems by elimination and checks each solution. Part 3 goes
through EVERY system a*x + b*y = e, c*x + d*y = f with all six coefficients
in -2..2 (15,625 systems) and sorts them into one solution, no solution and
infinitely many - finding no other possibility, as the lesson proves.
"""

from fractions import Fraction as F
from itertools import product

EXPERIMENT = {
    "id": "linear_relationships_systems",
    "title": "Linear tables and systems: one, none or infinitely many",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["linear-relationships"],
    "summary": (
        "Tests tables of values for a constant slope with exact fractions and "
        "recovers y = mx + b; solves the lesson's systems of two equations by "
        "elimination and checks the answers; and classifies all 15,625 systems "
        "with coefficients in -2..2 into one solution, no solution or "
        "infinitely many, checking every unique solution by substitution."
    ),
    "packages": [],
}

#: name -> list of (x, y) pairs
TABLES = {
    "taxi fare (km, soles)": [(0, 5), (1, 7), (2, 9), (5, 15)],
    "Celsius -> Fahrenheit": [(-40, -40), (0, 32), (25, 77), (100, 212)],
    "rice, kg -> rupees": [(1, 60), (2, 120), (5, 300), (8, 480)],
    "square: side -> area": [(1, 1), (2, 4), (3, 9), (4, 16)],
}

#: name -> (a, b, e, c, d, f) meaning a*x + b*y = e and c*x + d*y = f
SYSTEMS = {
    "chickens and rabbits": (1, 1, 35, 2, 4, 94),
    "y = 1.8x + 32, y = x": (F(-9, 5), 1, 32, -1, 1, 0),
    "x + y = 3, 2x + 2y = 10": (1, 1, 3, 2, 2, 10),
    "x + 2y = 4, 2x + 4y = 8": (1, 2, 4, 2, 4, 8),
}


def slope(p, q):
    """Exact slope between points p and q (with different x-coordinates)."""
    (x1, y1), (x2, y2) = p, q
    if x1 == x2:
        raise ValueError("vertical: slope undefined")
    return F(y2 - y1) / F(x2 - x1)


def linear_fit(points):
    """Return (m, b) if all points lie on one line y = m*x + b, else None."""
    slopes = {slope(p, q) for p, q in zip(points, points[1:])}
    if len(slopes) != 1:
        return None
    m = slopes.pop()
    x0, y0 = points[0]
    return m, F(y0) - m * x0


def line_text(m, b):
    """Readable equation y = mx + b, e.g. 'y = (9/5)x + 32' or 'y = 60x'."""
    slope_part = f"{m}x" if m.denominator == 1 else f"({m})x"
    if b == 0:
        return f"y = {slope_part}"
    sign = "+" if b > 0 else "-"
    return f"y = {slope_part} {sign} {abs(b)}"


def classify(a, b, e, c, d, f):
    """Classify a*x + b*y = e, c*x + d*y = f.

    Returns ("one", (x, y)), ("none", None) or ("infinite", None).
    """
    det = F(a) * d - F(b) * c
    if det != 0:
        x = (F(e) * d - F(b) * f) / det
        y = (F(a) * f - F(e) * c) / det
        return "one", (x, y)
    if a == b == c == d == 0:
        return ("infinite", None) if e == f == 0 else ("none", None)
    # Rank 1: consistent exactly when the augmented minors vanish too.
    if F(a) * f - F(c) * e == 0 and F(b) * f - F(d) * e == 0:
        return "infinite", None
    return "none", None


def check(a, b, e, c, d, f, x, y):
    """Does (x, y) satisfy both equations exactly?"""
    return a * x + b * y == e and c * x + d * y == f


def census(values):
    """Classify every system with all six coefficients in ``values``."""
    counts = {"one": 0, "none": 0, "infinite": 0}
    bad = 0
    for a, b, e, c, d, f in product(values, repeat=6):
        kind, sol = classify(a, b, e, c, d, f)
        counts[kind] += 1
        if kind == "one" and not check(a, b, e, c, d, f, *sol):
            bad += 1
    return counts, bad


def main():
    print("1. Is the table linear (one slope between consecutive points)?")
    for name, points in TABLES.items():
        fit = linear_fit(points)
        if fit is None:
            print(f"   {name:<23} not linear: slopes vary")
        else:
            m, b = fit
            kind = "proportional" if b == 0 else "linear, not proportional"
            print(f"   {name:<23} {line_text(m, b)}   ({kind})")
    print()
    print("2. Systems solved by elimination")
    for name, coeffs in SYSTEMS.items():
        kind, sol = classify(*coeffs)
        if kind == "one":
            ok = "checks" if check(*coeffs, *sol) else "FAILS"
            text = f"x = {sol[0]}, y = {sol[1]}  ({ok})"
        else:
            text = {"none": "no solution", "infinite": "infinitely many"}[kind]
        print(f"   {name:<24} {text}")
    print()
    counts, bad = census(range(-2, 3))
    total = sum(counts.values())
    print(f"3. All {total} systems with coefficients in -2..2:")
    for kind in ("one", "none", "infinite"):
        share = 100 * counts[kind] / total
        print(f"   {kind:<9} solution(s): {counts[kind]:>6}  ({share:.1f}%)")
    print(f"   unique solutions failing the substitution check: {bad}")
    print()
    print("Epistemic status: parts 1 and 2 are exact rational arithmetic, and")
    print("every solution is checked by substitution. Part 3 is an exhaustive")
    print("check of finitely many systems; the lesson proves for ALL systems")
    print("that one, none and infinitely many are the only possibilities.")


if __name__ == "__main__":
    main()
