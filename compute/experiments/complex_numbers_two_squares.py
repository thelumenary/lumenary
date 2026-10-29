"""Multiplying complex numbers multiplies sums of two squares.

For Gaussian integers z = a + bi (a, b whole numbers) the squared modulus
N(z) = a^2 + b^2 is a sum of two squares, and |zw|^2 = |z|^2 |w|^2 says that
(a^2 + b^2)(c^2 + d^2) = (ac - bd)^2 + (ad + bc)^2. The experiment checks this
exhaustively on a grid of Gaussian integers (exact integer arithmetic), then
uses complex multiplication to *produce* new sums of two squares, e.g.
65 = 5 * 13 = 1^2 + 8^2 = 4^2 + 7^2 from (1 + 2i)(2 + 3i) and (1 + 2i)(2 - 3i).
"""

import math

EXPERIMENT = {
    "id": "complex_numbers_two_squares",
    "title": "Complex multiplication and sums of two squares",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["complex-numbers"],
    "summary": (
        "Checks N(zw) = N(z) N(w) for all Gaussian integers z, w with "
        "coordinates in -6..6 (exact integers, 28561 pairs), then multiplies "
        "Gaussian integers to build sums of two squares: 5 * 13 = 65 = 1 + 64 "
        "= 16 + 49. The grid is evidence; the identity is proved by algebra."
    ),
    "packages": [],
}


def gauss_mul(z, w):
    """Product of Gaussian integers given as pairs (a, b) meaning a + bi."""
    (a, b), (c, d) = z, w
    return (a * c - b * d, a * d + b * c)


def norm(z):
    """N(a + bi) = a^2 + b^2, the squared modulus."""
    a, b = z
    return a * a + b * b


def grid(radius):
    """All Gaussian integers a + bi with |a|, |b| <= radius."""
    if radius < 0:
        raise ValueError("radius must be non-negative")
    values = range(-radius, radius + 1)
    return [(a, b) for a in values for b in values]


def check_multiplicative(radius):
    """Return (pairs checked, failures) for N(zw) == N(z) N(w) on the grid."""
    points = grid(radius)
    failures = [
        (z, w)
        for z in points
        for w in points
        if norm(gauss_mul(z, w)) != norm(z) * norm(w)
    ]
    return len(points) ** 2, failures


def two_square_reps(n):
    """All (a, b) with 0 <= a <= b and a^2 + b^2 = n."""
    reps = []
    for a in range(math.isqrt(n // 2) + 1):
        b2 = n - a * a
        b = math.isqrt(b2)
        if b * b == b2 and a <= b:
            reps.append((a, b))
    return reps


def normalise(z):
    """Sort |real|, |imag| so a representation reads (small, large)."""
    a, b = abs(z[0]), abs(z[1])
    return (min(a, b), max(a, b))


def show(z):
    """Write the pair (a, b) as the text a + bi (or a - bi)."""
    a, b = z
    sign = "-" if b < 0 else "+"
    return f"{a} {sign} {abs(b)}i"


def square(x):
    """x^2 as text, with brackets around negative x."""
    return f"({x})^2" if x < 0 else f"{x}^2"


def main():
    cases, failures = check_multiplicative(6)
    print("N(zw) = N(z)N(w) for all z, w with coordinates in -6..6:")
    print(f"  {cases} pairs checked, {len(failures)} failures")
    print()
    z, w = (1, 2), (2, 3)
    w_bar = (2, -3)
    for v in (w, w_bar):
        p = gauss_mul(z, v)
        print(f"({show(z)})({show(v)}) = {show(p)},  "
              f"N = {square(p[0])} + {square(p[1])} = {norm(p)}")
    print("So 5 * 13 = 65 has two representations:", two_square_reps(65))
    print()
    print("n   = a^2 + b^2   (all representations with 0 <= a <= b)")
    for n in [5, 13, 25, 65, 85, 325, 1105]:
        reps = two_square_reps(n)
        shown = ", ".join(f"{a}^2+{b}^2" for a, b in reps)
        print(f"{n:<5} {shown}")
    print("3, 7, 21 have none:", [two_square_reps(n) for n in (3, 7, 21)])
    print()
    print("Epistemic status: the grid check is exhaustive but finite; the")
    print("identity (a^2+b^2)(c^2+d^2) = (ac-bd)^2+(ad+bc)^2 is proved for all")
    print("numbers by expanding both sides (and in Lean). Which n are sums of")
    print("two squares is a theorem of Fermat and Euler, not shown here.")


if __name__ == "__main__":
    main()
