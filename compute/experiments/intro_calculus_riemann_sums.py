"""Riemann sums for the area under y = x^2, computed exactly.

With fractions there is no rounding at all: the right Riemann sum of x^2 on
[0, 1] with n strips is exactly (n + 1)(2n + 1)/(6n^2), its error is exactly
1/(2n) + 1/(6n^2), and the midpoint sum misses 1/3 by exactly 1/(12n^2). The
fundamental theorem (via SymPy) gives the limit 1/3 at once. A last check
shows that integrals are signed: midpoint sums of sin on [0, 2 pi] tend to 0.
"""

import math
from fractions import Fraction

import sympy

EXPERIMENT = {
    "id": "intro_calculus_riemann_sums",
    "title": "Riemann sums for the parabola, exactly",
    "evidence": ["exact", "exhaustive-finite", "symbolic", "numerical"],
    "lessons": ["intro-calculus"],
    "summary": (
        "Computes left, right and midpoint Riemann sums of x^2 on [0, 1] in exact "
        "rational arithmetic, confirms the closed form (n + 1)(2n + 1)/(6n^2) for "
        "every n up to 200 and the exact errors 1/(2n) + 1/(6n^2) and -1/(12n^2), "
        "compares with the antiderivative x^3/3 (SymPy), and shows signed area "
        "for sin on [0, 2 pi] numerically."
    ),
    "packages": ["sympy"],
}


def riemann_sum(f, a, b, n, rule="right"):
    """Sum of n strips of width (b - a)/n; heights at the left end, right
    end or midpoint of each strip. Exact when f, a, b are rational."""
    if n < 1:
        raise ValueError("n must be at least 1")
    offset = {"left": Fraction(0), "right": Fraction(1), "midpoint": Fraction(1, 2)}
    if rule not in offset:
        raise ValueError("rule must be left, right or midpoint")
    width = (b - a) / n
    return sum(f(a + (k + offset[rule]) * width) for k in range(n)) * width


def square(x):
    """f(x) = x^2."""
    return x * x


def right_closed_form(n):
    """(n + 1)(2n + 1) / (6 n^2), the right sum of x^2 on [0, 1]."""
    return Fraction((n + 1) * (2 * n + 1), 6 * n * n)


def antiderivative_check():
    """SymPy: an antiderivative of x^2 and the integral over [0, 1]."""
    x = sympy.symbols("x")
    return sympy.integrate(x ** 2, x), sympy.integrate(x ** 2, (x, 0, 1))


def main():
    zero, one = Fraction(0), Fraction(1)
    third = Fraction(1, 3)
    agree = all(
        riemann_sum(square, zero, one, n) == right_closed_form(n)
        for n in range(1, 201)
    )
    print(f"Right sum = (n+1)(2n+1)/(6n^2) exactly for n = 1..200: {agree}")
    print()
    print("   n   left sum      right sum     midpoint      right - 1/3")
    for n in [1, 2, 4, 10, 100]:
        left = riemann_sum(square, zero, one, n, "left")
        right = riemann_sum(square, zero, one, n, "right")
        mid = riemann_sum(square, zero, one, n, "midpoint")
        print(f"{n:4d}   {float(left):.8f}    {float(right):.8f}    "
              f"{float(mid):.8f}    {str(right - third)}")
    n = 100
    err_right = riemann_sum(square, zero, one, n) - third
    err_mid = riemann_sum(square, zero, one, n, "midpoint") - third
    print(f"n = 100: right error = 1/(2n) + 1/(6n^2)? "
          f"{err_right == Fraction(1, 2 * n) + Fraction(1, 6 * n * n)}")
    print(f"n = 100: midpoint error = -1/(12n^2)? "
          f"{err_mid == Fraction(-1, 12 * n * n)}")
    print()
    anti, area = antiderivative_check()
    print(f"SymPy: antiderivative {anti}, so the area is F(1) - F(0) = {area}")
    print()
    signed = riemann_sum(math.sin, 0.0, 2 * math.pi, 1000, "midpoint")
    above = riemann_sum(math.sin, 0.0, math.pi, 1000, "midpoint")
    print(f"sin on [0, 2pi], 1000 strips: |midpoint sum| < 1e-12? "
          f"{abs(signed) < 1e-12}")
    print(f"Signed area cancels: the part above the axis alone is {above:.6f}")
    print("(the exact value of that part is 2).")
    print()
    print("Epistemic status: the fraction sums are exact and the closed form")
    print("is checked for n = 1..200 only (the lesson proves it for all n);")
    print("SymPy's integral is symbolic; the sine sums are floating point.")


if __name__ == "__main__":
    main()
