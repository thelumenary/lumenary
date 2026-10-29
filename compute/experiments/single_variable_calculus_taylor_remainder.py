"""Taylor polynomials: the Lagrange error bound against the actual error.

Taylor's theorem says f(x) = T_n(x) + R_n(x) with
R_n(x) = f^(n+1)(xi) x^(n+1) / (n+1)! for some xi between 0 and x. Bounding
|f^(n+1)| gives a guaranteed error bound. This experiment computes Taylor
polynomials of exp and sin exactly (rational arithmetic), compares the actual
error (against the library functions) with the Lagrange bound, finds how many
terms of the series for e give ten correct digits, and shows Cauchy's flat
function exp(-1/x^2), whose Taylor polynomials at 0 are all zero.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "single_variable_calculus_taylor_remainder",
    "title": "Taylor polynomials: Lagrange bound versus actual error",
    "evidence": ["exact", "numerical"],
    "lessons": ["single-variable-calculus"],
    "summary": (
        "Computes Maclaurin polynomials of exp and sin exactly with fractions, "
        "compares their actual errors (measured against the floating-point "
        "library) with the Lagrange remainder bound for several degrees, finds "
        "the degree that guarantees ten digits of e, and evaluates Cauchy's flat "
        "function, whose Taylor polynomials at 0 are zero. Numerical evidence for "
        "particular x and n; Taylor's theorem is what guarantees the bound."
    ),
    "packages": [],
}


def exp_taylor(x, n):
    """Exact value of the Maclaurin polynomial sum_{k=0}^{n} x^k / k!."""
    if n < 0:
        raise ValueError("degree must be non-negative")
    x = Fraction(x)
    term = Fraction(1)
    total = Fraction(1)
    for k in range(1, n + 1):
        term = term * x / k
        total += term
    return total


def sin_taylor(x, n):
    """Exact value of the Maclaurin polynomial of sin of degree n."""
    if n < 0:
        raise ValueError("degree must be non-negative")
    x = Fraction(x)
    total = Fraction(0)
    for k in range(1, n + 1, 2):
        sign = -1 if (k - 1) // 2 % 2 else 1
        total += sign * x**k / math.factorial(k)
    return total


def exp_bound(x, n):
    """Lagrange bound on |exp(x) - T_n(x)|: e^max(x,0) |x|^(n+1) / (n+1)!.

    The unknown point xi lies between 0 and x, so e^xi <= e^max(x, 0).
    """
    return math.exp(max(x, 0)) * abs(x) ** (n + 1) / math.factorial(n + 1)


def sin_bound(x, n):
    """Lagrange bound on |sin(x) - T_n(x)|, using |sin^(m+1)| <= 1.

    For odd n the next coefficient of sin is zero, so T_n = T_(n+1) and the
    remainder of degree m = n + 1 gives a sharper bound.
    """
    m = n + 1 if n % 2 else n
    return abs(x) ** (m + 1) / math.factorial(m + 1)


def degree_for_e(tolerance):
    """Least n whose Lagrange bound 3/(n+1)! for |e - T_n(1)| is below tolerance."""
    n = 0
    while 3 / math.factorial(n + 1) >= tolerance:
        n += 1
    return n


def flat(x):
    """Cauchy's smooth function: exp(-1/x^2) for x != 0, and 0 at 0."""
    return 0.0 if x == 0 else math.exp(-1 / x**2)


def error_rows(f, poly, bound, x, degrees):
    """Rows (n, actual error, bound) for the given degrees."""
    rows = []
    for n in degrees:
        actual = abs(f(x) - float(poly(Fraction(x), n)))
        rows.append((n, actual, bound(x, n)))
    return rows


def main():
    cases = [
        ("exp", math.exp, exp_taylor, exp_bound, 1, [2, 4, 6, 8, 10]),
        ("exp", math.exp, exp_taylor, exp_bound, -2, [2, 4, 8, 12, 16]),
        ("sin", math.sin, sin_taylor, sin_bound, 0.3, [1, 3, 5, 7]),
    ]
    print("Maclaurin polynomials: actual error versus Lagrange bound")
    for name, f, poly, bound, x, degrees in cases:
        print(f"f = {name}, x = {x}")
        print("   n    actual error   Lagrange bound   bound / actual")
        for n, actual, b in error_rows(f, poly, bound, x, degrees):
            print(f"  {n:2d}    {actual:.3e}      {b:.3e}        {b / actual:7.2f}")
    n = degree_for_e(1e-10)
    print(f"Degree n with 3/(n+1)! < 1e-10 (ten digits of e): n = {n}")
    approx = float(exp_taylor(1, n))
    print(f"  T_{n}(1) = {approx:.12f}, error {abs(math.e - approx):.1e}")
    print("Cauchy's flat function: every T_n at 0 is the zero polynomial")
    for x in [0.5, 0.2, 0.1]:
        print(f"  x = {x}: f(x) = {flat(x):.3e} = error of T_n for every n")
    print()
    print("Epistemic status: the polynomial values are exact rationals; the")
    print("errors are measured against floating-point exp and sin, so they are")
    print("numerical evidence for these x and n only. That the bound holds for")
    print("every x and n is Taylor's theorem; that exp is the sum of its series")
    print("is the lesson's corollary. For the flat function no degree helps.")


if __name__ == "__main__":
    main()
