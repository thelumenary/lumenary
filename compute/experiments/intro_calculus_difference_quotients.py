"""Derivatives as limits of difference quotients - and the limits of floats.

For f(x) = x^2 the difference quotient ((a + h)^2 - a^2)/h equals 2a + h
exactly (checked with fractions), so it tends to 2a. For f = sin at a = 1 the
quotient tends to cos 1, but in floating point the error first shrinks like h
(the mathematics) and then grows again like 1e-16/h (rounding: subtracting two
nearly equal numbers). SymPy computes the limit and the power rule exactly.
"""

import math
from fractions import Fraction

import sympy

EXPERIMENT = {
    "id": "intro_calculus_difference_quotients",
    "title": "Difference quotients: exact, numerical and symbolic",
    "evidence": ["exact", "numerical", "symbolic"],
    "lessons": ["intro-calculus"],
    "summary": (
        "Shows with exact fractions that the difference quotient of x^2 at a is "
        "2a + h; tabulates floating-point forward and central quotients of sin "
        "at 1 against cos 1 for h = 1e-1 ... 1e-13, where rounding error "
        "eventually wins; and lets SymPy compute the limit and the derivative "
        "of x^n symbolically."
    ),
    "packages": ["sympy"],
}


def forward_quotient(f, a, h):
    """(f(a + h) - f(a)) / h, the slope of a secant line."""
    if h == 0:
        raise ValueError("h must be non-zero")
    return (f(a + h) - f(a)) / h


def central_quotient(f, a, h):
    """(f(a + h) - f(a - h)) / (2h), a symmetric secant slope."""
    if h == 0:
        raise ValueError("h must be non-zero")
    return (f(a + h) - f(a - h)) / (2 * h)


def square(x):
    """f(x) = x^2."""
    return x * x


def quotient_errors(exponents):
    """Rows (h, forward error, central error) for sin at 1 against cos 1."""
    exact = math.cos(1.0)
    rows = []
    for k in exponents:
        h = 10.0 ** (-k)
        fwd = abs(forward_quotient(math.sin, 1.0, h) - exact)
        cen = abs(central_quotient(math.sin, 1.0, h) - exact)
        rows.append((h, fwd, cen))
    return rows


def symbolic_results():
    """SymPy's limit of the sine quotient and derivative of x^n."""
    x, h = sympy.symbols("x h")
    n = sympy.symbols("n", positive=True, integer=True)
    lim = sympy.limit((sympy.sin(1 + h) - sympy.sin(1)) / h, h, 0)
    deriv = sympy.simplify(sympy.diff(x ** n, x))
    return lim, deriv


def main():
    print("Exact fractions: ((a + h)^2 - a^2)/h for a = 3")
    for h in [Fraction(1, 10), Fraction(1, 1000), Fraction(-1, 10 ** 6)]:
        q = forward_quotient(square, Fraction(3), h)
        print(f"  h = {str(h):>10}:  quotient = {q}  (= 2a + h)")
    print()
    print("Floats: sin at a = 1, compared with cos 1")
    print("      h      forward error   central error")
    for h, fwd, cen in quotient_errors(range(1, 14, 2)):
        print(f"  {h:8.0e}     {fwd:.2e}        {cen:.2e}")
    print("The forward error falls like h, the central one like h^2, until")
    print("rounding (about 1e-16 / h) takes over for tiny h.")
    print()
    lim, deriv = symbolic_results()
    print(f"SymPy: limit of (sin(1 + h) - sin 1)/h as h -> 0 is {lim}")
    print(f"SymPy: d/dx x^n = {deriv}")
    print()
    print("Epistemic status: the fraction rows are exact; the float table is")
    print("numerical evidence affected by rounding, so it can suggest but")
    print("never prove a limit; the SymPy results are symbolic computations.")
    print("The lesson's proofs establish the derivatives for every a and n.")


if __name__ == "__main__":
    main()
