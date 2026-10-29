"""Truncation error against rounding error, and when error bounds fail.

Part 1: the forward difference (f(x + h) - f(x))/h approximates f'(x) with a
truncation error about h|f''|/2, but rounding errors in f contribute about
2u|f|/h. As h shrinks the total error first falls and then rises again, with
its minimum near h = sqrt(u) = 1e-8; the central difference does better,
with its minimum near u^(1/3) = 1e-5.

Part 2: the composite trapezoid and Simpson rules on two integrands. For the
periodic function e^(cos x) on [0, 2 pi] the trapezoid rule converges far
faster than its O(h^2) bound suggests. For sqrt(x) on [0, 1], whose
derivatives blow up at 0, both rules converge only like h^1.5: the smoothness
hypotheses of the error theorems are not met.
"""

import math

EXPERIMENT = {
    "id": "numerical_methods_differentiation",
    "title": "Truncation versus rounding, and smoothness in quadrature",
    "evidence": ["numerical"],
    "lessons": ["numerical-methods"],
    "summary": (
        "Measures the error of forward and central difference quotients for the "
        "derivative of sin at 1 as h shrinks from 1e-1 to 1e-13, showing the "
        "V shape where rounding error takes over; then measures trapezoid and "
        "Simpson errors for e^cos(x) on [0, 2 pi] (fast, because periodic) and "
        "for sqrt(x) on [0, 1] (slow, because not smooth at 0)."
    ),
    "packages": [],
}


def forward_difference(f, x, h):
    """(f(x + h) - f(x)) / h."""
    return (f(x + h) - f(x)) / h


def central_difference(f, x, h):
    """(f(x + h) - f(x - h)) / (2h)."""
    return (f(x + h) - f(x - h)) / (2 * h)


def trapezoid(f, a, b, n):
    """Composite trapezoid rule with n strips."""
    h = (b - a) / n
    return h * (0.5 * f(a) + sum(f(a + i * h) for i in range(1, n)) + 0.5 * f(b))


def simpson(f, a, b, n):
    """Composite Simpson rule with n strips (n even)."""
    if n <= 0 or n % 2:
        raise ValueError("Simpson's rule needs a positive even number of strips")
    h = (b - a) / n
    odd = sum(f(a + i * h) for i in range(1, n, 2))
    even = sum(f(a + i * h) for i in range(2, n, 2))
    return h / 3 * (f(a) + 4 * odd + 2 * even + f(b))


def bessel_i0(x, terms=30):
    """Modified Bessel function I0(x) = sum (x/2)^(2k) / (k!)^2."""
    return sum((x / 2) ** (2 * k) / math.factorial(k) ** 2 for k in range(terms))


def main():
    exact = math.cos(1.0)
    print("Derivative of sin at 1: errors of difference quotients")
    print("      h     forward    central")
    for k in range(1, 14, 2):
        h = 10.0 ** (-k)
        fe = abs(forward_difference(math.sin, 1.0, h) - exact)
        ce = abs(central_difference(math.sin, 1.0, h) - exact)
        print(f"  1e-{k:02d}  {fe:9.1e}  {ce:9.1e}")
    print()
    per_exact = 2 * math.pi * bessel_i0(1.0)
    print("Trapezoid errors for e^cos(x) on [0, 2 pi] (periodic):")
    for n in (2, 4, 8, 16):
        err = abs(trapezoid(lambda t: math.exp(math.cos(t)), 0, 2 * math.pi, n)
                  - per_exact)
        print(f"  n = {n:2d}: {err:.1e}")
    print("sqrt(x) on [0, 1] (exact 2/3): errors and observed orders")
    print("    n   trapezoid   Simpson")
    prev = None
    for n in (16, 64, 256, 1024):
        te = abs(trapezoid(math.sqrt, 0, 1, n) - 2 / 3)
        se = abs(simpson(math.sqrt, 0, 1, n) - 2 / 3)
        rate = "" if prev is None else (
            f"   orders {math.log(prev[0] / te, 4):.2f},"
            f" {math.log(prev[1] / se, 4):.2f}")
        print(f"  {n:4d}  {te:9.2e}  {se:9.2e}{rate}")
        prev = (te, se)
    print()
    print("Epistemic status: floating-point measurements for a few functions.")
    print("They agree with the error analysis (truncation ~ h or h^2, rounding")
    print("~ u/h) and show that the O(h^2) and O(h^4) quadrature bounds need")
    print("bounded derivatives; they do not prove any rate.")


if __name__ == "__main__":
    main()
