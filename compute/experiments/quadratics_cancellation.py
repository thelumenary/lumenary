"""When the quadratic formula goes wrong on a computer - and how Vieta saves it.

The roots of x^2 - Bx + 1 = 0 for large B are about B and 1/B. In
floating-point arithmetic the formula (B - sqrt(B^2 - 4))/2 for the small root
subtracts two nearly equal numbers, and most of its digits cancel. Vieta's
formula r1 * r2 = c/a gives the small root as 1/r1 with no cancellation. Exact
reference values come from 60-digit decimal arithmetic.
"""

from decimal import Decimal, localcontext
import math

EXPERIMENT = {
    "id": "quadratics_cancellation",
    "title": "Catastrophic cancellation in the quadratic formula",
    "evidence": ["numerical"],
    "lessons": ["quadratics"],
    "summary": (
        "Computes the small root of x^2 - Bx + 1 = 0 for B = 10^2 ... 10^8 with "
        "double-precision floats in two ways: the textbook formula, which loses "
        "accuracy to cancellation, and Vieta's product r1 r2 = c/a, which does "
        "not. Errors are measured against 60-digit decimal reference values."
    ),
    "packages": [],
}


def naive_small_root(a, b, c):
    """The textbook formula (-b - sqrt(b^2 - 4ac)) / (2a).

    For a > 0 and b < 0 this is the root of smaller size; when 4ac is tiny
    compared with b^2 it subtracts two nearly equal numbers.
    """
    return (-b - math.sqrt(b * b - 4 * a * c)) / (2 * a)


def stable_roots(a, b, c):
    """Both real roots without cancellation (needs b != 0 and D >= 0).

    First the root where -b and the square root have the same sign (no
    cancellation), then the other one from Vieta: r1 * r2 = c / a.
    """
    d = b * b - 4 * a * c
    if d < 0:
        raise ValueError("no real roots")
    big = (-b + math.copysign(math.sqrt(d), -b)) / (2 * a)
    return big, c / (a * big)


def reference_small_root(big_b, digits=60):
    """Small root of x^2 - B x + 1 to ``digits`` significant digits."""
    with localcontext() as ctx:
        ctx.prec = digits
        b = Decimal(big_b)
        return (b - (b * b - 4).sqrt()) / 2


def relative_error(approx, exact):
    """|approx - exact| / |exact|, with exact a Decimal (60-digit arithmetic)."""
    with localcontext() as ctx:
        ctx.prec = 60
        return abs((Decimal(approx) - exact) / exact)


def main():
    print("small root of x^2 - Bx + 1 = 0 (true value is about 1/B)")
    print(f"{'B':>6}  {'textbook formula':>18}  {'rel. error':>10}"
          f"  {'Vieta':>12}  {'rel. error':>10}")
    for k in range(2, 9):
        big_b = 10 ** k
        exact = reference_small_root(big_b)
        naive = naive_small_root(1.0, -float(big_b), 1.0)
        vieta = stable_roots(1.0, -float(big_b), 1.0)[1]
        print(f"  1e{k}  {naive:18.12e}  {float(relative_error(naive, exact)):10.1e}"
              f"  {vieta:12.6e}  {float(relative_error(vieta, exact)):10.1e}")
    print()
    print("For B = 1e8, sqrt(B^2 - 4) agrees with B in about 16 digits, so")
    print("B - sqrt(B^2 - 4) keeps almost none of them: the textbook answer")
    print("is wrong in the first digit. Vieta's 1/r1 keeps full precision.")
    print()
    print("Epistemic status: numerical evidence about IEEE double-precision")
    print("floating point, checked against 60-digit decimal values whose own")
    print("error is far below the digits shown. Algebraically both formulas are")
    print("exactly equal; the difference is entirely rounding error.")


if __name__ == "__main__":
    main()
