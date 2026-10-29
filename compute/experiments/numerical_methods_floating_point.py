"""Floating point: machine epsilon, and cancellation that destroys accuracy.

Python floats are IEEE 754 binary64 numbers. We find machine epsilon by
halving until 1 + eps is no longer bigger than 1, check that 0.1 + 0.2 is not
the float nearest to 0.3, and then watch catastrophic cancellation: computing
(1 - cos x)/x^2 for small x loses all its digits, although every operation is
correctly rounded, while the algebraically equal 2 sin^2(x/2)/x^2 stays
accurate. The same happens to the small root of x^2 - 10^8 x + 1 in the
schoolbook quadratic formula, and a rearranged formula fixes it.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "numerical_methods_floating_point",
    "title": "Machine epsilon and catastrophic cancellation",
    "evidence": ["numerical", "exact"],
    "lessons": ["numerical-methods"],
    "summary": (
        "Finds machine epsilon 2^-52 by repeated halving, shows the exact binary "
        "value stored for 0.1, and measures the relative error of (1 - cos x)/x^2 "
        "and of the quadratic formula's small root against accurate rearranged "
        "formulas, showing that cancellation of nearly equal numbers can lose "
        "every significant digit even though each operation is correctly rounded."
    ),
    "packages": [],
}


def machine_epsilon():
    """Smallest power of two eps with 1 + eps > 1 in floating point."""
    eps = 1.0
    while 1.0 + eps / 2 > 1.0:
        eps /= 2
    return eps


def naive_one_minus_cos(x):
    """(1 - cos x) / x^2, computed directly (suffers cancellation)."""
    return (1 - math.cos(x)) / x ** 2


def stable_one_minus_cos(x):
    """The same quantity as 2 sin^2(x/2) / x^2: no subtraction of close numbers."""
    s = math.sin(x / 2)
    return 2 * s * s / x ** 2


def one_minus_cos_series(x, terms=8):
    """(1 - cos x)/x^2 from its Taylor series sum (-1)^k x^(2k) / (2k + 2)!."""
    return sum((-1) ** k * x ** (2 * k) / math.factorial(2 * k + 2)
               for k in range(terms))


def relative_error(approx, exact):
    """|approx - exact| / |exact|."""
    return abs(approx - exact) / abs(exact)


def quadratic_roots_naive(b, c):
    """Roots of x^2 + b x + c by the schoolbook formula (b < 0 assumed)."""
    d = math.sqrt(b * b - 4 * c)
    return (-b + d) / 2, (-b - d) / 2


def quadratic_roots_stable(b, c):
    """Large root by the formula without cancellation, small root as c / large."""
    d = math.sqrt(b * b - 4 * c)
    big = (-b + d) / 2 if b < 0 else (-b - d) / 2
    return big, c / big


def main():
    eps = machine_epsilon()
    print(f"machine epsilon = {eps!r} = 2^{round(math.log2(eps))}")
    print(f"1 + eps/2 == 1: {1 + eps / 2 == 1}")
    print(f"0.1 is stored as {Fraction(0.1)}")
    print(f"0.1 + 0.2 = {0.1 + 0.2!r}; equal to 0.3: {0.1 + 0.2 == 0.3}")
    print()
    print("(1 - cos x)/x^2 (true value from its Taylor series, about 1/2):")
    print("       x      naive           rel. error   stable rel. error")
    for k in range(1, 9):
        x = 10.0 ** (-k)
        exact = one_minus_cos_series(x)
        naive = naive_one_minus_cos(x)
        print(f"  1e-{k:d}  {naive:.12f}  {relative_error(naive, exact):10.1e}"
              f"  {relative_error(stable_one_minus_cos(x), exact):10.1e}")
    print()
    b, c = -1e8, 1.0
    small_true = 1e-8 + 1e-24  # small root of x^2 - 1e8 x + 1, to 32 digits
    naive_small = quadratic_roots_naive(b, c)[1]
    stable_small = quadratic_roots_stable(b, c)[1]
    print("Small root of x^2 - 10^8 x + 1 (true value 1.0000...e-08):")
    print(f"  schoolbook formula: {naive_small:.10e}  rel. error "
          f"{relative_error(naive_small, small_true):.1e}")
    print(f"  c / (large root):   {stable_small:.10e}  rel. error "
          f"{relative_error(stable_small, small_true):.1e}")
    print()
    print("Epistemic status: exact facts about IEEE binary64 arithmetic as")
    print("implemented by this Python (all mainstream platforms agree). The")
    print("errors are measured against series and exact expansions; they")
    print("illustrate, not prove, the cancellation bound of the lesson.")


if __name__ == "__main__":
    main()
