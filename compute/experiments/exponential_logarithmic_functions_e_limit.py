"""Compound interest and the number e.

A deposit of 1 at 100% annual interest, compounded n times a year, grows to
(1 + 1/n)^n after one year. As n grows this approaches e = 2.71828..., but
slowly: the error is close to e/(2n). The series 1 + 1 + 1/2! + 1/3! + ...
reaches the same number much faster. We also check that ln turns products
into sums, the idea behind Napier's logarithm tables.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "exponential_logarithmic_functions_e_limit",
    "title": "Compound interest, the number e, and logarithm tables",
    "evidence": ["numerical", "exact"],
    "lessons": ["exponential-logarithmic-functions"],
    "summary": (
        "Computes (1 + 1/n)^n for n = 1 ... 10^6 and compares the error with "
        "the prediction e/(2n); computes partial sums of 1/k! with exact "
        "fractions; and checks ln(xy) = ln x + ln y numerically, the principle "
        "of logarithm tables. Floating-point evidence, with error estimates."
    ),
    "packages": [],
}


def compound(n):
    """(1 + 1/n)^n, computed as exp(n * log1p(1/n)) to avoid rounding loss."""
    if n < 1:
        raise ValueError("n must be a positive integer")
    return math.exp(n * math.log1p(1 / n))


def compound_exact(n):
    """(1 + 1/n)^n as an exact fraction (use only for small n)."""
    return (1 + Fraction(1, n)) ** n


def series_partial_sum(terms):
    """1 + 1/1! + 1/2! + ... + 1/(terms - 1)! as an exact fraction."""
    total = Fraction(0)
    factorial = 1
    for k in range(terms):
        if k > 0:
            factorial *= k
        total += Fraction(1, factorial)
    return total


def main():
    print("1 deposited at 100% interest, compounded n times in one year:")
    print(f"{'n':>9}  {'(1 + 1/n)^n':>14}  {'e - value':>10}  {'n * error':>9}")
    for n in [1, 2, 4, 12, 365, 10 ** 4, 10 ** 6]:
        value = compound(n)
        err = math.e - value
        print(f"{n:9d}  {value:14.10f}  {err:10.3e}  {n * err:9.4f}")
    print(f"n * error approaches e/2 = {math.e / 2:.4f}: the error is about"
          " e/(2n).")
    print(f"exact check: (1 + 1/12)^12 = {compound_exact(12)}")
    print(f"           = {float(compound_exact(12)):.10f}")
    print()
    print("the series 1 + 1 + 1/2! + 1/3! + ... (exact fractions):")
    for terms in [3, 5, 8, 12, 16]:
        s = series_partial_sum(terms)
        print(f"  {terms:2d} terms: {float(s):.15f}   e - sum = "
              f"{math.e - float(s):.1e}")
    print()
    print("logarithm tables: ln(xy) = ln x + ln y")
    for x, y in [(2, 3), (7.5, 40), (0.125, 640)]:
        lhs, rhs = math.log(x * y), math.log(x) + math.log(y)
        print(f"  ln({x} * {y}) = {lhs:.12f},  ln {x} + ln {y} ="
              f" {rhs:.12f}")
    print()
    print("Epistemic status: numerical evidence in double-precision arithmetic")
    print("(about 16 significant digits); the e/(2n) pattern is an observed")
    print("estimate, consistent with a calculus argument we do not give here.")
    print("The limit itself is a theorem (in Lean via Mathlib), not something a")
    print("finite table can prove.")


if __name__ == "__main__":
    main()
