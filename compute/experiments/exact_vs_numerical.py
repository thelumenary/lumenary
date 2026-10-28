"""Exact computation versus numerical approximation.

Floating-point numbers ("floats") store a number in binary with about 16
significant decimal digits, so most decimals - even 0.1 - are rounded. That is
usually fine, but errors can show up and accumulate. Exact rational arithmetic
(``fractions.Fraction``, ``sympy.Rational``) and exact symbolic objects
(``sympy.sqrt(2)``) never round, at the cost of speed and memory.

Runs in the browser (Pyodide) with the ``sympy`` and ``numpy`` packages loaded.
"""

from fractions import Fraction
import math
import textwrap

import numpy as np
import sympy

EXPERIMENT = {
    "id": "exact_vs_numerical",
    "title": "Exact versus numerical: 0.1 + 0.2 and the square root of 2",
    "evidence": ["numerical", "exact", "symbolic"],
    "lessons": ["integers"],
    "summary": (
        "Compares 0.1 + 0.2 in floating point with exact fractions, shows how "
        "rounding error accumulates when 0.1 is added 10000 times in float64 and "
        "float32, and computes the square root of 2 by Newton's method (approximate) "
        "and with sympy.sqrt(2) (exact). Numerical results are approximations whose "
        "error must be measured; exact and symbolic results involve no rounding."
    ),
    "packages": ["numpy", "sympy"],
}


def float_sum_check():
    """Return (0.1 + 0.2 as a float, whether it equals the float 0.3)."""
    s = 0.1 + 0.2
    return s, s == 0.3


def fraction_sum_check():
    """Return (1/10 + 2/10 as an exact Fraction, whether it equals 3/10)."""
    s = Fraction(1, 10) + Fraction(2, 10)
    return s, s == Fraction(3, 10)


def sympy_sum_check():
    """Return (1/10 + 2/10 as a sympy Rational, whether it equals 3/10)."""
    s = sympy.Rational(1, 10) + sympy.Rational(2, 10)
    return s, s == sympy.Rational(3, 10)


def repeated_sum_loop(x, times):
    """Add the float x to 0.0 one at a time, ``times`` times (rounding at every step)."""
    total = 0.0
    for _ in range(times):
        total += x
    return total


def repeated_sums(times=10_000):
    """Return {method: result} for adding 0.1 ``times`` times in several ways."""
    f64 = np.full(times, 0.1, dtype=np.float64)
    f32 = np.full(times, 0.1, dtype=np.float32)
    return {
        "Python loop, float64": repeated_sum_loop(0.1, times),
        "numpy.sum, float64 (pairwise)": float(np.sum(f64)),
        "numpy running sum, float32": float(np.cumsum(f32)[-1]),
        "math.fsum (correctly rounded)": math.fsum([0.1] * times),
        "Fraction(1, 10) added exactly": sum([Fraction(1, 10)] * times, Fraction(0)),
    }


def newton_sqrt2_float(steps, x0=1.0):
    """Newton's method x -> (x + 2/x)/2 for sqrt(2) in floats; return the list of iterates."""
    xs = [float(x0)]
    for _ in range(steps):
        x = xs[-1]
        xs.append((x + 2 / x) / 2)
    return xs


def newton_sqrt2_exact(steps, x0=Fraction(1)):
    """The same Newton iteration in exact fractions; every iterate is a rational number."""
    xs = [Fraction(x0)]
    for _ in range(steps):
        x = xs[-1]
        xs.append((x + 2 / x) / 2)
    return xs


def main():
    print("1. Is 0.1 + 0.2 equal to 0.3?")
    s, eq = float_sum_check()
    print(f"   float (rounded):   0.1 + 0.2   = {s!r:<21}  equals 0.3?  {eq}")
    s, eq = fraction_sum_check()
    print(f"   Fraction (exact):  1/10 + 2/10 = {str(s):<21}  equals 3/10? {eq}")
    s, eq = sympy_sum_check()
    print(f"   sympy.Rational:    1/10 + 2/10 = {str(s):<21}  equals 3/10? {eq}")
    print(f"   The float written 0.1 is exactly {Fraction(0.1)}.")
    print()
    times = 10_000
    print(f"2. Add 0.1 to itself {times} times (exact answer: 1000)")
    print(f"   {'method':<32}{'result':<22}error")
    for method, result in repeated_sums(times).items():
        err = abs(Fraction(result) - 1000)
        err_s = "0 (exact)" if err == 0 else f"{float(err):.1e}"
        print(f"   {method:<32}{str(result):<22}{err_s}")
    hidden = times * (Fraction(0.1) - Fraction(1, 10))
    print("   fsum adds the stored floats exactly, then rounds once: their hidden excess")
    print(f"   ({float(hidden):.2e}) is just under half the float gap at 1000"
          f" ({math.ulp(1000.0) / 2:.2e}), so 1000.0.")
    print()
    print("3. The square root of 2")
    exact = sympy.sqrt(2)
    print(f"   exact symbol:  sympy.sqrt(2)**2 == 2 is {exact ** 2 == 2}")
    print(f"   float:         math.sqrt(2)**2 = {math.sqrt(2) ** 2!r}")
    print(f"   30 digits from sympy: {sympy.N(exact, 30)}")
    print(f"   {'step':<6}{'Newton in floats':<22}{'error vs sympy':<16}Newton in fractions")
    for i, (x, q) in enumerate(zip(newton_sqrt2_float(5), newton_sqrt2_exact(5))):
        err = abs(sympy.Float(x, 30) - sympy.N(exact, 30))
        err_s = "<1e-16" if err < 1e-16 else f"{float(err):.1e}"
        print(f"   {i:<6}{x!r:<22}{err_s:<16}{q}")
    print("   Floats stall at about 16 digits. Each fraction is exact, but none squares")
    print("   to exactly 2 - no fraction can, because sqrt(2) is irrational.")
    print()
    print(textwrap.fill(
        "Epistemic status: float results are numerical approximations whose errors "
        "we measured against exact values; Fraction and sympy.Rational results are "
        "exact; sympy.sqrt(2) is an exact symbolic object. None of these "
        "computations proves sqrt(2) is irrational - that needs the classical proof.",
        width=78,
    ))


if __name__ == "__main__":
    main()
