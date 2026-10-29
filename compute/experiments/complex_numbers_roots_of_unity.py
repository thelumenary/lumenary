"""Roots of unity, De Moivre's theorem and a square-root trap.

Numerically: the n numbers cos(2 pi k/n) + i sin(2 pi k/n) satisfy z^n = 1
up to rounding, add up to 0, multiply to (-1)^(n+1), and are spaced 2 sin(pi/n)
apart (a regular n-gon). Symbolically (SymPy): the exact cube roots of 1, and
the triple-angle formula cos 3t = 4 cos^3 t - 3 cos t read off from De
Moivre's theorem. Finally the trap: with principal square roots,
sqrt(-1) * sqrt(-1) = -1 while sqrt((-1) * (-1)) = 1.
"""

import cmath
import math

import sympy

EXPERIMENT = {
    "id": "complex_numbers_roots_of_unity",
    "title": "Roots of unity and De Moivre's theorem",
    "evidence": ["numerical", "symbolic"],
    "lessons": ["complex-numbers"],
    "summary": (
        "Computes the n-th roots of unity in floating point for n = 3..8 and "
        "checks z^n = 1, sum 0, product (-1)^(n+1) and side 2 sin(pi/n) up to "
        "rounding; uses SymPy for the exact cube roots of 1 and to derive "
        "cos 3t = 4cos^3 t - 3cos t from De Moivre; shows why "
        "sqrt(ab) = sqrt(a) sqrt(b) fails for negative a, b."
    ),
    "packages": ["sympy"],
}


def roots_of_unity(n):
    """The n complex numbers cis(2 pi k / n), k = 0, ..., n - 1."""
    if n < 1:
        raise ValueError("n must be at least 1")
    return [cmath.rect(1.0, 2 * math.pi * k / n) for k in range(n)]


def max_error_power(n):
    """max |z^n - 1| over the computed n-th roots of unity (rounding only)."""
    return max(abs(z ** n - 1) for z in roots_of_unity(n))


def root_sum(n):
    """Sum of the n-th roots of unity (exactly 0 for n >= 2)."""
    return sum(roots_of_unity(n))


def root_product(n):
    """Product of the n-th roots of unity (exactly (-1)^(n+1))."""
    product = 1
    for z in roots_of_unity(n):
        product *= z
    return product


def side_length(n):
    """Distance between neighbouring n-th roots of unity."""
    zs = roots_of_unity(n)
    return abs(zs[1 % n] - zs[0])


def exact_cube_roots():
    """The roots of z^3 - 1 as exact SymPy expressions, sorted by argument."""
    z = sympy.symbols("z")
    roots = sympy.solve(z ** 3 - 1, z)
    return sorted(roots, key=lambda r: float(sympy.arg(r)) % (2 * math.pi))


def triple_angle():
    """Real and imaginary parts of (cos t + i sin t)^3, in terms of cos, sin."""
    t = sympy.symbols("t", real=True)
    c, s = sympy.cos(t), sympy.sin(t)
    w = sympy.expand((c + sympy.I * s) ** 3)
    re_part = sympy.re(w).subs(s ** 2, 1 - c ** 2)
    im_part = sympy.im(w).subs(c ** 2, 1 - s ** 2)
    return sympy.expand(re_part), sympy.expand(im_part)


def main():
    print(" n  max|z^n - 1|  |sum|    |prod - (-1)^(n+1)|  side      2 sin(pi/n)")
    for n in range(3, 9):
        prod_err = abs(root_product(n) - (-1) ** (n + 1))
        print(
            f"{n:2d}  {max_error_power(n):.1e}      {abs(root_sum(n)):.1e}"
            f"  {prod_err:.1e}              {side_length(n):.6f}"
            f"  {2 * math.sin(math.pi / n):.6f}"
        )
    print("Errors of about 1e-15 are floating-point rounding, not mathematics.")
    print()
    roots = ", ".join(str(r) for r in exact_cube_roots())
    print(f"Exact cube roots of 1 (SymPy): {roots}")
    re_part, im_part = triple_angle()
    print("De Moivre, n = 3: (cos t + i sin t)^3 = cos 3t + i sin 3t, so")
    print(f"  cos 3t = {re_part}")
    print(f"  sin 3t = {im_part}")
    print()
    a = cmath.sqrt(-1) * cmath.sqrt(-1)
    b = cmath.sqrt((-1) * (-1))
    print(f"sqrt(-1) * sqrt(-1) = {a.real:+.0f}   but   sqrt((-1)(-1)) = {b.real:+.0f}")
    print("So sqrt(ab) = sqrt(a) sqrt(b) fails when a and b are negative.")
    print()
    print("Epistemic status: the table is numerical evidence for n = 3..8 only;")
    print("the lesson proves z^n = 1, the sum and the spacing for every n. The")
    print("SymPy results are exact symbolic computations, as trustworthy as")
    print("SymPy's algebra; De Moivre's theorem itself is proved by induction.")


if __name__ == "__main__":
    main()
