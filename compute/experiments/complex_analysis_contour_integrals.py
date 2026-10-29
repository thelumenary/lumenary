"""Contour integrals by computer: Cauchy, residues and counting zeros.

On a circle z = c + r e^(it) the integrand of a contour integral is periodic
in t, and for such integrands the plain trapezoid rule converges extremely
fast (geometrically, when the integrand is analytic near the circle). We use
it to check: the integral of 1/z is 2 pi i; the integral of conj(z) over the
unit circle is also 2 pi i (so conj is not holomorphic); Cauchy's integral
formula; the residue evaluations of two real integrals; and the argument
principle, which counts the zeros of a polynomial inside a circle.

Evidence: numerical. Every printed number is an approximation with an error
estimate or a comparison with an exact value; none of it proves a theorem.
"""

import cmath
import math

EXPERIMENT = {
    "id": "complex_analysis_contour_integrals",
    "title": "Contour integrals by computer: Cauchy, residues, zeros",
    "evidence": ["numerical"],
    "lessons": ["complex-analysis"],
    "summary": (
        "Computes contour integrals around circles with the trapezoid rule "
        "(geometrically convergent for analytic periodic integrands): 1/z and "
        "conj(z) give 2 pi i, z^2 gives 0, Cauchy's formula recovers e^0.5, "
        "two real integrals match their residue values pi and pi/e, and the "
        "argument principle counts the zeros of z^5 - 3z + 1 in the unit disc. "
        "Numerical evidence only."
    ),
    "packages": [],
}


def circle_integral(f, center=0j, radius=1.0, n=64):
    """Trapezoid rule for the integral of f(z) dz over |z - center| = radius."""
    if n < 1:
        raise ValueError("n must be positive")
    total = 0j
    for k in range(n):
        w = cmath.exp(2j * math.pi * k / n)
        z = center + radius * w
        total += f(z) * 1j * radius * w
    return total * 2 * math.pi / n


def simpson(f, a, b, n):
    """Composite Simpson rule with n (even) subintervals."""
    if n % 2:
        raise ValueError("n must be even")
    h = (b - a) / n
    s = f(a) + f(b)
    s += 4 * sum(f(a + (2 * i - 1) * h) for i in range(1, n // 2 + 1))
    s += 2 * sum(f(a + 2 * i * h) for i in range(1, n // 2))
    return s * h / 3


def count_zeros(p, dp, radius=1.0, n=2048):
    """Argument principle: (1/2 pi i) times the integral of p'/p."""
    value = circle_integral(lambda z: dp(z) / p(z), 0j, radius, n)
    return value / (2j * math.pi)


def fmt(z):
    """Complex number as a short string."""
    return f"{z.real:+.6f} {z.imag:+.6f}i"


def main():
    two_pi_i = 2j * math.pi
    print("Integrals over the unit circle (trapezoid rule, n = 64):")
    rows = [("1/z", lambda z: 1 / z), ("conj(z)", lambda z: z.conjugate()),
            ("z^2", lambda z: z * z), ("exp(z)/z^3", lambda z: cmath.exp(z) / z ** 3)]
    for name, f in rows:
        print(f"  {name:<11} {fmt(circle_integral(f))}")
    print(f"  2 pi i    = {fmt(two_pi_i)};  pi i = {fmt(two_pi_i / 2)}")
    print()
    print("Cauchy's formula: (1/2 pi i) * integral of e^z/(z - 0.5) = e^0.5")
    for n in [4, 8, 16, 32]:
        v = circle_integral(lambda z: cmath.exp(z) / (z - 0.5), n=n) / two_pi_i
        print(f"  n = {n:2d}: error {abs(v - math.exp(0.5)):.2e}")
    print()
    print("Real integrals over [-R, R], R = 400, against residue values:")
    a = simpson(lambda x: 1 / (1 + x * x), -400, 400, 80000)
    b = simpson(lambda x: math.cos(x) / (1 + x * x), -400, 400, 80000)
    print(f"  1/(1+x^2):      {a:.6f}  residue value pi   = {math.pi:.6f}")
    print(f"  cos x/(1+x^2):  {b:.6f}  residue value pi/e = {math.pi / math.e:.6f}")
    print("  (the first misses its tails, about 2/400; the second's")
    print("  oscillating tails are only about 1e-5.)")
    print()
    p = lambda z: z ** 5 - 3 * z + 1
    dp = lambda z: 5 * z ** 4 - 3
    print("Zeros of z^5 - 3z + 1 counted by the argument principle:")
    for r in [0.5, 1.0, 2.0]:
        print(f"  inside |z| = {r}: {fmt(count_zeros(p, dp, r))}")
    print()
    print("Epistemic status: numerical. The trapezoid rule on a circle is")
    print("spectrally accurate for analytic integrands, and the errors shown")
    print("are measured against exact values; the zero counts are near-integers")
    print("that Rouche's theorem confirms (1 zero in |z| < 1, all 5 in |z| < 2).")
    print("None of this replaces the proofs of Cauchy's and the residue theorem.")


if __name__ == "__main__":
    main()
