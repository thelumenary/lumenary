"""Time averages versus space averages in four systems.

1. Rotation by the golden ratio: the fraction of time an orbit spends in
   [0, 1/4) tends to 1/4 (Weyl), but the overlaps mu(A & R^-n A) keep
   returning near 1/2, so the rotation is not mixing. A rational rotation is
   not ergodic: the time average depends on the starting point.
2. The doubling map in floating point collapses to 0 (each step discards a
   binary digit), while exact arithmetic on random binary digits behaves
   typically: Birkhoff for the doubling map is the law of large numbers.
3. The Gauss map x -> {1/x}: continued fraction digits of random numbers
   follow the Gauss-Kuzmin law log2(1 + 1/(k(k + 2))), and the Gauss measure
   is invariant (checked by a telescoping partial product).
"""

import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "ergodic_theory_birkhoff_averages",
    "title": "Birkhoff averages: rotations, doubling and continued fractions",
    "evidence": ["numerical", "exact", "statistical"],
    "lessons": ["ergodic-theory"],
    "summary": (
        "Computes Birkhoff averages for an irrational and a rational rotation, the "
        "non-mixing overlaps of the golden rotation, the collapse of the doubling "
        "map in floating point versus exact arithmetic on random bits, and the "
        "frequencies of continued fraction digits of random numbers against the "
        "Gauss-Kuzmin law, plus a check of the invariance of the Gauss measure. "
        "Finite orbits and seeded random samples: evidence, not proof."
    ),
    "packages": [],
}

GOLDEN = (math.sqrt(5) - 1) / 2


def rotation_average(alpha, x0, n, a=0.0, b=0.25):
    """Fraction of x0, x0 + alpha, ..., (n - 1 terms) mod 1 lying in [a, b)."""
    count, x = 0, x0 % 1.0
    for _ in range(n):
        if a <= x < b:
            count += 1
        x = (x + alpha) % 1.0
    return count / n


def rotation_overlap(alpha, n):
    """Lebesgue measure of A & R^-n A for A = [0, 1/2) and R(x) = x + alpha:
    1/2 - ||n alpha||, with ||t|| the distance from t to the nearest integer."""
    t = n * alpha
    return 0.5 - abs(t - round(t))


def float_doubling_steps(x, limit=200):
    """Number of steps until the floating-point doubling orbit of x hits 0."""
    for k in range(limit):
        if x == 0:
            return k
        x = (2 * x) % 1.0
    return limit


def exact_doubling_frequency(bits):
    """Exact doubling orbit of x = 0.b1 b2 b3 ... (binary): the fraction of
    the first len(bits) iterates lying in [0, 1/2)."""
    n = len(bits)
    x = Fraction(int("".join(map(str, bits)), 2), 2 ** n)
    hits = 0
    for _ in range(n):
        hits += x < Fraction(1, 2)
        x = 2 * x - int(2 * x)
    return hits / n


def continued_fraction_digits(x, count):
    """The first `count` continued fraction digits a1, a2, ... of x in (0, 1),
    obtained by iterating the Gauss map exactly."""
    digits = []
    for _ in range(count):
        if x == 0:
            break
        a = int(1 / x)
        digits.append(a)
        x = 1 / x - a
    return digits


def gauss_kuzmin(k):
    """Gauss measure of {x : a1(x) = k} = log2(1 + 1/(k (k + 2)))."""
    return math.log2(1 + 1 / (k * (k + 2)))


def gauss_preimage_measure(t, terms):
    """Gauss measure of T^-1 [0, t) = union of [1/(n + t), 1/n), via the partial
    product prod (n + 1)(n + t) / (n (n + 1 + t)) over n <= terms."""
    product = 1.0
    for n in range(1, terms + 1):
        product *= (n + 1) * (n + t) / (n * (n + 1 + t))
    return math.log2(product)


def main():
    print("1. Rotations: fraction of time in A = [0, 1/4)")
    for n in [100, 10_000, 100_000]:
        avg = rotation_average(GOLDEN, 0.0, n)
        print(f"   golden, N = {n:>6}: {avg:.5f}  (space average 0.25)")
    print("   rotation by 2/5, from x0 = 0 and x0 = 0.3:",
          rotation_average(0.4, 0.0, 1000), rotation_average(0.4, 0.3, 1000))
    print("   golden overlaps mu(A & R^-n A), A = [0, 1/2), for n = 1, 4, 55, 89:")
    print("  ", [round(rotation_overlap(GOLDEN, n), 4) for n in [1, 4, 55, 89]],
          "- no limit 1/4: not mixing")
    print()
    print("2. Doubling map")
    print(f"   float orbit of 0.1 reaches 0 after {float_doubling_steps(0.1)} steps")
    rng = random.Random(2024)
    bits = [rng.randrange(2) for _ in range(4000)]
    print(f"   exact orbit of 4000 random bits: time in [0, 1/2) ="
          f" {exact_doubling_frequency(bits):.4f}")
    print("   (space average 0.5; the orbit reads off the binary digits)")
    print()
    print("3. Gauss map: continued fraction digits of 20 random numbers")
    digits = []
    for _ in range(20):
        x = Fraction(rng.getrandbits(3000), 2 ** 3000)
        digits += continued_fraction_digits(x, 400)
    total = len(digits)
    print(f"   {total} digits;  k: observed frequency vs Gauss-Kuzmin")
    for k in [1, 2, 3, 4, 10]:
        observed = digits.count(k) / total
        print(f"   k = {k:>2}: {observed:.4f} vs {gauss_kuzmin(k):.4f}")
    print("   Gauss measure of T^-1[0, 0.3) vs [0, 0.3):",
          f"{gauss_preimage_measure(0.3, 10_000):.5f} vs {math.log2(1.3):.5f}")
    print()
    print("Epistemic status: numerical and statistical evidence from finite")
    print("orbits and seeded random samples (the overlaps and the Gauss product")
    print("are exact formulas, evaluated in floating point). Birkhoff's theorem,")
    print("non-mixing of rotations and invariance of the Gauss measure are the")
    print("lesson's theorems; the floating-point collapse shows that a computed")
    print("orbit need not be a typical orbit.")


if __name__ == "__main__":
    main()
