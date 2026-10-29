"""Floating-point summation: why the order of operations changes the answer.

Every double-precision float is a rational number with a power-of-two
denominator, so the exact sum of a list of floats can be computed with
integers. Against that exact value the experiment measures the error of
summing the same 100,000 numbers in different orders (as a parallel reduction
might), by pairwise summation, by Kahan's compensated summation and by
math.fsum, and compares the errors with the proven bound
((1 + u)^(n-1) - 1) * sum |x_i|, u = 2^-53, from the lesson. The exact sums are
exact; the floating-point results are what this machine's IEEE 754 arithmetic
produced, which other hardware or libraries need not reproduce bit for bit.
"""

import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "computational_reproducibility_floating_point",
    "title": "Summing the same numbers in different orders",
    "evidence": ["exact", "numerical"],
    "lessons": ["computational-reproducibility"],
    "summary": (
        "Shows that floating-point addition is not associative, then sums 100,000 "
        "seeded random numbers in several orders and by pairwise, Kahan and "
        "math.fsum summation. Errors are measured against the exact rational sum "
        "(computed with integers) and compared with the proven worst-case bound "
        "for recursive summation. The exact sums are exact; the float results are "
        "this machine's IEEE 754 arithmetic."
    ),
    "packages": [],
}

U = 2.0 ** -53          # unit roundoff of IEEE double precision


def exact_sum(xs):
    """The exact sum of a list of floats, as a Fraction (via integers)."""
    ratios = [x.as_integer_ratio() for x in xs]
    big = max((d for _, d in ratios), default=1)   # all are powers of two
    return Fraction(sum(n * (big // d) for n, d in ratios), big)


def recursive_sum(xs):
    """Left-to-right summation, one rounding per addition."""
    s = 0.0
    for x in xs:
        s += x
    return s


def pairwise_sum(xs):
    """Pairwise (tree) summation: error grows like log n instead of n."""
    if len(xs) <= 8:
        return recursive_sum(xs)
    mid = len(xs) // 2
    return pairwise_sum(xs[:mid]) + pairwise_sum(xs[mid:])


def kahan_sum(xs):
    """Kahan's compensated summation: carries the lost low-order bits."""
    s, c = 0.0, 0.0
    for x in xs:
        y = x - c
        t = s + y
        c = (t - s) - y
        s = t
    return s


def recursive_bound(xs):
    """The lesson's bound ((1 + u)^(n-1) - 1) * sum |x_i|, rounded up a little."""
    n = len(xs)
    factor = math.expm1((n - 1) * math.log1p(U))
    return factor * math.fsum(abs(x) for x in xs) * (1 + 1e-12)


def make_data(n, seed=2024):
    """n seeded numbers of mixed sign and magnitude (1e-6 to 1e6)."""
    rng = random.Random(seed)
    return [rng.uniform(-1.0, 1.0) * 10.0 ** rng.randint(-6, 6)
            for _ in range(n)]


def main():
    a, b, c = 0.1, 0.2, 0.3
    print(f"(0.1 + 0.2) + 0.3 = {(a + b) + c!r}")
    print(f"0.1 + (0.2 + 0.3) = {a + (b + c)!r}")
    print(f"the float 0.1 is exactly {Fraction(a)}")
    print()
    xs = make_data(100_000)
    exact = exact_sum(xs)
    rng = random.Random(7)
    shuffled = xs[:]
    rng.shuffle(shuffled)
    methods = [
        ("given order", recursive_sum(xs)),
        ("shuffled order", recursive_sum(shuffled)),
        ("increasing |x|", recursive_sum(sorted(xs, key=abs))),
        ("decreasing |x|", recursive_sum(sorted(xs, key=abs, reverse=True))),
        ("pairwise", pairwise_sum(xs)),
        ("Kahan", kahan_sum(xs)),
        ("math.fsum", math.fsum(xs)),
    ]
    print(f"n = {len(xs)}; exact sum = {float(exact)!r} (rounded to print)")
    print(f"{'method':<16}{'computed sum':>26}{'|error|':>12}")
    for name, value in methods:
        err = abs(Fraction(value) - exact)
        print(f"{name:<16}{value!r:>26}{float(err):>12.2e}")
    distinct = len({value for _, value in methods})
    print(f"{distinct} different results from {len(methods)} methods.")
    print(f"Proven bound for any recursive order: {recursive_bound(xs):.2e}")
    print()
    print("Epistemic status: the exact sum and every error are exact rational")
    print("arithmetic; the computed sums are what this machine produced. The")
    print("observed errors lie far below the worst-case bound, which is a theorem")
    print("(proved in Lean) under the standard model of rounding; a different")
    print("order, compiler or library may legitimately give different last digits.")


if __name__ == "__main__":
    main()
