"""Exponential generating functions, computed exactly and checked by brute force.

A labelled structure on n points is counted by a_n, and its exponential
generating function (EGF) is A(x) = sum a_n x^n / n!. The exponential
formula says: if a structure is a set of "connected" pieces counted by
C(x), then A(x) = exp(C(x)). We expand three EGFs with exact fractions:

* set partitions:   exp(e^x - 1)        (blocks are nonempty sets)
* involutions:      exp(x + x^2/2)      (cycles of length 1 or 2)
* derangements:     e^(-x) / (1 - x)    (permutations with no fixed point)

and compare their coefficients with direct enumeration for n <= 7. We also
watch D(n)/n! approach 1/e, with the alternating-series error bound.
"""

import itertools
import math
from fractions import Fraction

EXPERIMENT = {
    "id": "enumerative_combinatorics_egf",
    "title": "Exponential generating functions versus brute-force counting",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["enumerative-combinatorics"],
    "summary": (
        "Expands the EGFs exp(e^x - 1), exp(x + x^2/2) and e^(-x)/(1 - x) with exact "
        "fractions and compares their coefficients with brute-force counts of set "
        "partitions, involutions and derangements for n <= 7, then checks "
        "|D(n)/n! - 1/e| <= 1/(n+1)! numerically. Exact for the sizes shown."
    ),
    "packages": [],
}

N = 12


def series_mul(a, b):
    """Product of two truncated power series (lists of Fractions)."""
    return [sum(a[i] * b[n - i] for i in range(n + 1)) for n in range(len(a))]


def series_exp(f):
    """exp(f) for a truncated series with f[0] = 0, via g' = f' g:
    n g_n = sum_{k=1}^{n} k f_k g_{n-k}."""
    if f[0] != 0:
        raise ValueError("constant term must be 0")
    g = [Fraction(1)] + [Fraction(0)] * (len(f) - 1)
    for n in range(1, len(f)):
        g[n] = sum(k * f[k] * g[n - k] for k in range(1, n + 1)) / n
    return g


def exp_series(c=1):
    """e^(c x) as a truncated series."""
    return [Fraction(c) ** n / math.factorial(n) for n in range(N + 1)]


def egf_counts(series):
    """Turn EGF coefficients into counts a_n = n! [x^n]."""
    counts = [s * math.factorial(n) for n, s in enumerate(series)]
    assert all(c.denominator == 1 for c in counts)
    return [int(c) for c in counts]


def set_partitions_egf():
    e = exp_series()
    return egf_counts(series_exp([Fraction(0)] + e[1:]))


def involutions_egf():
    f = [Fraction(0)] * (N + 1)
    f[1], f[2] = Fraction(1), Fraction(1, 2)
    return egf_counts(series_exp(f))


def derangements_egf():
    geometric = [Fraction(1)] * (N + 1)
    return egf_counts(series_mul(exp_series(-1), geometric))


def count_set_partitions(n):
    """Brute force: build partitions of {0..n-1} element by element."""
    blocks_list = [[]]
    for x in range(n):
        new = []
        for blocks in blocks_list:
            for i in range(len(blocks)):
                new.append(blocks[:i] + [blocks[i] + [x]] + blocks[i + 1:])
            new.append(blocks + [[x]])
        blocks_list = new
    return len(blocks_list)


def count_involutions(n):
    return sum(1 for p in itertools.permutations(range(n))
               if all(p[p[i]] == i for i in range(n)))


def count_derangements(n):
    return sum(1 for p in itertools.permutations(range(n))
               if all(p[i] != i for i in range(n)))


def main():
    rows = [
        ("set partitions (Bell)", "exp(e^x - 1)", set_partitions_egf(),
         count_set_partitions),
        ("involutions", "exp(x + x^2/2)", involutions_egf(), count_involutions),
        ("derangements", "e^(-x)/(1 - x)", derangements_egf(),
         count_derangements),
    ]
    for name, egf, coeffs, brute in rows:
        checked = all(coeffs[n] == brute(n) for n in range(8))
        print(f"{name} from {egf}:")
        print(f"  n = 0..10: {coeffs[:11]}")
        print(f"  equal to brute-force counts for n <= 7: {checked}")
    print()
    d = derangements_egf()
    print("Derangements: D(n)/n! approaches 1/e = 0.3678794412...")
    for n in (3, 6, 9, 12):
        ratio = Fraction(d[n], math.factorial(n))
        error = abs(float(ratio) - math.exp(-1))
        bound = 1 / math.factorial(n + 1)
        print(f"  n = {n:>2}: D(n)/n! = {float(ratio):.10f}, error {error:.2e}"
              f" <= {bound:.2e}: {error <= bound}")
    print(f"  D(n) = round(n!/e) for 1 <= n <= 12: "
          f"{all(d[n] == round(math.factorial(n) / math.e) for n in range(1, 13))}")
    print()
    print("Epistemic status: exact rational arithmetic for the series and "
          "exhaustive\nenumeration for n <= 7, so the agreement is a finite "
          "check of the\nexponential formula, not a proof; the error column "
          "uses floating point,\nwhich is ample at this precision.")


if __name__ == "__main__":
    main()
