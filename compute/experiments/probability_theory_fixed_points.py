"""Fixed points of random permutations: linearity of expectation, checked exhaustively.

Shuffle n cards labelled 1..n. The number of cards that end up in their own
place is a sum of n dependent indicator variables, each with expectation 1/n,
so linearity of expectation gives mean 1 for every n - no independence needed.
A covariance calculation gives variance 1 for n >= 2. Here we list all n!
permutations for n <= 7 and compute these numbers exactly, together with the
chance of no fixed point (a derangement), which tends to 1/e, and the whole
distribution for n = 7, which is close to Poisson(1).
"""

import itertools
import math
from fractions import Fraction

EXPERIMENT = {
    "id": "probability_theory_fixed_points",
    "title": "Fixed points of random permutations, all n! of them",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["probability-theory"],
    "summary": (
        "Enumerates every permutation of n = 1..7 objects and computes, as exact "
        "fractions, the mean and variance of the number of fixed points (1 and 1, "
        "as linearity of expectation and covariances predict) and the probability "
        "of a derangement, which approaches 1/e. The distribution for n = 7 is "
        "compared with Poisson(1). Finite cases only: the proofs cover every n."
    ),
    "packages": [],
}


def fixed_point_counts(n):
    """List of the number of fixed points of each permutation of range(n)."""
    if n < 0:
        raise ValueError("n must be non-negative")
    return [sum(1 for i, j in enumerate(p) if i == j)
            for p in itertools.permutations(range(n))]


def mean_and_variance(values):
    """Exact mean and variance (Fractions) of equally likely values."""
    if not values:
        raise ValueError("need at least one value")
    m = Fraction(sum(values), len(values))
    v = Fraction(sum(x * x for x in values), len(values)) - m * m
    return m, v


def distribution(values):
    """Dictionary k -> exact probability that the count equals k."""
    total = len(values)
    return {k: Fraction(values.count(k), total) for k in sorted(set(values))}


def main():
    print(" n      n!  mean  variance  P(no fixed point)   vs 1/e = 0.367879")
    for n in range(1, 8):
        counts = fixed_point_counts(n)
        m, v = mean_and_variance(counts)
        p0 = distribution(counts).get(0, Fraction(0))
        print(f"{n:>2} {len(counts):>7} {str(m):>5} {str(v):>9}"
              f" {str(p0):>14} = {float(p0):.6f}")
    print()
    print("Distribution of the number of fixed points for n = 7:")
    dist = distribution(fixed_point_counts(7))
    print("  k   exact probability   Poisson(1): e^-1/k!")
    for k in range(8):
        p = dist.get(k, Fraction(0))
        poisson = math.exp(-1) / math.factorial(k)
        print(f"  {k}   {float(p):>17.6f}   {poisson:>19.6f}")
    print()
    print("Epistemic status: exhaustive and exact for n = 1, ..., 7 (5913")
    print("permutations in all). That the mean is 1 and the variance 1 for")
    print("every n >= 2 is proved in the lesson with indicators; the limit")
    print("1/e and the Poisson(1) limit are theorems that this table only")
    print("illustrates.")


if __name__ == "__main__":
    main()
