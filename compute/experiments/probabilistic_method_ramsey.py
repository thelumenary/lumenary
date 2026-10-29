"""Random colourings and Ramsey numbers: what the first moment gives.

Colour each edge of K_n red or blue by a fair coin. The expected number of
monochromatic copies of K_k is E(n, k) = C(n, k) 2^(1 - C(k, 2)); when it is
below 1, some colouring has none, so R(k, k) > n (Erdos, 1947). The deletion
method improves this: removing one vertex from each monochromatic K_k leaves
a good colouring on at least n - E(n, k) vertices. We tabulate both bounds,
simulate random colourings of K_6 to see that the probability of having no
monochromatic K_4 really is at least 1 - E(6, 4), and check by exhaustive
search that the Paley graph on 17 vertices (edges between quadratic residue
differences mod 17) has no K_4 and no independent 4-set, an explicit
colouring proving R(4, 4) > 17 - far better than the random bound for such
small k. Exact arithmetic for the bounds, exhaustive search for Paley, and a
seeded simulation (statistical evidence) for the random colourings.
"""

import itertools
import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "probabilistic_method_ramsey",
    "title": "Random colourings and Ramsey lower bounds",
    "evidence": ["exact", "exhaustive-finite", "statistical"],
    "lessons": ["probabilistic-method"],
    "summary": (
        "Tabulates Erdos's first-moment bound and the deletion bound for "
        "R(k, k), k = 3..10, against 2^(k/2); simulates 4000 random "
        "colourings of K_6 to compare the chance of no monochromatic K_4 "
        "with the guarantee 1 - E; and verifies by exhaustive search that "
        "the Paley graph on 17 vertices gives R(4, 4) > 17. Exact bounds, "
        "exhaustive check, seeded simulation."
    ),
    "packages": [],
}


def expected_monochromatic(n, k):
    """E(n, k) = C(n, k) 2^(1 - C(k, 2)) as an exact fraction."""
    return Fraction(math.comb(n, k) * 2, 2 ** math.comb(k, 2))


def first_moment_bound(k):
    """Largest n with E(n, k) < 1, so that R(k, k) > n."""
    n = k
    while expected_monochromatic(n + 1, k) < 1:
        n += 1
    return n


def deletion_bound(k):
    """max over n of n - floor(E(n, k)): R(k, k) exceeds this number.

    Some colouring has at most floor(E) monochromatic K_k; deleting one
    vertex from each leaves at least n - floor(E) vertices and none.
    """
    best, n = 0, k
    while True:
        value = n - math.floor(expected_monochromatic(n, k))
        if value < best - 5:
            return best
        best = max(best, value)
        n += 1


def random_colouring(n, rng):
    """A dict {(i, j): bool} for i < j, each edge red with probability 1/2."""
    return {e: rng.random() < 0.5 for e in itertools.combinations(range(n), 2)}


def count_monochromatic(colouring, n, k):
    """Number of k-subsets all of whose edges have the same colour."""
    count = 0
    for subset in itertools.combinations(range(n), k):
        colours = {colouring[e] for e in itertools.combinations(subset, 2)}
        count += len(colours) == 1
    return count


def paley_colouring(q):
    """Paley colouring of K_q, q prime = 1 mod 4: red iff i - j is a square."""
    squares = {(x * x) % q for x in range(1, q)}
    return {(i, j): (j - i) % q in squares
            for i, j in itertools.combinations(range(q), 2)}


def main():
    print(" k  2^(k/2)  first moment: R(k,k) >  deletion: R(k,k) >")
    for k in range(3, 11):
        print(f"{k:>2}  {2 ** (k / 2):>7.1f}  {first_moment_bound(k):>22}"
              f"  {deletion_bound(k):>18}")
    rng = random.Random(1947)
    n, k, trials = 6, 4, 4000
    counts = [count_monochromatic(random_colouring(n, rng), n, k)
              for _ in range(trials)]
    e = expected_monochromatic(n, k)
    good = counts.count(0) / trials
    margin = 1.96 * math.sqrt(good * (1 - good) / trials)
    print(f"Random colourings of K_{n}, {trials} samples (seed 1947):")
    print(f"  mean number of monochromatic K_{k}: {sum(counts) / trials:.3f}"
          f"  (exact E = {float(e):.3f})")
    print(f"  fraction with none: {good:.3f} +- {margin:.3f}"
          f"  (guaranteed >= 1 - E = {1 - float(e):.3f})")
    paley = paley_colouring(17)
    mono = count_monochromatic(paley, 17, 4)
    print(f"Paley colouring of K_17: {mono} monochromatic K_4 among "
          f"{math.comb(17, 4)} sets,")
    print("  so R(4,4) > 17 (in fact R(4,4) = 18); the random bound gives > 6.")
    print()
    print("Epistemic status: the bounds are exact arithmetic and the Paley")
    print("check is exhaustive, so both are proofs of what they state; the")
    print("simulation is statistical evidence (95% interval shown) about one")
    print("seeded run.")


if __name__ == "__main__":
    main()
