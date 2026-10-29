"""Borel-Cantelli in action: convergence in probability without a.s. convergence.

Take independent events A_n with P(A_n) = 1/n, and independent events B_n with
P(B_n) = 1/n^2. Both indicator sequences tend to 0 in probability. The second
Borel-Cantelli lemma says infinitely many A_n occur almost surely (the sum of
1/n diverges), while the first says only finitely many B_n occur (the sum of
1/n^2 converges). We compute the exact expected number of occurrences in each
dyadic block [2^k, 2^(k+1)), and simulate a few seeded runs to watch the A_n
keep happening in late blocks while the B_n stop early.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "measure_theoretic_probability_borel_cantelli",
    "title": "Borel-Cantelli: events that keep happening, and events that stop",
    "evidence": ["exact", "statistical"],
    "lessons": ["measure-theoretic-probability"],
    "summary": (
        "Exact expected counts of independent events with P(A_n) = 1/n and "
        "P(B_n) = 1/n^2 in dyadic blocks (about ln 2 per block versus a "
        "geometrically shrinking amount), plus seeded simulations of five runs "
        "up to n = 2^16 showing the late occurrences of each. The simulation is "
        "statistical evidence for a finite horizon only; the almost-sure "
        "statements are the Borel-Cantelli lemmas proved in the lesson."
    ),
    "packages": [],
}


def block_expectation(k, power):
    """Exact sum of 1/n^power over the dyadic block 2^k <= n < 2^(k+1)."""
    if k < 0 or power < 1:
        raise ValueError("need k >= 0 and power >= 1")
    return sum(Fraction(1, n ** power) for n in range(2 ** k, 2 ** (k + 1)))


def simulate(power, n_max, rng):
    """Indices n <= n_max at which the event with P = 1/n^power occurs."""
    return [n for n in range(1, n_max + 1) if rng.random() < 1.0 / n ** power]


def block_counts(hits, k_max):
    """How many hits fall in each block [2^k, 2^(k+1)) for k = 0..k_max."""
    counts = [0] * (k_max + 1)
    for n in hits:
        k = n.bit_length() - 1
        if k <= k_max:
            counts[k] += 1
    return counts


def main():
    k_max = 15
    print("Exact expected number of occurrences in the block [2^k, 2^(k+1)):")
    print("   k   P(A_n) = 1/n    P(B_n) = 1/n^2")
    for k in [0, 1, 2, 4, 6, 8]:
        a = float(block_expectation(k, 1))
        b = float(block_expectation(k, 2))
        print(f"  {k:>2}   {a:.6f}        {b:.3e}")
    print("The 1/n blocks decrease to ln 2 = 0.693147, so the series diverges;")
    print("the 1/n^2 blocks shrink like 2^-(k+1), so that series converges.")
    print()
    rng = random.Random(1933)
    n_max = 2 ** (k_max + 1) - 1
    print(f"Five seeded runs up to n = {n_max}:")
    for run in range(5):
        a_hits = simulate(1, n_max, rng)
        b_hits = simulate(2, n_max, rng)
        late = sum(block_counts(a_hits, k_max)[10:])
        print(f"  run {run + 1}: {late} of the A_n with n >= 1024 occur,"
              f" last at n = {a_hits[-1]}; last B_n at n = {b_hits[-1]}")
    print("About ln 2 of the A_n are expected in every dyadic block, forever;")
    print("the B_n stop after a few indices. Yet P(A_n) -> 0: the indicators")
    print("of A_n tend to 0 in probability but not almost surely.")
    print()
    print("Epistemic status: the block expectations are exact rational")
    print("arithmetic. The runs are seeded pseudo-random simulations of a")
    print("finite horizon: they illustrate, but cannot prove, the almost-sure")
    print("statements, which are the two Borel-Cantelli lemmas.")


if __name__ == "__main__":
    main()
