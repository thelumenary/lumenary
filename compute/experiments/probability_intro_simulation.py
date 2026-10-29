"""Simulated dice and coins against exact probabilities.

A seeded pseudo-random generator rolls two dice thousands of times. The
relative frequency of each sum is compared with its exact probability
(ways / 36). Repeating with more and more rolls shows the frequencies
settling down - the law of large numbers - with typical errors shrinking
roughly like 1/sqrt(n). Two misconceptions are then tested: that a coin is
"due" heads after three tails (the gambler's fallacy), and that a
probability of 1/6 means exactly one six in every six rolls.
"""

import math
import random
from collections import Counter

EXPERIMENT = {
    "id": "probability_intro_simulation",
    "title": "Relative frequency versus probability: simulated dice and coins",
    "evidence": ["statistical", "exact"],
    "lessons": ["probability-intro"],
    "summary": (
        "Rolls two simulated dice up to 60,000 times (seeded) and compares the "
        "relative frequency of each sum with its exact probability; the "
        "largest error shrinks roughly like 1/sqrt(n). Also checks that after "
        "three tails in a row a simulated coin still lands heads about half "
        "the time, and that six rolls contain exactly one six only about 40% "
        "of the time (exactly (5/6)^5). Statistical evidence from one run."
    ),
    "packages": [],
}

EXACT = {s: (6 - abs(s - 7)) / 36 for s in range(2, 13)}


def roll_two_dice(rng, n):
    """Counter of sums for n rolls of two dice."""
    return Counter(rng.randint(1, 6) + rng.randint(1, 6) for _ in range(n))


def largest_error(counts, n):
    """Largest |relative frequency - exact probability| over all sums."""
    return max(abs(counts[s] / n - EXACT[s]) for s in range(2, 13))


def heads_after_tails(flips, run):
    """Among flips that follow `run` tails in a row, the fraction of heads.

    Returns (fraction, number of such flips). Flips are 'H' or 'T'.
    """
    after = [flips[i] for i in range(run, len(flips))
             if all(f == "T" for f in flips[i - run:i])]
    if not after:
        return None, 0
    return after.count("H") / len(after), len(after)


def exactly_one_six_rate(rng, blocks):
    """Fraction of blocks of six rolls that contain exactly one six."""
    hits = 0
    for _ in range(blocks):
        sixes = sum(1 for _ in range(6) if rng.randint(1, 6) == 6)
        hits += sixes == 1
    return hits / blocks


def main():
    rng = random.Random(2024)
    counts = roll_two_dice(rng, 3600)
    print("3,600 rolls of two dice: relative frequency vs exact probability")
    print("  sum   count   frequency   exact (ways/36)")
    for s in range(2, 13):
        print(f"  {s:3d}   {counts[s]:5d}   {counts[s] / 3600:9.4f}   "
              f"{EXACT[s]:.4f}")
    print()
    print("More rolls, smaller errors (largest error over the 11 sums):")
    for n in (60, 600, 6000, 60000):
        err = largest_error(roll_two_dice(rng, n), n)
        print(f"  n = {n:6d}: largest error {err:.4f}   1/sqrt(n) = "
              f"{1 / math.sqrt(n):.4f}")
    print()
    flips = ["H" if rng.random() < 0.5 else "T" for _ in range(100000)]
    frac, cases = heads_after_tails(flips, 3)
    print(f"Coin: after three tails in a row ({cases} times in 100,000 "
          f"flips),")
    print(f"  the next flip was heads {frac:.3f} of the time. Not 'due'.")
    rate = exactly_one_six_rate(rng, 20000)
    print(f"Blocks of six rolls with exactly one six: {rate:.3f} "
          f"(exact (5/6)^5 = {(5 / 6) ** 5:.3f})")
    print()
    print("Epistemic status: statistical evidence from one seeded run of a")
    print("pseudo-random generator, compared with exact values. Frequencies")
    print("vary from run to run; the law of large numbers (a theorem) says")
    print("they settle near the probabilities as n grows, not that they hit")
    print("them exactly.")


if __name__ == "__main__":
    main()
