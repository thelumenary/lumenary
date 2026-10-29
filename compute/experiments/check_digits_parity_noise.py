"""A parity bit on a noisy line: simulation next to the exact probabilities.

Each word is 7 data bits plus 1 parity bit, so every word sent has an even
number of 1s. The channel flips each of the 8 bits independently with
probability p. The receiver accepts a word with an even number of 1s and
rejects one with an odd number. A seeded simulation of 10,000 words per value
of p is compared with exact formulas: a word arrives intact with probability
(1 - p)^8, is rejected exactly when an odd number of bits flipped, and slips
through damaged when an even number (2, 4, 6 or 8) flipped.
"""

import math
import random

EXPERIMENT = {
    "id": "check_digits_parity_noise",
    "title": "A parity bit on a noisy line",
    "evidence": ["statistical", "exact"],
    "lessons": ["check-digits"],
    "summary": (
        "Sends 10,000 eight-bit words (7 data bits and a parity bit) through a "
        "simulated channel that flips each bit with probability p, for three "
        "values of p, and counts intact, rejected and undetected-damaged words. "
        "The counts are compared with exact binomial probabilities. Simulation is "
        "statistical evidence; the formulas follow from the parity theorem."
    ),
    "packages": [],
}

BITS = 8  # 7 data bits + 1 parity bit


def with_parity(data):
    """Append a parity bit so that the number of 1s is even."""
    return list(data) + [sum(data) % 2]


def accepted(word):
    """The receiver's test: an even number of 1s."""
    return sum(word) % 2 == 0


def exact_probabilities(p, n=BITS):
    """(intact, rejected, undetected) probabilities for n bits, flip prob p."""
    flips = [math.comb(n, k) * p ** k * (1 - p) ** (n - k) for k in range(n + 1)]
    intact = flips[0]
    rejected = sum(flips[k] for k in range(1, n + 1, 2))
    undetected = sum(flips[k] for k in range(2, n + 1, 2))
    return intact, rejected, undetected


def simulate(p, words, seed):
    """Counts (intact, rejected, undetected) for ``words`` random words."""
    rng = random.Random(seed)
    intact = rejected = undetected = 0
    for _ in range(words):
        sent = with_parity([rng.randrange(2) for _ in range(BITS - 1)])
        got = [b ^ (rng.random() < p) for b in sent]
        if got == sent:
            intact += 1
        elif accepted(got):
            undetected += 1
        else:
            rejected += 1
    return intact, rejected, undetected


def main():
    words = 10_000
    print(f"{words} words of 7 data bits + 1 parity bit; each bit flips with")
    print("probability p. Simulated counts, then the exact expected counts:")
    print()
    print(f"{'p':>5}  {'':9}{'intact':>9}{'rejected':>10}{'undetected':>12}")
    for k, p in enumerate((0.01, 0.05, 0.2)):
        sim = simulate(p, words, seed=100 + k)
        exp = [words * q for q in exact_probabilities(p)]
        print(f"{p:>5}  {'simulated':9}{sim[0]:>9}{sim[1]:>10}{sim[2]:>12}")
        print(f"{'':>5}  {'exact':9}{exp[0]:>9.1f}{exp[1]:>10.1f}{exp[2]:>12.1f}")
    print()
    print("With p = 0.01 almost every damaged word is caught: two flips in one")
    print("word are rare. With p = 0.2 about 4 in 10 damaged words slip through,")
    print("because an even number of flips is invisible to a parity bit.")
    print()
    print("Epistemic status: the simulated counts are statistical evidence from")
    print("one seeded run and wobble around the exact values; the exact columns")
    print("are binomial probabilities that follow from the theorem 'a parity bit")
    print("detects an odd number of flips and no even number', with the extra")
    print("assumption that bits flip independently.")


if __name__ == "__main__":
    main()
