"""Guessing versus a system: how often does guessing miss an outfit?

There are 4 shirts and 3 pairs of trousers: 12 outfits. A "guesser" names
outfits at random, writes down each new one, and gives up after a few
guesses in a row that bring nothing new ("I can't think of any more").
The program simulates many guessers (with a fixed seed, so every run is the
same) and counts how often they really found all 12. A systematic list
finds all 12 in exactly 12 steps, every time.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import random
import textwrap
from fractions import Fraction

EXPERIMENT = {
    "id": "systematic_listing_guessing",
    "title": "Guessing versus a system: missing outfits",
    "evidence": ["statistical", "exact"],
    "lessons": ["systematic-listing"],
    "summary": (
        "Simulates 2000 seeded guessers who name random outfits out of 12 "
        "and stop after 3, 5 or 10 guesses in a row with nothing new, and "
        "counts how often they found all 12. Also compares the average "
        "number of guesses needed to find all 12 with the exact value 12 x "
        "(1 + 1/2 + ... + 1/12). Statistical evidence for this setting only."
    ),
    "packages": [],
}

OUTFITS = [(s, t) for s in range(4) for t in range(3)]


def guess_until_bored(rng, patience):
    """Guess random outfits; stop after `patience` guesses with nothing new.

    Returns the set of different outfits found.
    """
    found = set()
    misses = 0
    while misses < patience and len(found) < len(OUTFITS):
        outfit = rng.choice(OUTFITS)
        if outfit in found:
            misses += 1
        else:
            found.add(outfit)
            misses = 0
    return found


def guesses_to_find_all(rng):
    """Number of random guesses until every outfit has appeared."""
    found = set()
    guesses = 0
    while len(found) < len(OUTFITS):
        found.add(rng.choice(OUTFITS))
        guesses += 1
    return guesses


def expected_guesses(n):
    """Exact average number of guesses to see all n outfits: n(1 + ... + 1/n)."""
    return n * sum(Fraction(1, k) for k in range(1, n + 1))


def main():
    rng = random.Random(2024)
    runs = 2000
    print(f"{len(OUTFITS)} outfits. A system lists all of them in 12 steps.")
    print()
    print("Guessers who stop after some guesses in a row with nothing new:")
    print("  stop after   found all 12   average found")
    for patience in (3, 5, 10):
        results = [len(guess_until_bored(rng, patience)) for _ in range(runs)]
        complete = sum(r == len(OUTFITS) for r in results)
        print(f"  {patience:>2} misses   {100 * complete / runs:>9.1f} %"
              f"   {sum(results) / runs:>13.2f}")
    print()
    sims = [guesses_to_find_all(rng) for _ in range(runs)]
    exact = expected_guesses(len(OUTFITS))
    print("Guessers who never give up need, on average:")
    print(f"  simulated: {sum(sims) / runs:.2f} guesses"
          f"   exact: {float(exact):.2f} guesses")
    print(f"  (the exact value is 12 x (1 + 1/2 + ... + 1/12) = {exact})")
    print()
    print(textwrap.fill(
        f"Epistemic status: the percentages are statistical evidence from "
        f"{runs} simulated guessers per row (seeded, so repeatable); another "
        "seed gives slightly different numbers. The exact average comes from "
        "a short probability argument, not from the simulation. Guessing can "
        "never guarantee that nothing is missed; only a system can.",
        width=78,
    ))


if __name__ == "__main__":
    main()
