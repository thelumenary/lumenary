"""How rounding errors add up: round first, or add first?

Rounding one number to the nearest ten moves it by at most 5, so rounding k
numbers before adding can move the total by up to 5k. We check every list of
three numbers below 60 exactly, then simulate (with a fixed seed) many
shopping lists of 5, 20 and 80 prices and compare the worst case 5k with the
errors that actually happen: positive and negative errors partly cancel.
"""

import random
import statistics

EXPERIMENT = {
    "id": "estimation_accumulated_error",
    "title": "Rounding errors: the worst case and the typical case",
    "evidence": ["exhaustive-finite", "statistical"],
    "lessons": ["estimation"],
    "summary": (
        "Checks all 216,000 lists of three numbers below 60: the rounded-first total "
        "is always within 5 x 3 = 15 of the exact total, and it differs from the "
        "rounded exact total in a known fraction of cases. Then simulates seeded random "
        "shopping lists and compares the worst-case error 5k with the typical error, "
        "which grows much more slowly. The simulation is statistical evidence only."
    ),
    "packages": [],
}


def round_ten(n):
    """Round a whole number to the nearest ten, halves up (35 -> 40)."""
    if n < 0:
        raise ValueError("whole numbers only")
    return (n + 5) // 10 * 10


def round_first_error(numbers):
    """(sum of rounded numbers) - (exact sum)."""
    return sum(round_ten(x) for x in numbers) - sum(numbers)


def exhaustive_triples(limit):
    """Over all triples from range(limit): (count, min error, max error,
    how often rounding first gives a different rounded total)."""
    rounded = [round_ten(x) for x in range(limit)]
    count = low = high = differ = 0
    for a in range(limit):
        for b in range(limit):
            for c in range(limit):
                exact = a + b + c
                err = rounded[a] + rounded[b] + rounded[c] - exact
                low, high = min(low, err), max(high, err)
                differ += rounded[a] + rounded[b] + rounded[c] != round_ten(exact)
                count += 1
    return count, low, high, differ


def simulate(k, trials, rng):
    """Errors of 'round first' for random lists of k prices from 100 to 999."""
    errors = []
    for _ in range(trials):
        prices = [rng.randint(100, 999) for _ in range(k)]
        errors.append(round_first_error(prices))
    return errors


def main():
    print("One number: rounding to the nearest ten moves it by at most 5:")
    worst = max(abs(round_ten(n) - n) for n in range(10_000))
    print(f"  largest change over 0..9,999: {worst}")
    count, low, high, differ = exhaustive_triples(60)
    print(f"All {count:,} lists of three numbers below 60, rounded first:")
    print(f"  error ranges from {low} to +{high} (the bound is -12 to +15)")
    print("  the rounded-first total differs from the rounded exact total in")
    print(f"  {differ:,} lists ({differ / count:.0%})")
    print()
    rng = random.Random(2024)
    print("Random shopping lists (prices 100-999, 2,000 lists each, seed 2024):")
    print("  items   worst possible   largest seen   typical size (RMS)")
    for k in (5, 20, 80):
        errors = simulate(k, 2_000, rng)
        rms = statistics.fmean(e * e for e in errors) ** 0.5
        print(f"  {k:>5}   {5 * k:>14}   {max(map(abs, errors)):>12}"
              f"   {rms:>18.1f}")
    print("  The typical error grows like the square root of the number of")
    print("  items, not like the number of items: errors up and down cancel.")
    print()
    print("Epistemic status: the bound 5k is proved in the lesson; the triples")
    print("are checked completely; the shopping lists are a random simulation,")
    print("so their numbers are statistical evidence that depends on the seed.")


if __name__ == "__main__":
    main()
