"""How fast does n! grow? Exact factorials and a famous approximation.

The number of ways to arrange n different objects is n!. This experiment
prints exact factorials next to 2^n and 10^n, finds where n! overtakes
each, counts the digits of 52! (the number of ways to shuffle a deck of
cards), and estimates how long listing all those orders would take. It
ends with Stirling's approximation n! ~ sqrt(2 pi n) (n/e)^n, a result
from analysis that is quoted here, not proved, with its exact relative
error for several n.
"""

import math

EXPERIMENT = {
    "id": "counting_principles_factorial_growth",
    "title": "How fast factorials grow: exact values and Stirling's formula",
    "evidence": ["exact", "numerical"],
    "lessons": ["counting-principles"],
    "summary": (
        "Prints exact factorials beside 2^n and 10^n, finds where n! "
        "overtakes them (n = 4 and n = 25), counts the 68 digits of 52!, "
        "estimates the time to list every shuffle of a deck, and compares "
        "n! with Stirling's approximation, whose relative error shrinks "
        "roughly like 1/(12n). Exact integers plus floating-point estimates; "
        "Stirling's formula is quoted, not proved."
    ),
    "packages": [],
}

SECONDS_PER_YEAR = 365.25 * 24 * 3600
AGE_OF_UNIVERSE_YEARS = 1.38e10


def first_n_where_factorial_exceeds(base):
    """Smallest n >= 1 with n! > base**n."""
    n = 1
    while math.factorial(n) <= base ** n:
        n += 1
    return n


def digits(n):
    """Number of decimal digits of a positive integer."""
    return len(str(n))


def stirling(n):
    """Stirling's approximation sqrt(2 pi n) (n / e)^n, as a float."""
    return math.sqrt(2 * math.pi * n) * (n / math.e) ** n


def relative_error(n):
    """(n! - Stirling) / n!, computed in floating point."""
    return (math.factorial(n) - stirling(n)) / math.factorial(n)


def years_to_list(count, per_second):
    """Years needed to list `count` items at `per_second` items a second."""
    return count / per_second / SECONDS_PER_YEAR


def main():
    print("  n            n!          2^n")
    for n in (1, 2, 3, 4, 5, 8, 10, 13):
        print(f"{n:3d} {math.factorial(n):>13,} {2 ** n:>12,}")
    print(f"n! first exceeds 2^n at n = {first_n_where_factorial_exceeds(2)},"
          f" and 10^n at n = {first_n_where_factorial_exceeds(10)}.")
    print()
    deck = math.factorial(52)
    print(f"Shuffles of a 52-card deck: 52! has {digits(deck)} digits,")
    print(f"  about {float(deck):.3e}.")
    years = years_to_list(deck, 1e9)
    print(f"  Listing a billion shuffles a second would take about "
          f"{years:.1e} years,")
    print(f"  roughly {years / AGE_OF_UNIVERSE_YEARS:.0e} times the age of "
          "the universe.")
    print()
    print("Stirling's approximation sqrt(2 pi n) (n/e)^n:")
    print("    n    relative error    1/(12n)")
    for n in (1, 2, 5, 10, 20, 52):
        print(f"  {n:3d}    {relative_error(n):.6f}        {1 / (12 * n):.6f}")
    print()
    print("Epistemic status: the factorials, powers and digit count are exact")
    print("integers; times and Stirling values are floating-point estimates.")
    print("Stirling's formula is a theorem of analysis quoted here, not")
    print("proved; the table only shows its error for six values of n.")


if __name__ == "__main__":
    main()
