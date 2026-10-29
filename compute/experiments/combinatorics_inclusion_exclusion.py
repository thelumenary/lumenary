"""Inclusion-exclusion and the pigeonhole principle, counted exactly.

Three checks. (1) How many of 1..N are divisible by 2, 3 or 5? Counting
every number agrees with the inclusion-exclusion formula. (2) Derangements:
the number of ways to hand back n hats so that nobody gets their own is found
by listing all n! arrangements (n <= 8) and agrees with the general
inclusion-exclusion formula n! * sum (-1)^k / k!; the fraction approaches
1/e. (3) Birthdays: the exact probability that k people (365 equally likely
days) share a birthday passes 1/2 at k = 23, but only the pigeonhole
principle makes it certain, at k = 366.
"""

import itertools
import math
from fractions import Fraction

EXPERIMENT = {
    "id": "combinatorics_inclusion_exclusion",
    "title": "Inclusion-exclusion, derangements and birthdays",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["combinatorics"],
    "summary": (
        "Counts the numbers up to N divisible by 2, 3 or 5 directly and by "
        "inclusion-exclusion; counts derangements of n hats by listing all n! "
        "arrangements (n <= 8) and by the inclusion-exclusion formula, watching "
        "the fraction approach 1/e; and computes the exact birthday "
        "probabilities, which pass 1/2 at 23 people but reach 1 only at 366, "
        "where the pigeonhole principle applies."
    ),
    "packages": [],
}


def divisible_count_direct(n, divisors):
    """How many of 1..n are divisible by at least one of the divisors."""
    return sum(1 for m in range(1, n + 1) if any(m % d == 0 for d in divisors))


def divisible_count_ie(n, divisors):
    """The same count by inclusion-exclusion over all non-empty subsets."""
    total = 0
    for r in range(1, len(divisors) + 1):
        for subset in itertools.combinations(divisors, r):
            lcm = math.lcm(*subset)
            total += (-1) ** (r + 1) * (n // lcm)
    return total


def derangements_brute(n):
    """Arrangements of 0..n-1 with no element in its own place, by listing."""
    return sum(1 for p in itertools.permutations(range(n))
               if all(p[i] != i for i in range(n)))


def derangements_ie(n):
    """n! * sum_{k=0}^{n} (-1)^k / k!, the inclusion-exclusion count."""
    return sum((-1) ** k * math.factorial(n) // math.factorial(k)
               for k in range(n + 1))


def shared_birthday(k, days=365):
    """Exact probability that some two of k people share a birthday."""
    if k > days:
        return Fraction(1)
    none = Fraction(1)
    for i in range(k):
        none *= Fraction(days - i, days)
    return 1 - none


def main():
    print("1. Numbers in 1..N divisible by 2, 3 or 5")
    for n in (100, 1000, 30000):
        direct = divisible_count_direct(n, (2, 3, 5))
        print(f"   N = {n:5d}: counted {direct:5d}, inclusion-exclusion "
              f"{divisible_count_ie(n, (2, 3, 5)):5d}")
    print()
    print("2. Derangements (nobody gets their own hat)")
    print("    n   listed   formula   fraction of n!   1/e = 0.367879")
    for n in range(1, 9):
        listed = derangements_brute(n)
        frac = listed / math.factorial(n)
        print(f"   {n:2d}   {listed:6d}   {derangements_ie(n):7d}   "
              f"{frac:14.6f}")
    print()
    print("3. Shared birthdays among k people (365 equally likely days)")
    print("      k   P(shared)   P(no two share)")
    for k in (10, 22, 23, 50, 70, 365, 366):
        p = shared_birthday(k)
        none = "exactly 0" if p == 1 else f"{float(1 - p):.3e}"
        print(f"   {k:4d}   {float(p):9.6f}   {none}")
    print()
    print("Epistemic status: exact integer and rational arithmetic. Parts 1")
    print("and 2 compare a direct count with a formula over a finite range")
    print("(evidence; the lesson proves the formulas). Part 3 is an exact")
    print("model calculation assuming 365 equally likely, independent days.")


if __name__ == "__main__":
    main()
