"""Doubling against powers: when does 2^n overtake n^k for good?

For each k we search for the last n with 2^n <= n^k, using exact integer
arithmetic. A finite search alone cannot show that 2^n stays ahead forever,
so we add the lesson's argument: going from n to n + 1 multiplies 2^n by 2 but
n^k only by (1 + 1/n)^k, which is less than 2 once n is large enough. If
2^n > n^k holds at some n beyond that point, it holds for every larger n.
"""

EXPERIMENT = {
    "id": "exponential_logarithmic_functions_growth_race",
    "title": "Doubling against powers: when does 2^n win for good?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["exponential-logarithmic-functions"],
    "summary": (
        "Finds, with exact integers, the point from which 2^n > n^k for k = 2, 3, "
        "5, 10, and combines the search with an induction step (the ratio "
        "(1 + 1/n)^k < 2) so that the finite check proves the inequality for all "
        "larger n. Also computes the thickness of a sheet of paper folded 42 times."
    ),
    "packages": [],
}


def ratio_below_two_from(k):
    """Least n >= 1 with (n + 1)^k < 2 n^k, i.e. (1 + 1/n)^k < 2 (exact).

    The ratio decreases as n grows, so it stays below 2 from then on.
    """
    n = 1
    while (n + 1) ** k >= 2 * n ** k:
        n += 1
    return n


def crossover(k):
    """Least N such that 2^n > n^k for every n >= N (proved, not just tested).

    Checks every n up to the point where the induction step takes over.
    """
    start = ratio_below_two_from(k)
    n = start
    while 2 ** n <= n ** k:  # find a point beyond `start` where 2^n is ahead
        n += 1
    last_failure = max((m for m in range(1, n) if 2 ** m <= m ** k), default=0)
    return last_failure + 1


def holds_from(k, big_n, upto):
    """Check 2^n > n^k for all n with big_n <= n <= upto (exact)."""
    return all(2 ** n > n ** k for n in range(big_n, upto + 1))


def folded_thickness_km(folds, sheet_mm=0.1):
    """Thickness in km of a sheet of `sheet_mm` mm after `folds` doublings."""
    return sheet_mm * 2 ** folds / 1_000_000


def main():
    print("When does 2^n beat n^k for good?  (exact integer arithmetic)")
    print("   k   2^n > n^k for all n >=   (1+1/n)^k < 2 for n >=")
    for k in (2, 3, 5, 10):
        big_n = crossover(k)
        print(f"  {k:2d}   {big_n:22d}   {ratio_below_two_from(k):22d}")
    n = crossover(10)
    print(f"  e.g. 2^{n - 1} = {2 ** (n - 1):,} <= {n - 1}^10 = "
          f"{(n - 1) ** 10:,}")
    print(f"       2^{n} = {2 ** n:,} >  {n}^10 = {n ** 10:,}")
    print("  re-check by brute force up to n = 1000:",
          all(holds_from(k, crossover(k), 1000) for k in (2, 3, 5, 10)))
    print()
    print("Why the table is a proof: from the right-hand column on, each step")
    print("multiplies 2^n by 2 but n^k by less than 2. So once 2^n is ahead")
    print("there, it stays ahead; the exact search covers all smaller n.")
    print()
    km = folded_thickness_km(42)
    print(f"A 0.1 mm sheet folded 42 times would be {km:,.0f} km thick,")
    print("more than the distance to the Moon (about 384,400 km).")
    print()
    print("Epistemic status: all comparisons are exact integer computations.")
    print("Together with the induction step they prove 2^n > n^k for every")
    print("n in the stated range, for these four values of k. The folding")
    print("figure is a calculation, not a feasible experiment.")


if __name__ == "__main__":
    main()
