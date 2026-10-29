"""Multiple testing: why twenty tests find a 'significant' effect that is not there.

We simulate many studies, each running m two-sided z-tests. Under a true null
hypothesis the test statistic is N(0, 1); under a real effect it is N(3, 1).
We check that null p-values are uniformly distributed, measure the family-wise
error rate (the chance of at least one false positive) with and without the
Bonferroni correction, and compare Bonferroni with the Benjamini-Hochberg
procedure, which controls the false discovery rate instead.
"""

import math
import random

EXPERIMENT = {
    "id": "statistics_multiple_testing",
    "title": "Multiple testing: false positives, Bonferroni and Benjamini-Hochberg",
    "evidence": ["statistical", "exact"],
    "lessons": ["statistics"],
    "summary": (
        "Seeded simulation of studies that each run many z-tests. Null p-values come "
        "out uniform; with 20 true nulls at level 0.05 the chance of at least one false "
        "positive is about 0.64 (exactly 1 - 0.95^20), and Bonferroni brings it below "
        "0.05. With 10 real effects among 50 tests, Benjamini-Hochberg finds more of "
        "them than Bonferroni while keeping the proportion of false discoveries low."
    ),
    "packages": [],
}


def p_value(z):
    """Two-sided p-value of a standard normal test statistic z."""
    return math.erfc(abs(z) / math.sqrt(2))


def bonferroni(pvalues, alpha):
    """Indices rejected by Bonferroni: p <= alpha / m."""
    m = len(pvalues)
    return {i for i, p in enumerate(pvalues) if p <= alpha / m}


def benjamini_hochberg(pvalues, alpha):
    """Indices rejected by the Benjamini-Hochberg step-up procedure (1995).

    Sort the p-values; find the largest k with p_(k) <= k alpha / m and reject
    the k smallest.
    """
    m = len(pvalues)
    order = sorted(range(m), key=lambda i: pvalues[i])
    k_max = 0
    for rank, i in enumerate(order, start=1):
        if pvalues[i] <= rank * alpha / m:
            k_max = rank
    return set(order[:k_max])


def simulate(rng, m, effects, shift=3.0):
    """p-values for one study: the first ``effects`` tests have a real effect."""
    return [p_value(rng.gauss(shift if i < effects else 0.0, 1.0))
            for i in range(m)]


def main():
    rng = random.Random(1995)
    alpha, reps = 0.05, 2000
    deciles = [0] * 10
    any_raw = any_bonf = 0
    for _ in range(reps):
        ps = simulate(rng, 20, 0)
        for p in ps:
            deciles[min(int(p * 10), 9)] += 1
        any_raw += any(p <= alpha for p in ps)
        any_bonf += bool(bonferroni(ps, alpha))
    print(f"{reps} studies, each with 20 true null hypotheses, alpha = 0.05")
    print("Null p-values per tenth of [0, 1] (uniform means about 4000 each):")
    print("  " + " ".join(f"{c:>5}" for c in deciles))
    print(f"P(at least one p <= 0.05), uncorrected: {any_raw / reps:.3f}"
          f"  (exact 1 - 0.95^20 = {1 - 0.95 ** 20:.3f})")
    print(f"P(at least one rejection), Bonferroni:  {any_bonf / reps:.3f}"
          f"  (guaranteed <= 0.05)")
    print()
    print("Studies with 50 tests, of which 10 have a real effect (mean 3):")
    totals = {"Bonferroni": [0, 0], "Benjamini-Hochberg": [0, 0]}
    fdp_bh = 0.0
    for _ in range(reps):
        ps = simulate(rng, 50, 10)
        for name, rule in [("Bonferroni", bonferroni),
                           ("Benjamini-Hochberg", benjamini_hochberg)]:
            rejected = rule(ps, alpha)
            true_hits = sum(1 for i in rejected if i < 10)
            totals[name][0] += true_hits
            totals[name][1] += len(rejected) - true_hits
            if name == "Benjamini-Hochberg" and rejected:
                fdp_bh += (len(rejected) - true_hits) / len(rejected)
    for name, (hits, false) in totals.items():
        print(f"  {name:<19} real effects found {hits / reps:5.2f} of 10,"
              f" false positives {false / reps:4.2f}")
    print(f"  Average false discovery proportion for BH: {fdp_bh / reps:.3f}")
    print("  (BH guarantees at most 0.05 x 40/50 = 0.04 for independent tests)")
    print()
    print("Epistemic status: seeded Monte Carlo simulation (2000 studies per")
    print("scenario), so every proportion has sampling error of order 0.01.")
    print("The guarantees quoted (Bonferroni's union bound, the BH theorem for")
    print("independent tests) are theorems; the simulation only illustrates")
    print("them in two scenarios.")


if __name__ == "__main__":
    main()
