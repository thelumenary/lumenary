"""Do 95% confidence intervals cover the truth 95% of the time?

Part 1 is exact. For a binomial count X ~ Bin(n, p), the coverage of an
interval method is the sum of P(X = k) over the k whose interval contains p.
We compute it for the textbook Wald interval p_hat +- 1.96 sqrt(p_hat(1 -
p_hat)/n) and for the Wilson score interval. Part 2 is a seeded simulation:
for normal samples of size 5 we compare the z-interval with known sigma, the
Student t-interval, and the naive z-interval that plugs in the sample
standard deviation.
"""

import math
import random
import statistics

EXPERIMENT = {
    "id": "statistics_interval_coverage",
    "title": "How often do 95% confidence intervals really cover the truth?",
    "evidence": ["exact", "statistical"],
    "lessons": ["statistics"],
    "summary": (
        "Computes the exact coverage probability of the Wald and Wilson 95% intervals "
        "for a binomial proportion for several n and p (the Wald interval can fall far "
        "below 95%), then simulates 4,000 normal samples of size 5 to compare the "
        "z-interval, the Student t-interval and the naive z-interval with the sample "
        "standard deviation, which undercovers."
    ),
    "packages": [],
}

Z = 1.959963984540054  # the 97.5% point of N(0, 1)
T4 = 2.776445105197799  # the 97.5% point of Student's t with 4 degrees of freedom


def binomial_pmf(n, k, p):
    """P(X = k) for X ~ Bin(n, p), computed with logarithms (no overflow)."""
    if p in (0.0, 1.0):
        return float(k == round(n * p))
    log_c = math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)
    return math.exp(log_c + k * math.log(p) + (n - k) * math.log(1 - p))


def wald_interval(k, n, z=Z):
    """The Wald interval p_hat +- z sqrt(p_hat (1 - p_hat) / n)."""
    p_hat = k / n
    half = z * math.sqrt(p_hat * (1 - p_hat) / n)
    return p_hat - half, p_hat + half


def wilson_interval(k, n, z=Z):
    """The Wilson score interval (Wilson, 1927)."""
    p_hat = k / n
    denom = 1 + z * z / n
    centre = (p_hat + z * z / (2 * n)) / denom
    half = z / denom * math.sqrt(p_hat * (1 - p_hat) / n + z * z / (4 * n * n))
    return centre - half, centre + half


def coverage(method, n, p):
    """Exact probability that the interval method(X, n) contains p."""
    total = 0.0
    for k in range(n + 1):
        low, high = method(k, n)
        if low <= p <= high:
            total += binomial_pmf(n, k, p)
    return total


def simulate_normal_intervals(n=5, reps=4000, seed=2024):
    """Coverage of three 95% intervals for the mean of N(10, 2^2) samples.

    Returns (z with known sigma, t with S, naive z with S) as proportions.
    """
    rng = random.Random(seed)
    mu, sigma = 10.0, 2.0
    hits = [0, 0, 0]
    for _ in range(reps):
        xs = [rng.gauss(mu, sigma) for _ in range(n)]
        mean, s = statistics.fmean(xs), statistics.stdev(xs)
        for j, half in enumerate([Z * sigma / math.sqrt(n),
                                  T4 * s / math.sqrt(n),
                                  Z * s / math.sqrt(n)]):
            hits[j] += abs(mean - mu) <= half
    return [h / reps for h in hits]


def main():
    print("Part 1 (exact): coverage of nominal 95% intervals for a proportion")
    print(f"{'n':>6} {'p':>6} {'Wald':>8} {'Wilson':>8}")
    for n in [10, 30, 100, 1000]:
        for p in [0.5, 0.2, 0.05]:
            print(f"{n:>6} {p:>6} {coverage(wald_interval, n, p):>8.3f}"
                  f" {coverage(wilson_interval, n, p):>8.3f}")
    print("The Wald interval can undercover badly when n p is small; the")
    print("Wilson interval stays much closer to 95%.")
    print()
    print("Part 2 (simulation, 4000 normal samples of size n = 5):")
    known, t_int, naive = simulate_normal_intervals()
    print(f"  z-interval, sigma known:         {known:.3f}")
    print(f"  t-interval, S and t(4) = 2.776:  {t_int:.3f}")
    print(f"  naive z-interval with S:         {naive:.3f}")
    print("Plugging S into the z-interval ignores the uncertainty in S;")
    print("Student's t-distribution corrects for it exactly for normal data.")
    print()
    print("Epistemic status: part 1 is an exact computation of coverage")
    print("probabilities (in floating point) for the listed n and p. Part 2 is")
    print("a seeded Monte Carlo estimate with standard error about 0.004; it")
    print("illustrates, but does not prove, that the t-interval has coverage")
    print("exactly 95% for normal samples (a theorem).")


if __name__ == "__main__":
    main()
