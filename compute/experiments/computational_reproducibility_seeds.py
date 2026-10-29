"""Seeds, pseudorandom streams and honest statistical claims.

A pseudorandom generator is a deterministic function of its seed, so a
Monte Carlo computation is reproducible bit for bit once the generator, its
version and the seed are fixed - which the experiment checks with a 64-bit
fingerprint (FNV-1a) of the output. Different seeds give different estimates;
the honest report is an estimate with a standard error. Over 200 seeds the
experiment counts how often the nominal 95% interval contains the true value
of the integral of exp(-x^2) over [0, 1], known exactly through erf. That
coverage count is statistical evidence about the method, not a proof.
"""

import math
import random
import statistics

EXPERIMENT = {
    "id": "computational_reproducibility_seeds",
    "title": "Seeds, fingerprints and confidence intervals in Monte Carlo",
    "evidence": ["exact", "statistical"],
    "lessons": ["computational-reproducibility"],
    "summary": (
        "Estimates the integral of exp(-x^2) on [0, 1] by Monte Carlo. With a fixed "
        "seed two runs agree bit for bit (checked by a 64-bit FNV-1a fingerprint); "
        "different seeds give different estimates, reported with standard errors. "
        "Over 200 seeds it counts how often the nominal 95% interval covers the "
        "exact value (via erf): statistical evidence about the method."
    ),
    "packages": [],
}

TRUE_VALUE = math.sqrt(math.pi) / 2 * math.erf(1.0)


def fnv1a64(text):
    """64-bit FNV-1a hash of a string: a cheap fingerprint of an output."""
    h = 0xCBF29CE484222325
    for byte in text.encode("utf-8"):
        h ^= byte
        h = (h * 0x100000001B3) % 2 ** 64
    return h


def monte_carlo(seed, n):
    """Estimate the integral of exp(-x^2) on [0, 1]; return (mean, std. error)."""
    rng = random.Random(seed)
    values = [math.exp(-rng.random() ** 2) for _ in range(n)]
    return statistics.fmean(values), statistics.stdev(values) / math.sqrt(n)


def coverage(seeds, n, z=1.96):
    """How many of the intervals mean +- z*SE (one per seed) contain the truth."""
    hits = 0
    for seed in seeds:
        mean, se = monte_carlo(seed, n)
        hits += abs(mean - TRUE_VALUE) <= z * se
    return hits


def minstd(seed, k):
    """First k outputs of the Park-Miller 'minimal standard' generator."""
    out, x = [], seed
    for _ in range(k):
        x = 16807 * x % (2 ** 31 - 1)
        out.append(x)
    return out


def main():
    print(f"Target: integral of exp(-x^2) on [0, 1] = {TRUE_VALUE:.15f}")
    print("Park-Miller generator from seed 42: "
          + ", ".join(map(str, minstd(42, 3))) + ", ...")
    print()
    run_a, run_b = monte_carlo(2024, 5000), monte_carlo(2024, 5000)
    fa, fb = fnv1a64(repr(run_a)), fnv1a64(repr(run_b))
    print(f"seed 2024, run A: {run_a[0]!r}  fingerprint {fa:016x}")
    print(f"seed 2024, run B: {run_b[0]!r}  fingerprint {fb:016x}")
    print(f"bit-for-bit identical: {run_a == run_b}")
    covers = abs(run_a[0] - TRUE_VALUE) <= 1.96 * run_a[1]
    print(f"its 95% interval +- {1.96 * run_a[1]:.6f} covers the truth: {covers}")
    print()
    print("Same method, five other seeds (estimate +- 1.96 standard errors):")
    for seed in range(1, 6):
        mean, se = monte_carlo(seed, 5000)
        print(f"  seed {seed}: {mean:.6f} +- {1.96 * se:.6f}")
    hits = coverage(range(100, 300), 1000)
    print(f"Nominal 95% intervals (n = 1000) covering the truth: {hits}/200")
    print()
    print("Epistemic status: the identity of the two seeded runs is exact (same")
    print("generator, same seed, same Python); the estimates are statistical, and")
    print("the coverage count is statistical evidence that the intervals behave")
    print("as advertised for this integrand. Python guarantees the random()")
    print("stream for a given seed, but other methods may change between versions.")


if __name__ == "__main__":
    main()
