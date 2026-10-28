"""A random walk on the integers: what can statistics tell us?

Start at 0. At each step flip a fair coin and move +1 or -1. How likely is
the walker to come back to 0 within h steps? We estimate this by simulating
many walks (with a fixed seed, so the run is reproducible), attach a 95%
confidence interval, and compare with the exact answer, which is known:

    P(first return within 2m steps) = 1 - C(2m, m) / 4^m.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from fractions import Fraction
from math import comb, sqrt
import random
import textwrap

EXPERIMENT = {
    "id": "random_walk_statistics",
    "title": "Does a random walk come home? Statistical evidence",
    "evidence": ["statistical", "exact"],
    "lessons": ["integers"],
    "summary": (
        "Simulates 4000 seeded random walks on the integers, estimates the chance "
        "of returning to 0 within 2, 10, 100 and 1000 steps with 95% confidence "
        "intervals, and compares with the exact formula 1 - C(2m, m)/4^m. "
        "Agreement is statistical evidence, which can never be certain and cannot "
        "show that a return eventually happens with probability 1 (Polya's theorem)."
    ),
    "packages": [],
}

SEED = 20260101
HORIZONS = (2, 10, 100, 1000)


def first_return_time(rng, max_steps):
    """Walk from 0 with fair +1/-1 steps; return the first time back at 0, or None if not within max_steps."""
    position = 0
    for t in range(1, max_steps + 1):
        position += 1 if rng.getrandbits(1) else -1
        if position == 0:
            return t
    return None


def simulate(n_walks, max_steps, seed):
    """Run ``n_walks`` independent walks with a seeded generator; return their first-return times."""
    rng = random.Random(seed)
    return [first_return_time(rng, max_steps) for _ in range(n_walks)]


def returned_within(times, horizon):
    """How many walks (from :func:`simulate`) returned to 0 within ``horizon`` steps."""
    return sum(1 for t in times if t is not None and t <= horizon)


def exact_return_probability(horizon):
    """Exact P(first return to 0 within ``horizon`` steps) = 1 - C(2m, m)/4^m with m = horizon // 2.

    Returns a Fraction. Returns are only possible at even times.
    """
    if horizon < 0:
        raise ValueError("horizon must be non-negative")
    m = horizon // 2
    return 1 - Fraction(comb(2 * m, m), 4 ** m)


def wilson_interval(successes, trials, z=1.96):
    """Wilson score confidence interval for a proportion (95% for z = 1.96).

    Returns (low, high). It behaves better than "p +/- 1.96 * standard error"
    when p is close to 0 or 1.
    """
    if trials <= 0:
        raise ValueError("trials must be positive")
    if not 0 <= successes <= trials:
        raise ValueError("successes must be between 0 and trials")
    p = successes / trials
    denom = 1 + z * z / trials
    centre = (p + z * z / (2 * trials)) / denom
    half = z * sqrt(p * (1 - p) / trials + z * z / (4 * trials * trials)) / denom
    return max(0.0, centre - half), min(1.0, centre + half)


def main():
    n_walks = 4000
    times = simulate(n_walks, max(HORIZONS), SEED)
    print(f"{n_walks} random walks from 0 (fair coin, random.Random(seed={SEED})).")
    print("Did the walk come back to 0 within h steps?")
    print()
    print(f"  {'h':>5} {'returned':>9} {'estimate':>9}   {'95% interval':<16} {'exact':>8}  inside?")
    inside_count = 0
    for h in HORIZONS:
        k = returned_within(times, h)
        low, high = wilson_interval(k, n_walks)
        exact = float(exact_return_probability(h))
        inside = low <= exact <= high
        inside_count += inside
        print(f"  {h:>5} {k:>9} {k / n_walks:>9.4f}   [{low:.4f}, {high:.4f}] {exact:>8.4f}  {'yes' if inside else 'no'}")
    print()
    print("Same question (h = 100), five different seeds, 1000 walks each:")
    estimates = [returned_within(simulate(1000, 100, seed), 100) / 1000 for seed in range(1, 6)]
    print("  " + "  ".join(f"{e:.3f}" for e in estimates)
          + f"   (exact {float(exact_return_probability(100)):.3f})")
    print("  Different seeds give different estimates: that spread is sampling error.")
    print()
    never = n_walks - returned_within(times, max(HORIZONS))
    print(f"{never} walks had not returned after {max(HORIZONS)} steps. Will they ever?")
    print("Polya's theorem (1921) says yes, with probability 1 - but no finite simulation")
    print("can show that: every finite run leaves some walks still out, and a true")
    print("probability of 0.9999 would look just like 1 in a sample of this size.")
    print()
    print(textwrap.fill(
        f"Epistemic status: statistical evidence. The exact value fell inside the "
        f"95% interval in {inside_count} of {len(HORIZONS)} rows, which supports the "
        "formula but cannot prove it (about 1 interval in 20 misses by chance). "
        "The formula and Polya's theorem are proved mathematically; this "
        "simulation only illustrates them.",
        width=78,
    ))


if __name__ == "__main__":
    main()
