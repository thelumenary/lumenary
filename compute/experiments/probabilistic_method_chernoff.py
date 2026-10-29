"""Concentration: Chebyshev versus Chernoff, and balancing sets.

For a sum S of n independent fair signs +-1, Chebyshev's inequality gives
P(S >= a) <= n / a^2, while the Chernoff bound gives P(S >= a) <=
exp(-a^2 / (2n)) - exponentially small. We compare both with the exact
binomial tail and with a seeded simulation for n = 100. Then we use the
Chernoff bound as the lesson does: colour n points red and blue at random;
for each of n given sets, the imbalance |chi(A)| exceeds sqrt(2 n ln 2n) with
probability below 1/n, so with positive probability no set does. For 64
random sets on 64 points we sample random colourings and record how often all
sets are within the bound and the best maximum imbalance found. Exact tails,
seeded simulation (statistical evidence).
"""

import math
import random

EXPERIMENT = {
    "id": "probabilistic_method_chernoff",
    "title": "Chernoff bounds and balancing sets",
    "evidence": ["exact", "statistical"],
    "lessons": ["probabilistic-method"],
    "summary": (
        "Compares the exact tail P(S >= a) of a sum of 100 random signs with "
        "Chebyshev's bound n/a^2, the Chernoff bound exp(-a^2/2n) and a "
        "seeded simulation, then colours 64 points at random and checks how "
        "often all of 64 random sets have imbalance at most sqrt(2n ln 2n), "
        "as the Chernoff-plus-union-bound argument predicts. Exact tails and "
        "statistical evidence."
    ),
    "packages": [],
}


def exact_tail(n, a):
    """P(S >= a) for S a sum of n fair +-1 signs (S = 2H - n, H binomial)."""
    need = math.ceil((n + a) / 2)
    return sum(math.comb(n, h) for h in range(max(need, 0), n + 1)) / 2 ** n


def chebyshev_bound(n, a):
    """Chebyshev: P(S >= a) <= P(|S| >= a) <= n / a^2 (a > 0)."""
    return min(1.0, n / a ** 2)


def chernoff_bound(n, a):
    """Chernoff: P(S >= a) <= exp(-a^2 / (2n))."""
    return math.exp(-a * a / (2 * n))


def simulate_tail(n, a, trials, rng):
    """Fraction of seeded trials with S >= a, using random bit strings."""
    hits = 0
    for _ in range(trials):
        heads = bin(rng.getrandbits(n)).count("1")
        hits += 2 * heads - n >= a
    return hits / trials


def random_sets(n_points, n_sets, rng):
    """Each set contains each point independently with probability 1/2."""
    return [[i for i in range(n_points) if rng.random() < 0.5]
            for _ in range(n_sets)]


def max_imbalance(colouring, sets):
    """max over sets A of |sum of colours (+-1) of the points in A|."""
    return max(abs(sum(colouring[i] for i in a)) for a in sets)


def main():
    n = 100
    rng = random.Random(2024)
    print(f"Sum of n = {n} random signs: P(S >= a)")
    print(f"{'a':>4} {'exact':>10} {'simulated':>10} {'Chebyshev':>10} "
          f"{'Chernoff':>10}")
    for a in (10, 20, 30, 40):
        sim = simulate_tail(n, a, 20000, rng)
        print(f"{a:>4} {exact_tail(n, a):>10.2e} {sim:>10.2e} "
              f"{chebyshev_bound(n, a):>10.2e} {chernoff_bound(n, a):>10.2e}")
    points = 64
    sets = random_sets(points, points, rng)
    bound = math.sqrt(2 * points * math.log(2 * points))
    trials = 500
    maxima = sorted(max_imbalance([rng.choice((-1, 1)) for _ in range(points)],
                                  sets) for _ in range(trials))
    within = sum(m <= bound for m in maxima)
    print(f"Balancing {points} random sets on {points} points:")
    print(f"  bound sqrt(2n ln 2n) = {bound:.1f}; random colourings within "
          f"it: {within}/{trials}")
    print(f"  maximum imbalance: median {maxima[trials // 2]}, "
          f"best {maxima[0]}, worst {maxima[-1]}")
    print()
    print("Epistemic status: the tails are exact; the simulated columns are")
    print("statistical evidence from seeded runs. The bounds themselves are")
    print("theorems (Chebyshev; Chernoff via cosh x <= exp(x^2/2)).")


if __name__ == "__main__":
    main()
