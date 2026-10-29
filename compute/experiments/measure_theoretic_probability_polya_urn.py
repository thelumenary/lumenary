"""Polya's urn: a martingale that converges to a random limit.

An urn starts with one red and one blue ball. At each step draw a ball,
return it, and add another of the same colour. The fraction of red balls
M_n = R_n / (n + 2) is a martingale. We verify exactly (with fractions) that
the martingale property holds and that after n draws the number of red balls
is uniformly distributed on {1, ..., n + 1}; so the almost-sure limit of M_n,
which exists by Doob's convergence theorem, is uniform on [0, 1]. A seeded
simulation shows individual urns settling down at different values.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "measure_theoretic_probability_polya_urn",
    "title": "Polya's urn: a martingale with a random limit",
    "evidence": ["exact", "statistical"],
    "lessons": ["measure-theoretic-probability"],
    "summary": (
        "Computes exactly the distribution of red balls in Polya's urn after n "
        "draws (uniform on 1..n+1) and checks the martingale identity "
        "E[M_(n+1) | R_n = r] = M_n with fractions for every r and n <= 30. A "
        "seeded simulation of 1000 urns shows each fraction settling and the "
        "limits spreading out uniformly. The exact part is a finite check; the "
        "convergence is Doob's theorem."
    ),
    "packages": [],
}


def red_distribution(n):
    """Exact law of the number of red balls after n draws, as {red: prob}."""
    if n < 0:
        raise ValueError("n must be non-negative")
    dist = {1: Fraction(1)}
    for step in range(n):
        total = step + 2
        new = {}
        for red, p in dist.items():
            up = p * Fraction(red, total)
            new[red + 1] = new.get(red + 1, 0) + up
            new[red] = new.get(red, 0) + p - up
        dist = new
    return dist


def martingale_defect(n, red):
    """E[M_(n+1) | R_n = red] - M_n, exactly (it should be 0)."""
    total = n + 2
    p_up = Fraction(red, total)
    expected = (p_up * Fraction(red + 1, total + 1)
                + (1 - p_up) * Fraction(red, total + 1))
    return expected - Fraction(red, total)


def run_urn(steps, rng):
    """Fractions of red balls after each of the given number of draws."""
    red, total, path = 1, 2, []
    for _ in range(steps):
        if rng.random() < red / total:
            red += 1
        total += 1
        path.append(red / total)
    return path


def main():
    print("Exact law of R_n (number of red balls) after n draws:")
    for n in [1, 2, 3, 10]:
        dist = red_distribution(n)
        values = ", ".join(str(v) for v in sorted(set(dist.values())))
        print(f"  n = {n:>2}: R_n takes each value 1..{n + 1} with prob. {values}")
    worst = max(abs(martingale_defect(n, r))
                for n in range(31) for r in range(1, n + 2))
    print("max |E[M_(n+1) | R_n] - M_n| over n <= 30, all r:", worst)
    print()
    rng = random.Random(1923)
    print("Six urns, fraction of red after 10, 100, 1000, 4000 draws:")
    for i in range(6):
        path = run_urn(4000, rng)
        cells = "  ".join(f"{path[k - 1]:.3f}" for k in [10, 100, 1000, 4000])
        print(f"  urn {i + 1}: {cells}")
    limits = [run_urn(300, rng)[-1] for _ in range(1000)]
    deciles = [0] * 10
    for x in limits:
        deciles[min(int(x * 10), 9)] += 1
    print("1000 urns after 300 draws, counts per tenth of [0, 1]:")
    print("  ", deciles, "(uniform: about 100 each)")
    print()
    print("Epistemic status: the uniform law and the martingale identity are")
    print("exact computations for n <= 30 (the lesson proves them for all n).")
    print("The urn runs are seeded simulations: statistical illustration of")
    print("Doob's theorem (almost-sure convergence), not a proof of it.")


if __name__ == "__main__":
    main()
