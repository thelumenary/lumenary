"""Geometric Brownian motion: Ito's correction is real.

We simulate dS = mu S dt + sigma S dB with mu = 0.1, sigma = 0.4, S_0 = 1 on
[0, 1] by the Euler-Maruyama scheme and compare it, path by path, with the
exact solution S_1 = exp((mu - sigma^2/2) + sigma B_1) driven by the same
Brownian increments. The strong error shrinks like sqrt(dt). The sample mean
matches e^mu, the sample median matches e^(mu - sigma^2/2), and the "ordinary
chain rule" guess exp(mu + sigma B_1) has the wrong mean e^(mu + sigma^2/2).
"""

import math
import random
import statistics

EXPERIMENT = {
    "id": "stochastic_processes_gbm",
    "title": "Geometric Brownian motion: Euler-Maruyama versus Ito's formula",
    "evidence": ["numerical", "statistical"],
    "lessons": ["stochastic-processes"],
    "summary": (
        "Simulates 1000 seeded paths of dS = mu S dt + sigma S dB by "
        "Euler-Maruyama with 2^2 to 2^8 steps and compares with the exact Ito "
        "solution on the same Brownian increments: the strong error decays like "
        "dt^(1/2). Sample mean and median of S_1 match e^mu and "
        "e^(mu - sigma^2/2); the naive chain-rule solution has the wrong mean. "
        "Statistical evidence for finitely many paths."
    ),
    "packages": [],
}

MU, SIGMA = 0.1, 0.4


def exact_solution(s0, mu, sigma, t, b):
    """Ito's solution S_t = s0 exp((mu - sigma^2/2) t + sigma B_t)."""
    return s0 * math.exp((mu - sigma ** 2 / 2) * t + sigma * b)


def euler_maruyama(s0, mu, sigma, increments, dt):
    """Iterate S <- S + mu S dt + sigma S dB over the given increments."""
    s = s0
    for db in increments:
        s += mu * s * dt + sigma * s * db
    return s


def coarsen(increments, factor):
    """Sum consecutive blocks of increments (same path, coarser grid)."""
    return [math.fsum(increments[i:i + factor])
            for i in range(0, len(increments), factor)]


def main():
    rng = random.Random(1973)
    paths, fine = 1000, 2 ** 8
    incs = [[rng.gauss(0.0, math.sqrt(1 / fine)) for _ in range(fine)]
            for _ in range(paths)]
    finals = [math.fsum(inc) for inc in incs]
    exact = [exact_solution(1.0, MU, SIGMA, 1.0, b) for b in finals]
    print("Strong error E|S_1(Euler) - S_1(exact)| on the same paths:")
    print("  steps       dt       error   error/sqrt(dt)")
    for m in [2, 4, 6, 8]:
        n = 2 ** m
        errs = [abs(euler_maruyama(1.0, MU, SIGMA, coarsen(inc, fine // n),
                                   1 / n) - ex)
                for inc, ex in zip(incs, exact)]
        err = statistics.fmean(errs)
        print(f"  {n:>5}   {1 / n:.5f}   {err:.5f}   {err / math.sqrt(1 / n):.4f}")
    print()
    naive = [math.exp(MU + SIGMA * b) for b in finals]
    print(f"Sample mean of exact S_1:   {statistics.fmean(exact):.4f}"
          f"   (theory e^mu = {math.exp(MU):.4f})")
    print(f"Sample median of exact S_1: {statistics.median(exact):.4f}"
          f"   (theory e^(mu - s^2/2) = {math.exp(MU - SIGMA ** 2 / 2):.4f})")
    print(f"Mean of naive exp(mu + s B_1): {statistics.fmean(naive):.4f}"
          f" (= e^(mu + s^2/2) = {math.exp(MU + SIGMA ** 2 / 2):.4f}, wrong)")
    print("The ordinary chain rule would predict the naive formula; Ito's")
    print("formula adds -sigma^2/2 to the exponent, and only then is the mean")
    print("e^(mu t), as dS = mu S dt + sigma S dB requires.")
    print()
    print("Epistemic status: seeded simulations with 1000 paths (statistical")
    print("evidence; sample means carry errors of a few percent) and floating")
    print("point. The rate dt^(1/2) and the formulas are theorems; the run")
    print("illustrates them.")


if __name__ == "__main__":
    main()
