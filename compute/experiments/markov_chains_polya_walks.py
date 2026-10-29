"""Polya's theorem in numbers: does a random walk come home?

Simple random walk on Z^d returns to the origin with probability 1 when
d = 1 or 2 and with probability less than 1 when d = 3. The criterion is
whether the expected number of returns, sum_n P(S_2n = 0), is infinite. We
compute these return probabilities: exactly from C(2n, n)/4^n in d = 1 and its
square in d = 2, and from the trinomial formula in d = 3. The partial sums
grow like sqrt(n) and log(n) in d = 1 and 2, but level off in d = 3. A numpy
simulation of 1,000 walks of 1,000 steps adds the fraction that came back.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "markov_chains_polya_walks",
    "title": "Polya's theorem: return probabilities in one, two and three dimensions",
    "evidence": ["numerical", "statistical"],
    "lessons": ["markov-chains"],
    "summary": (
        "Computes P(S_2n = 0) for simple random walk in dimensions 1, 2 and 3 and the "
        "partial sums of the expected number of returns: they diverge like sqrt(n) and "
        "log(n) in dimensions 1 and 2 and converge in dimension 3. A seeded simulation "
        "of 1,000 walks of 1,000 steps shows how many return. Finite computations "
        "illustrate, but cannot prove, divergence or convergence."
    ),
    "packages": ["numpy"],
}


def return_probs_1d(n_max):
    """[P(S_2n = 0) for n = 0..n_max] in d = 1, via a_(n+1) = a_n (2n+1)/(2n+2)."""
    a = [1.0]
    for n in range(n_max):
        a.append(a[-1] * (2 * n + 1) / (2 * n + 2))
    return a


def return_prob_3d(n):
    """P(S_2n = 0) in d = 3: (1/6^(2n)) C(2n, n) sum_(i+j+k=n) (n!/(i! j! k!))^2.

    Computed with logarithms of factorials (math.lgamma).
    """
    lf = [math.lgamma(m + 1) for m in range(2 * n + 1)]
    log_c = lf[2 * n] - 2 * lf[n]
    total = 0.0
    for i in range(n + 1):
        for j in range(n - i + 1):
            k = n - i - j
            total += math.exp(2 * (lf[n] - lf[i] - lf[j] - lf[k])
                              + log_c - 2 * n * math.log(6))
    return total


def simulate_returns(d, walks=1000, steps=1000, seed=1921):
    """Fraction of walks in Z^d that revisit the origin within ``steps``."""
    rng = np.random.default_rng(seed + d)
    axis = rng.integers(0, d, size=(walks, steps))
    sign = rng.choice(np.array([-1, 1], dtype=np.int16), size=(walks, steps))
    at_origin = np.ones((walks, steps), dtype=bool)
    for c in range(d):
        position = np.cumsum(np.where(axis == c, sign, 0), axis=1)
        at_origin &= position == 0
    return float(at_origin.any(axis=1).mean())


def main():
    a = return_probs_1d(10000)
    print("Expected number of returns up to time 2n: sum of P(S_2k = 0), k = 1..n")
    print(f"{'n':>7} {'d = 1':>9} {'2 sqrt(n/pi)':>13} {'d = 2':>8}"
          f" {'ln(n)/pi':>9}")
    for n in [10, 100, 1000, 10000]:
        s1 = sum(a[1:n + 1])
        s2 = sum(x * x for x in a[1:n + 1])
        print(f"{n:>7} {s1:>9.2f} {2 * math.sqrt(n / math.pi):>13.2f}"
              f" {s2:>8.3f} {math.log(n) / math.pi:>9.3f}")
    u3 = [return_prob_3d(n) for n in range(1, 61)]
    print("d = 3: partial sums at n = 10, 20, 40, 60:",
          ", ".join(f"{sum(u3[:n]):.3f}" for n in [10, 20, 40, 60]))
    tail = sum(2 * (3 / (4 * math.pi * n)) ** 1.5 for n in range(61, 200001))
    print(f"       plus the asymptotic tail estimate {tail:.3f}"
          f" gives about {sum(u3) + tail:.3f}")
    print("       (exact value 0.516..., so the return probability is")
    print("       0.516/1.516 = 0.34 < 1: the walk is transient)")
    print()
    print("Simulation: fraction of 1000 walks back at the origin by step 1000")
    for d in [1, 2, 3]:
        print(f"  d = {d}: {simulate_returns(d):.3f}")
    print()
    print("Epistemic status: the return probabilities are computed exactly up")
    print("to floating-point rounding, but a partial sum can never show that a")
    print("series diverges; the divergence for d = 1, 2 is proved in Lean and")
    print("convergence for d = 3 follows from P(S_2n = 0) <= C n^(-3/2). The")
    print("simulation is statistical evidence about finite walks only.")


if __name__ == "__main__":
    main()
