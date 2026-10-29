"""The central limit theorem seen through characteristic functions.

For a fair +-1 coin X, the characteristic function is E[exp(itX)] = cos t, so
the normalised sum S_n / sqrt(n) of n independent coins has characteristic
function cos(t / sqrt(n))^n. We measure how fast it approaches exp(-t^2 / 2),
the characteristic function of the standard normal law, on [-3, 3]; the
error behaves like t^4 exp(-t^2/2) / (12 n). Then we compare the exact
binomial distribution function with the normal one (the Berry-Esseen rate is
1/sqrt(n), slower because the distribution of S_n has jumps).
"""

import math

EXPERIMENT = {
    "id": "measure_theoretic_probability_clt_charfun",
    "title": "The CLT through characteristic functions",
    "evidence": ["numerical"],
    "lessons": ["measure-theoretic-probability"],
    "summary": (
        "Computes the characteristic function cos(t/sqrt(n))^n of a normalised "
        "sum of n fair +-1 coins on a grid in [-3, 3] and its distance from "
        "exp(-t^2/2) for n up to 10^4, showing the 1/n decay predicted by the "
        "Taylor expansion, then the exact binomial CDF error, which decays like "
        "1/sqrt(n). Floating-point numerical evidence on finite grids only."
    ),
    "packages": [],
}


def charfun_sum(t, n):
    """Characteristic function of S_n / sqrt(n) for fair +-1 steps."""
    if n < 1:
        raise ValueError("n must be positive")
    return math.cos(t / math.sqrt(n)) ** n


def max_charfun_error(n, t_max=3.0, points=601):
    """max over a grid of |phi_n(t) - exp(-t^2/2)| for |t| <= t_max."""
    ts = [-t_max + 2 * t_max * k / (points - 1) for k in range(points)]
    return max(abs(charfun_sum(t, n) - math.exp(-t * t / 2)) for t in ts)


def normal_cdf(x):
    """Standard normal distribution function."""
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def binomial_cdf_error(n):
    """sup over the jump points of |P(S_n/sqrt(n) <= x) - Phi(x)|."""
    worst, cum = 0.0, 0.0
    for k in range(n + 1):
        x = (2 * k - n) / math.sqrt(n)
        left = cum
        cum += math.exp(math.lgamma(n + 1) - math.lgamma(k + 1)
                        - math.lgamma(n - k + 1) - n * math.log(2))
        phi = normal_cdf(x)
        worst = max(worst, abs(left - phi), abs(cum - phi))
    return worst


def main():
    print("Characteristic function of S_n/sqrt(n) versus exp(-t^2/2):")
    print("      n   max error on [-3,3]   n * error")
    for n in [1, 2, 5, 10, 100, 1000, 10000]:
        err = max_charfun_error(n)
        print(f"  {n:>5}   {err:.3e}             {n * err:.4f}")
    print("n * error settles at max t^4 exp(-t^2/2)/12 = 16/(12 e^2) = 0.1804")
    print("(at t = 2): the characteristic functions converge at rate 1/n.")
    print()
    print("Exact binomial CDF versus the normal CDF (sup over x):")
    print("      n   sup error    sqrt(n) * error")
    for n in [10, 100, 1000, 4000]:
        err = binomial_cdf_error(n)
        print(f"  {n:>5}   {err:.5f}      {math.sqrt(n) * err:.4f}")
    print("sqrt(n) * error tends to 1/sqrt(2 pi) = 0.3989: the CDFs converge")
    print("only like 1/sqrt(n), because S_n has jumps of size about")
    print("sqrt(2/(pi n)) at 0 (the Berry-Esseen rate is sharp here).")
    print()
    print("Epistemic status: floating-point evaluation on finite grids and for")
    print("finitely many n. It illustrates the rates; the convergence itself is")
    print("the central limit theorem, proved in the lesson from Levy's")
    print("continuity theorem.")


if __name__ == "__main__":
    main()
