"""How good is Chebyshev's inequality? Exact coin-flip tails against three estimates.

For n fair coin flips with S heads, the weak law of large numbers says that
P(|S/n - 1/2| >= eps) -> 0. We compute this probability exactly (integer
arithmetic on binomial coefficients) and compare it with Chebyshev's bound
1/(4 n eps^2), Hoeffding's bound 2 exp(-2 n eps^2) and the normal
approximation with a continuity correction. Then we check exactly that
Chebyshev's inequality cannot be improved in general: a three-point
distribution attains it.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "probability_theory_chebyshev_vs_exact",
    "title": "Chebyshev, Hoeffding and the normal curve against exact coin tails",
    "evidence": ["exact", "numerical"],
    "lessons": ["probability-theory"],
    "summary": (
        "Computes P(|S/n - 1/2| >= 0.05) exactly for n = 10 to 10,000 fair coin "
        "flips and compares it with Chebyshev's bound, Hoeffding's bound and the "
        "normal approximation. Chebyshev is always valid but very loose for coins; "
        "the true tail decays exponentially. A three-point distribution shows that "
        "Chebyshev's inequality is nevertheless sharp in general."
    ),
    "packages": [],
}


def tail_probability(n, eps):
    """Exact P(|S/n - 1/2| >= eps) for S ~ Binomial(n, 1/2), as a Fraction.

    ``eps`` may be a Fraction, an int or a decimal string such as "0.05".
    """
    if n < 1:
        raise ValueError("n must be positive")
    eps = Fraction(eps)
    total = 0
    coefficient = 1  # C(n, k), updated incrementally
    for k in range(n + 1):
        if abs(Fraction(k, n) - Fraction(1, 2)) >= eps:
            total += coefficient
        coefficient = coefficient * (n - k) // (k + 1)
    return Fraction(total, 2 ** n)


def chebyshev_bound(n, eps):
    """Chebyshev: Var(S/n) / eps^2 = 1 / (4 n eps^2)."""
    return 1 / (4 * n * float(eps) ** 2)


def hoeffding_bound(n, eps):
    """Hoeffding (1963) for variables in [0, 1]: 2 exp(-2 n eps^2)."""
    return 2 * math.exp(-2 * n * float(eps) ** 2)


def normal_approximation(n, eps):
    """2 (1 - Phi(z)) with z = (c - 1/2) / (sqrt(n)/2), c = ceil(n eps).

    For even n the deviation |S - n/2| is a whole number, so the event is
    |S - n/2| >= c, and the continuity correction moves c to c - 1/2.
    """
    c = math.ceil(n * Fraction(eps))
    z = (c - 0.5) / (math.sqrt(n) / 2)
    return math.erfc(z / math.sqrt(2))


def three_point_check(k):
    """X = -k, 0, k with probabilities 1/(2k^2), 1 - 1/k^2, 1/(2k^2).

    Returns (variance, P(|X| >= k), Chebyshev bound 1/k^2), all exact. Here
    the mean is 0 and the standard deviation 1, so the bound is attained.
    """
    k = Fraction(k)
    if k < 1:
        raise ValueError("k must be at least 1")
    p = 1 / (2 * k * k)
    variance = 2 * p * k * k
    return variance, 2 * p, 1 / (k * k)


def main():
    eps = Fraction(1, 20)
    print("Fair coin, eps = 0.05: P(|S/n - 1/2| >= eps), exact and estimated")
    print(f"{'n':>6} {'exact':>11} {'Chebyshev':>11} {'Hoeffding':>11}"
          f" {'normal':>11}")
    for n in [10, 100, 1000, 10000]:
        exact = float(tail_probability(n, eps))
        print(f"{n:>6} {exact:>11.3e} {chebyshev_bound(n, eps):>11.3e}"
              f" {hoeffding_bound(n, eps):>11.3e}"
              f" {normal_approximation(n, eps):>11.3e}")
    print()
    print("Chebyshev only uses the variance. It is valid for every n, but for")
    print("coins the true tail falls exponentially fast (like Hoeffding's")
    print("bound), not like 1/n. Values above 1 are true but useless.")
    print()
    print("Yet Chebyshev cannot be improved without more information:")
    for k in [2, 3, 10]:
        variance, prob, bound = three_point_check(k)
        print(f"  X = -{k}, 0, {k}: Var X = {variance}, P(|X| >= {k}) = {prob},"
              f" bound 1/k^2 = {bound}")
    print()
    print("Epistemic status: the coin tails are exact rational numbers (shown")
    print("rounded); the Hoeffding and normal columns are floating-point values")
    print("of formulas. The table illustrates the theorems for four values of")
    print("n; it does not prove them. The three-point rows are exact and show")
    print("the bound is attained, so no better constant works for all")
    print("distributions with given variance.")


if __name__ == "__main__":
    main()
