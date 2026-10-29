"""How fast does the central limit theorem kick in? Exact sums versus the bell curve.

For a fair die and for a lopsided coin (heads with probability 0.1) we compute
the exact distribution of the sum S_n of n independent copies by repeated
convolution, standardise it, and measure the Kolmogorov distance
D_n = sup_x |P((S_n - n mu)/(sigma sqrt n) <= x) - Phi(x)|. The CLT says
D_n -> 0; the Berry-Esseen theorem says D_n <= C rho / (sigma^3 sqrt n) with
C <= 0.4748 (Shevtsova 2011), where rho = E|X - mu|^3. The skewed coin
converges visibly more slowly.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "probability_theory_clt_convergence",
    "title": "The central limit theorem at work: exact sums of dice and coins",
    "evidence": ["numerical"],
    "lessons": ["probability-theory"],
    "summary": (
        "Convolves the distribution of a fair die and of a coin with P(heads) = 0.1 "
        "with itself n times (n up to 256), and measures the largest gap between "
        "the standardised distribution function and the normal one. The gap shrinks "
        "like 1/sqrt(n), within the Berry-Esseen bound, and is larger for the skewed "
        "coin. Floating-point computation of exact distributions; not a proof."
    ),
    "packages": ["numpy"],
}

C_BERRY_ESSEEN = 0.4748


def sum_distribution(pmf, n):
    """Probabilities of S_n = 0, 1, ... for n i.i.d. copies of ``pmf``.

    ``pmf`` lists P(X = 0), P(X = 1), ...; the result is the n-fold
    convolution, computed by repeated squaring.
    """
    if n < 1:
        raise ValueError("n must be positive")
    result = np.array([1.0])
    power = np.asarray(pmf, dtype=float)
    while n:
        if n & 1:
            result = np.convolve(result, power)
        n >>= 1
        if n:
            power = np.convolve(power, power)
    return result


def moments(pmf):
    """Mean, standard deviation and third absolute central moment of pmf."""
    values = np.arange(len(pmf))
    pmf = np.asarray(pmf, dtype=float)
    mu = float(values @ pmf)
    sigma = math.sqrt(float(((values - mu) ** 2) @ pmf))
    rho = float((np.abs(values - mu) ** 3) @ pmf)
    return mu, sigma, rho


def phi(z):
    """Standard normal distribution function."""
    return 0.5 * math.erfc(-z / math.sqrt(2))


def kolmogorov_distance(pmf, n):
    """sup_x |F_n(x) - Phi(x)| for the standardised sum of n copies of pmf.

    F_n is a step function, so the supremum is attained at a jump: compare
    Phi there with the values of F_n just before and just after the jump.
    """
    mu, sigma, _ = moments(pmf)
    probs = sum_distribution(pmf, n)
    cdf = np.cumsum(probs)
    worst = 0.0
    below = 0.0
    for k in range(len(probs)):
        if probs[k] == 0.0:
            continue
        p = phi((k - n * mu) / (sigma * math.sqrt(n)))
        worst = max(worst, abs(p - below), abs(p - cdf[k]))
        below = cdf[k]
    return worst


def berry_esseen_bound(pmf, n):
    """C rho / (sigma^3 sqrt n)."""
    _, sigma, rho = moments(pmf)
    return C_BERRY_ESSEEN * rho / (sigma ** 3 * math.sqrt(n))


def main():
    die = [0] + [1 / 6] * 6
    coin = [0.9, 0.1]
    print("Kolmogorov distance D_n between the standardised sum and N(0, 1)")
    print(f"{'n':>5} | {'die D_n':>9} {'sqrt(n) D_n':>12} {'B-E bound':>10} |"
          f" {'coin D_n':>9} {'sqrt(n) D_n':>12} {'B-E bound':>10}")
    for n in [1, 4, 16, 64, 256]:
        row = [f"{n:>5} |"]
        for pmf in (die, coin):
            d = kolmogorov_distance(pmf, n)
            row.append(f"{d:>9.4f} {math.sqrt(n) * d:>12.3f}"
                       f" {berry_esseen_bound(pmf, n):>10.4f}")
        print(" ".join([row[0], row[1], "|", row[2]]))
    print()
    print("sqrt(n) D_n stays roughly constant: the error falls like 1/sqrt(n),")
    print("as Berry-Esseen predicts, and every D_n is below its bound. The")
    print("skewed coin (rho / sigma^3 = 2.73 versus 1.28 for the die) needs")
    print("many more terms before the bell curve is a good description.")
    print()
    print("Epistemic status: the distributions of S_n are exact up to")
    print("floating-point rounding (about 1e-15), so the distances are reliable")
    print("numerical values. They illustrate the CLT and the Berry-Esseen")
    print("theorem for five values of n and two distributions; they do not")
    print("prove either theorem (the CLT is proved in Mathlib, see the lesson).")


if __name__ == "__main__":
    main()
