"""The asymptotic equipartition property: few sequences carry almost all probability.

For n independent flips of a coin with P(1) = 0.2, a sequence with k ones has
probability 0.2^k 0.8^(n-k), so -(1/n) log2 p(x) depends only on k. The
typical set T = {x : |-(1/n) log2 p(x) - H| <= eps} can therefore be measured
exactly with binomial coefficients. As n grows, P(T) -> 1 while |T| is only
about 2^(nH) of the 2^n sequences: this is why n H bits suffice to describe
the source.
"""

import math

EXPERIMENT = {
    "id": "information_theory_typical_sets",
    "title": "Typical sequences: the asymptotic equipartition property",
    "evidence": ["exact", "numerical"],
    "lessons": ["information-theory"],
    "summary": (
        "For Bernoulli(0.2) sequences of length n up to 2,000, computes exactly (via "
        "binomial coefficients, in logarithms) the probability of the typical set and "
        "the base-2 logarithm of its size, compared with n H and with n. The typical "
        "set's probability approaches 1 while it contains a vanishing fraction of all "
        "sequences."
    ),
    "packages": [],
}


def h2(p):
    """Binary entropy in bits."""
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def log2_comb(n, k):
    """log2 of the binomial coefficient C(n, k), via lgamma."""
    return (math.lgamma(n + 1) - math.lgamma(k + 1)
            - math.lgamma(n - k + 1)) / math.log(2)


def typical_set(n, p, eps):
    """(P(T), log2 |T|) for the eps-typical set of Bernoulli(p) sequences."""
    h = h2(p)
    prob = 0.0
    log_sizes = []
    for k in range(n + 1):
        rate = -(k * math.log2(p) + (n - k) * math.log2(1 - p)) / n
        if abs(rate - h) <= eps:
            lc = log2_comb(n, k)
            log_sizes.append(lc)
            prob += 2 ** (lc - n * rate)
    if not log_sizes:
        return 0.0, float("-inf")
    top = max(log_sizes)
    log_size = top + math.log2(sum(2 ** (s - top) for s in log_sizes))
    return prob, log_size


def main():
    p, eps = 0.2, 0.05
    h = h2(p)
    print(f"Bernoulli({p}) source: H = {h:.4f} bits per symbol, eps = {eps}")
    print(f"{'n':>6} {'P(typical)':>11} {'log2|T|':>9} {'n H':>8} {'n':>6}"
          f" {'fraction of all':>16}")
    for n in [10, 50, 100, 500, 1000, 2000]:
        prob, log_size = typical_set(n, p, eps)
        print(f"{n:>6} {prob:>11.4f} {log_size:>9.1f} {n * h:>8.1f} {n:>6}"
              f"   2^({log_size - n:.1f})")
    print()
    print("The typical set's probability tends to 1 (law of large numbers).")
    print("Its size is always at most 2^(n(H + eps)), and at least about")
    print("2^(n(H - eps)) once P(T) is near 1, yet it is an exponentially small")
    print("fraction of all 2^n sequences: indexing it needs about n H bits.")
    print()
    print("Epistemic status: exact counts computed in floating-point logarithms")
    print("for six values of n. They illustrate the asymptotic equipartition")
    print("property, which is proved from the weak law of large numbers.")


if __name__ == "__main__":
    main()
