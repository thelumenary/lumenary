"""Two conjectures with impressive numerical support: one false, one open.

The Mertens conjecture says |M(n)| < sqrt(n) for all n > 1, where
M(n) = mu(1) + ... + mu(n) sums the Moebius function. Goldbach's conjecture
says every even n > 2 is a sum of two primes. For both, the experiment
computes the evidence a paper might quote: the largest |M(n)|/sqrt(n) for
n <= 10^6 (it stays far below 1), and the smallest number of Goldbach
representations in each decade up to 2 * 10^5 (it grows). Odlyzko and te
Riele proved in 1985 that the Mertens conjecture is false; Goldbach's
conjecture is open. The computations are exact and exhaustive up to the
stated bounds - and they cannot tell the two cases apart.
"""

import numpy as np

EXPERIMENT = {
    "id": "reading_literature_evidence",
    "title": "Mertens and Goldbach: the same kind of evidence, different fates",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["reading-literature"],
    "summary": (
        "Computes the Mertens function up to 10^6 with a Moebius sieve (max "
        "|M(n)|/sqrt(n) stays well below 1) and the number of Goldbach "
        "representations of every even n up to 2 x 10^5 by exact convolution "
        "(the minimum per decade grows). Both conjectures look equally well "
        "supported; Mertens's is false (Odlyzko and te Riele, 1985) and "
        "Goldbach's is open. Exhaustive up to the stated bounds only."
    ),
    "packages": ["numpy"],
}


def mobius_sieve(limit):
    """mu(n) for 0 <= n <= limit (mu(0) set to 0), by a sieve over primes."""
    mu = np.ones(limit + 1, dtype=np.int64)
    mu[0] = 0
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, limit + 1):
        if is_prime[p]:
            is_prime[2 * p::p] = False
            mu[p::p] *= -1
            mu[p * p::p * p] = 0
    return mu


def mertens(limit):
    """M(n) for 0 <= n <= limit."""
    return np.cumsum(mobius_sieve(limit))


def worst_mertens_ratio(m, lo, hi):
    """(n, |M(n)|/sqrt(n)) maximising the ratio over lo <= n <= hi."""
    n = np.arange(lo, hi + 1)
    ratio = np.abs(m[lo:hi + 1]) / np.sqrt(n)
    k = int(np.argmax(ratio))
    return lo + k, float(ratio[k])


def goldbach_counts(limit):
    """r[n] = #{(p, q) primes, p <= q, p + q = n} for 0 <= n <= limit."""
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, int(limit ** 0.5) + 1):
        if is_prime[p]:
            is_prime[p * p::p] = False
    f = is_prime.astype(float)
    size = 1 << (2 * limit + 1).bit_length()
    ordered = np.rint(np.fft.irfft(np.fft.rfft(f, size) ** 2, size))
    ordered = ordered[: limit + 1].astype(np.int64)    # ordered pairs
    squares = np.zeros(limit + 1, dtype=np.int64)       # pairs with p = q
    evens = 2 * np.nonzero(is_prime[: limit // 2 + 1])[0]
    squares[evens] = 1
    return (ordered + squares) // 2


def decade_minima(r, limit):
    """Smallest r(n) over even n in [lo, hi) for decades up to limit."""
    rows, lo = [], 4
    while lo <= limit:
        hi = min(10 if lo == 4 else lo * 10, limit + 1)
        evens = np.arange(lo + lo % 2, hi, 2)
        rows.append((lo, hi - 1, int(r[evens].min())))
        lo = hi
    return rows


def main():
    limit = 10 ** 6
    m = mertens(limit)
    print(f"Mertens function M(n), n <= {limit}:")
    for k in range(1, 7):
        print(f"  M(10^{k}) = {int(m[10 ** k]):>4}")
    for lo in (2, 10 ** 4):
        n_star, worst = worst_mertens_ratio(m, lo, limit)
        print(f"  largest |M(n)|/sqrt(n) for {lo} <= n <= 10^6: {worst:.4f} "
              f"(at n = {n_star})")
    print()
    glimit = 2 * 10 ** 5
    r = goldbach_counts(glimit)
    print(f"Goldbach representations r(n), even 4 <= n <= {glimit}:")
    for lo, hi, least in decade_minima(r, glimit):
        print(f"  min r(n) for even n in [{lo}, {hi}]: {least}")
    print(f"  r(n) = 0 for some even n in range: {bool((r[4::2] == 0).any())}")
    print()
    print("Same shape of evidence: a quantity that stays safely inside its")
    print("bound, or grows. Yet |M(n)| > sqrt(n) for some n (Odlyzko and")
    print("te Riele, 1985), no explicit such n is known, and Goldbach's")
    print("conjecture, verified to 4 * 10^18, is still unproved.")
    print()
    print("Epistemic status: exact integer computations, exhaustive for the")
    print("stated ranges (the FFT counts are rounded from floating point and")
    print("cross-checked in the tests). They are evidence about those ranges")
    print("only; they cannot distinguish a true conjecture from a false one.")


if __name__ == "__main__":
    main()
