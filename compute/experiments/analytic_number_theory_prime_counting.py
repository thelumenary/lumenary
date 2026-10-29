"""Counting primes: pi(x) against x/log x and li(x), and a prime race.

We sieve the primes up to one million and compare the prime-counting
function pi(x) with Gauss's and Legendre's approximations x/log x and the
logarithmic integral li(x) at x = 10, 100, ..., 10^6. The prime number
theorem says pi(x) / (x / log x) -> 1; the table shows how slowly, and that
the *difference* pi(x) - x/log x grows without bound even though the ratio
tends to 1. We also compute Chebyshev's psi(x) = sum of log p over prime
powers p^k <= x, for which psi(x)/x -> 1 is the same theorem, and the race
between primes 1 and 3 mod 4: primes 3 mod 4 lead for a long time (Chebyshev's
bias), the first lead change is at 26861 (Leech, 1957), and the ratio of the
two counts tends to 1 (Dirichlet; de la Vallee Poussin). Exact counts, with
li(x) computed from a convergent series in floating point; numerical
evidence about finitely many x, not a proof of any limit.
"""

import itertools
import math

EXPERIMENT = {
    "id": "analytic_number_theory_prime_counting",
    "title": "Counting primes up to a million",
    "evidence": ["exact", "numerical"],
    "lessons": ["analytic-number-theory"],
    "summary": (
        "Sieves the primes below 10^6 and tabulates pi(x), x/log x and li(x) "
        "at powers of 10, the ratio pi(x)/(x/log x) and the growing "
        "difference, Chebyshev's psi(x)/x, and the race between primes 1 and "
        "3 mod 4 with its first lead change at 26861. Exact counts and "
        "numerical approximations at finitely many points; no limit is proved."
    ),
    "packages": [],
}

EULER_GAMMA = 0.5772156649015329


def sieve(n):
    """Bytearray flags: flags[k] == 1 exactly when k is prime (0 <= k <= n)."""
    flags = bytearray([1]) * (n + 1)
    flags[0:2] = b"\x00\x00"[: min(2, n + 1)]
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p * p::p] = bytes(len(range(p * p, n + 1, p)))
    return flags


def prime_counts(flags, points):
    """pi(x) for each x in the increasing list points."""
    out, count, i = [], 0, 0
    for x in points:
        while i <= x:
            count += flags[i]
            i += 1
        out.append(count)
    return out


def li(x):
    """Logarithmic integral li(x) = gamma + log log x + sum (log x)^n/(n n!)."""
    t = math.log(x)
    total, term, n = 0.0, 1.0, 1
    while True:
        term *= t / n
        add = term / n
        total += add
        if add < 1e-17 * total:
            break
        n += 1
    return EULER_GAMMA + math.log(t) + total


def psi(flags, x):
    """Chebyshev psi(x) = sum of log p over prime powers p^k <= x."""
    total = 0.0
    for p in itertools.compress(range(x + 1), flags[:x + 1]):
        k, q = 0, p
        while q <= x:
            k, q = k + 1, q * p
        total += k * math.log(p)
    return total


def first_lead_change(flags, n):
    """First x <= n with #{p <= x : p = 1 mod 4} > #{p <= x : p = 3 mod 4}."""
    ones = threes = 0
    for x in range(3, n + 1):
        if flags[x]:
            if x % 4 == 1:
                ones += 1
            else:
                threes += 1
            if ones > threes:
                return x
    return None


def main():
    n = 10 ** 6
    flags = sieve(n)
    points = [10 ** k for k in range(1, 7)]
    counts = prime_counts(flags, points)
    print(f"{'x':>8} {'pi(x)':>7} {'x/log x':>10} {'ratio':>7} "
          f"{'pi - x/log x':>12} {'li(x) - pi':>10}")
    for x, c in zip(points, counts):
        approx = x / math.log(x)
        print(f"{x:>8} {c:>7} {approx:>10.1f} {c / approx:>7.4f} "
              f"{c - approx:>12.1f} {li(x) - c:>10.1f}")
    print("psi(x)/x at x = 10^3, 10^4, 10^5, 10^6:",
          " ".join(f"{psi(flags, x) / x:.4f}" for x in points[2:]))
    ones = sum(flags[5::4])
    threes = sum(flags[3::4])
    print(f"Primes below 10^6: {ones} are 1 mod 4, {threes} are 3 mod 4 "
          f"(ratio {ones / threes:.4f})")
    print("First x where primes 1 mod 4 take the lead:",
          first_lead_change(flags, 100000))
    print()
    print("Epistemic status: exact prime counts below 10^6 and floating-point")
    print("values of x/log x and li(x). The trends (ratio -> 1, difference")
    print("unbounded, li(x) closer) are numerical evidence; the limits are the")
    print("prime number theorem and Dirichlet's theorem, proved analytically.")


if __name__ == "__main__":
    main()
