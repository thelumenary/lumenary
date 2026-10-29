"""Patterns that fail: four searches with stated bounds.

1. Euler's sum-of-powers conjecture for fifth powers: an exhaustive search
   over all a <= b <= c <= d < e <= 150 (meet in the middle: sums of two fifth
   powers, looked up with NumPy) finds Lander and Parkin's counterexample.
2. The prime race modulo 4: primes 3 mod 4 lead primes 1 mod 4 for every x
   below 26861, then fall behind (Leech, 1957).
3. pi(x) < li(x) for every real x in [2, 10^6] (and far beyond), although
   Littlewood proved that the inequality reverses infinitely often.
4. The Borwein integrals: an exact rational computation shows when the
   pattern "the integral equals pi/2" breaks, and by how little.
Searches 1-3 are exhaustive up to the stated bounds; li(x) is computed in
floating point with a convergent series.
"""

import math
from fractions import Fraction

import numpy as np

EXPERIMENT = {
    "id": "experimental_mathematics_counterexamples",
    "title": "Counterexample searches with stated bounds",
    "evidence": ["exhaustive-finite", "counterexample", "numerical", "exact"],
    "lessons": ["experimental-mathematics"],
    "summary": (
        "Searches all fifth-power equations a^5+b^5+c^5+d^5 = e^5 with e <= 150 "
        "and finds Lander and Parkin's counterexample to Euler's conjecture; "
        "finds the first x (26861) where primes 1 mod 4 overtake primes 3 mod 4; "
        "compares pi(x) with li(x) up to 10^6; and computes exactly where the "
        "Borwein sinc-integral pattern fails. Exhaustive only up to the bounds."
    ),
    "packages": ["numpy"],
}

EULER_GAMMA = 0.5772156649015329


def euler_fifth_power_search(limit):
    """All (a, b, c, d, e) with a<=b<=c<=d<e<=limit and a^5+b^5+c^5+d^5 = e^5."""
    fifth = np.arange(limit + 1, dtype=np.int64) ** 5
    a, b = np.triu_indices(limit + 1, k=0)
    keep = (a >= 1)
    a, b = a[keep], b[keep]
    sums = fifth[a] + fifth[b]
    order = np.argsort(sums, kind="stable")
    sums, a, b = sums[order], a[order], b[order]
    found = set()
    for e in range(2, limit + 1):
        target = fifth[e] - sums                      # e^5 - (c^5 + d^5)
        ok = (target > 0)
        idx = np.searchsorted(sums, target[ok])
        idx = np.minimum(idx, len(sums) - 1)
        hits = np.nonzero(sums[idx] == target[ok])[0]
        cd = np.nonzero(ok)[0][hits]
        for i, j in zip(idx[hits], cd):
            quad = tuple(sorted((int(a[i]), int(b[i]), int(a[j]), int(b[j]))))
            if quad[3] < e:
                found.add(quad + (e,))
    return sorted(found)


def prime_sieve(limit):
    """Boolean array is_prime[0..limit]."""
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, int(limit ** 0.5) + 1):
        if is_prime[p]:
            is_prime[p * p::p] = False
    return is_prime


def race_mod_4(limit):
    """First x where #primes = 1 mod 4 exceeds #primes = 3 mod 4, and the
    number of integers x <= limit at which it does."""
    is_prime = prime_sieve(limit)
    n = np.arange(limit + 1)
    ones = np.cumsum(is_prime & (n % 4 == 1))
    threes = np.cumsum(is_prime & (n % 4 == 3))
    ahead = np.nonzero(ones > threes)[0]
    return int(ahead[0]), int(len(ahead))


def li(x):
    """Logarithmic integral li(x) = gamma + ln ln x + sum (ln x)^k / (k k!)."""
    t = math.log(x)
    total, term, k = 0.0, 1.0, 1
    while True:
        term *= t / k
        add = term / k
        total += add
        if add < 1e-17 * total:
            break
        k += 1
    return EULER_GAMMA + math.log(t) + total


def li_array(xs):
    """li for a NumPy array of x > 1, by the same series (vectorised)."""
    t = np.log(np.asarray(xs, dtype=float))
    total, term = np.zeros_like(t), np.ones_like(t)
    for k in range(1, 200):
        term = term * t / k
        total += term / k
        if np.all(term / k < 1e-17 * total):
            break
    return EULER_GAMMA + np.log(t) + total


def li_exceeds_pi_up_to(limit):
    """Is li(x) > pi(x) for every real 2 <= x <= limit?  Since li increases and
    pi is constant between primes, it suffices to check x = each prime."""
    is_prime = prime_sieve(limit)
    primes = np.nonzero(is_prime)[0]
    margin = li_array(primes) - np.arange(1, len(primes) + 1)
    return bool(np.all(margin > 0)), float(margin.min())


def borwein_pattern(max_n):
    """For n = 1..max_n: (s_n, exact value of the n-th Borwein integral / pi).

    The n-th integral is that of prod_{k=0}^{n} sinc(x/(2k+1)) over (0, inf).
    It equals pi/2 while s_n = 1/3 + ... + 1/(2n+1) < 1; at the first n with
    s_n > 1 it equals (pi/2)(1 - (s_n - 1)^n / (2^(n-1) n! prod 1/(2k+1)))
    (D. and J. Borwein, 2001).
    """
    rows = []
    for n in range(1, max_n + 1):
        a = [Fraction(1, 2 * k + 1) for k in range(1, n + 1)]
        s = sum(a)
        if s < 1:
            rows.append((s, Fraction(1, 2)))
        else:
            prod = math.prod(a)
            deficit = (s - 1) ** n / (2 ** (n - 1) * math.factorial(n) * prod)
            rows.append((s, Fraction(1, 2) * (1 - deficit)))
            break
    return rows


def main():
    sols = euler_fifth_power_search(150)
    print("1. a^5 + b^5 + c^5 + d^5 = e^5, all 1 <= a<=b<=c<=d < e <= 150:")
    for a, b, c, d, e in sols:
        print(f"   {a}^5 + {b}^5 + {c}^5 + {d}^5 = {e}^5")
    print(f"   {len(sols)} solution(s): Euler's conjecture (1769) is false.")
    first, count = race_mod_4(10 ** 5)
    print("2. Prime race mod 4, x <= 100000: primes 1 mod 4 first lead at")
    print(f"   x = {first}; they lead at only {count} of the 100000 values of x.")
    is_prime = prime_sieve(10 ** 6)
    counts = np.cumsum(is_prime)
    print("3. pi(x) versus li(x):")
    for k in range(2, 7):
        x = 10 ** k
        print(f"   x = 10^{k}: pi(x) = {int(counts[x]):>6}, "
              f"li(x) = {li(x):>10.1f}, li(x) - pi(x) = {li(x) - counts[x]:6.1f}")
    holds, margin = li_exceeds_pi_up_to(10 ** 6)
    print(f"   li(x) > pi(x) for all real 2 <= x <= 10^6: {holds} "
          f"(smallest gap {margin:.3f})")
    print("4. Borwein integrals, exact values divided by pi:")
    for n, (s, value) in enumerate(borwein_pattern(10), start=1):
        tag = "= 1/2" if value == Fraction(1, 2) else \
            f"= 1/2 - {float(Fraction(1, 2) - value):.3e}"
        print(f"   n = {n}: 1/3 + ... + 1/{2 * n + 1} = {float(s):.4f}, "
              f"integral/pi {tag}")
    print()
    print("Epistemic status: searches 1 and 2 are exhaustive and exact up to their")
    print("stated bounds, and 4 is exact rational arithmetic on a proved formula.")
    print("Check 3 uses floating-point li(x) at every prime up to 10^6: numerical")
    print("evidence only - and Littlewood's theorem shows that this evidence,")
    print("however far it is extended, points the wrong way.")


if __name__ == "__main__":
    main()
