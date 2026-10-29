"""Diffie-Hellman in a small group, and how the cost of a discrete logarithm grows.

Two parties agree on a key over a public channel using powers of a generator
g modulo a prime p. An eavesdropper sees g^a and g^b and must find a or b: a
discrete logarithm. The experiment runs a toy exchange, then measures, for
primes of increasing size, how many group operations two attacks need:
trying every exponent (about p steps) and Shanks's baby-step giant-step
(about sqrt(p) steps). Step counts are exact for these examples; the trend
illustrates, but does not prove, that discrete logarithms are hard - no
efficient classical algorithm is known, and none is proved impossible.
"""

import math
import random

EXPERIMENT = {
    "id": "cryptography_discrete_log",
    "title": "Diffie-Hellman and the cost of discrete logarithms",
    "evidence": ["exact", "experimental"],
    "lessons": ["cryptography"],
    "summary": (
        "Runs a toy Diffie-Hellman exchange modulo a prime, then counts the group "
        "operations needed to recover a secret exponent by exhaustive search "
        "(about p) and by baby-step giant-step (about sqrt(p)) for primes from "
        "about 10^3 to 10^9. Exact counts for these cases; an illustration of "
        "growth, not a proof that the problem is hard."
    ),
    "packages": [],
}


def is_prime(n):
    """Trial division (fine for the sizes used here)."""
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))


def prime_factors(n):
    """The distinct prime factors of n."""
    out, f = [], 2
    while f * f <= n:
        if n % f == 0:
            out.append(f)
            while n % f == 0:
                n //= f
        f += 1
    return out + ([n] if n > 1 else [])


def is_generator(g, p):
    """g generates (Z/pZ)^x iff g^((p-1)/r) != 1 for each prime r | p - 1."""
    return all(pow(g, (p - 1) // r, p) != 1 for r in prime_factors(p - 1))


def smallest_generator(p):
    """The least generator of the multiplicative group modulo the prime p."""
    return next(g for g in range(2, p) if is_generator(g, p))


def brute_force_log(g, h, p):
    """Find x with g^x = h (mod p) by trying x = 0, 1, 2, ...; (x, steps)."""
    value = 1
    for x in range(p - 1):
        if value == h:
            return x, x + 1
        value = value * g % p
    return None, p - 1


def bsgs_log(g, h, p):
    """Shanks's baby-step giant-step; returns (x, group operations used)."""
    m = math.isqrt(p - 1) + 1
    table, value = {}, 1
    for j in range(m):  # baby steps g^j
        table.setdefault(value, j)
        value = value * g % p
    giant = pow(g, -m, p)
    gamma = h
    for i in range(m):  # giant steps h * g^(-im)
        if gamma in table:
            return i * m + table[gamma], m + i + 1
        gamma = gamma * giant % p
    return None, 2 * m


def main():
    rng = random.Random(1976)
    p = 2_147_483_647  # the prime 2^31 - 1
    g = smallest_generator(p)
    a, b = rng.randrange(2, p - 1), rng.randrange(2, p - 1)
    A, B = pow(g, a, p), pow(g, b, p)
    print(f"public: p = {p}, g = {g}")
    print(f"Ama sends A = g^a = {A}; Bolat sends B = g^b = {B}")
    print(f"shared key B^a = {pow(B, a, p)}, A^b = {pow(A, b, p)}")
    print()
    print("Recovering a secret exponent x from g^x mod p:")
    print("         p   brute force (this x)   baby-step giant-step (this x)")
    for target in (1_009, 100_003, 10_000_019, 1_000_000_007):
        q = next(n for n in range(target, 2 * target) if is_prime(n))
        g = smallest_generator(q)
        x = rng.randrange(1, q - 1)
        h = pow(g, x, q)
        brute = brute_force_log(g, h, q)[1] if q < 10**6 else None
        found, steps = bsgs_log(g, h, q)
        assert found == x
        shown = f"{brute:>12}" if brute else "   (skipped)"
        print(f"{q:>10}   {shown}           {steps:>10}  (sqrt p = {math.isqrt(q)})")
    print("Brute force needs up to p - 1 steps, baby-step giant-step about")
    print("2 sqrt(p): for a 2048-bit p, about 2^1025 steps.")
    print()
    print("Epistemic status: exact step counts for these primes and seeds. The")
    print("growth (about p, about sqrt p) matches the analysis of these two")
    print("algorithms only. Faster attacks exist (index calculus), and whether")
    print("discrete logarithms are truly hard is an open problem.")


if __name__ == "__main__":
    main()
