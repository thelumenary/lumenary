"""Primitive roots: which moduli have them, and how often 2 is one.

A primitive root modulo n is a generator of the unit group (Z/nZ)^x. The
program finds, for every n up to 60, whether a primitive root exists, and
compares with the theorem: exactly when n is 1, 2, 4, p^k or 2p^k for an odd
prime p. It lists the least primitive root of the first primes, then counts the
primes below 50000 for which 2 is a primitive root and compares the proportion
with Artin's constant 0.3739558..., which Artin conjectured in 1927 to be the
limiting density (proved by Hooley in 1967 assuming the generalised Riemann
hypothesis; still open unconditionally).
"""

from math import gcd

EXPERIMENT = {
    "id": "elementary_number_theory_primitive_roots",
    "title": "Primitive roots and Artin's conjecture",
    "evidence": ["exact", "exhaustive-finite", "statistical"],
    "lessons": ["elementary-number-theory"],
    "summary": (
        "Decides for every n up to 60 whether (Z/nZ)^x is cyclic and checks the "
        "classification n = 1, 2, 4, p^k, 2p^k; finds least primitive roots; and "
        "measures how often 2 is a primitive root modulo primes below 50000, "
        "compared with Artin's constant 0.3739558 (a conjectured density, proved "
        "only under the generalised Riemann hypothesis). Statistical for Artin."
    ),
    "packages": [],
}

ARTIN_CONSTANT = 0.3739558136


def prime_factors(n):
    """The distinct prime factors of n, by trial division."""
    factors, q = [], 2
    while q * q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    return factors


def totient(n):
    """Euler's phi function from the prime factorisation."""
    result = n
    for q in prime_factors(n):
        result -= result // q
    return result


def multiplicative_order(a, n):
    """Least k >= 1 with a^k = 1 mod n (requires gcd(a, n) = 1)."""
    phi = totient(n)
    order = phi
    for q in prime_factors(phi):
        while order % q == 0 and pow(a, order // q, n) == 1:
            order //= q
    return order


def primitive_root(n):
    """The least primitive root modulo n, or None if there is none."""
    if n == 1:
        return 0
    phi = totient(n)
    for a in range(1, n):
        if gcd(a, n) == 1 and multiplicative_order(a, n) == phi:
            return a
    return None


def predicted(n):
    """The classification: n = 1, 2, 4, p^k or 2 p^k with p an odd prime."""
    if n in (1, 2, 4):
        return True
    m = n // 2 if n % 2 == 0 else n
    if m % 2 == 0:
        return False
    return len(prime_factors(m)) == 1


def primes_below(n):
    """Sieve of Eratosthenes."""
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n) if sieve[i]]


def two_is_primitive_share(bound):
    """(number of odd primes p < bound with 2 a primitive root, number of odd primes)."""
    ps = primes_below(bound)[1:]
    hits = sum(multiplicative_order(2, p) == p - 1 for p in ps)
    return hits, len(ps)


def main():
    have = [n for n in range(1, 61) if primitive_root(n) is not None]
    print("n <= 60 with a primitive root:")
    print("  " + " ".join(map(str, have[:24])))
    print("  " + " ".join(map(str, have[24:])))
    agree = all((primitive_root(n) is not None) == predicted(n) for n in range(1, 61))
    print(f"matches 1, 2, 4, p^k, 2p^k for every n <= 60: {agree}")
    print("no primitive root: 8, 12, 15, ... e.g. orders mod 8:",
          [multiplicative_order(a, 8) for a in (1, 3, 5, 7)])
    first = primes_below(60)
    print("least primitive root of p:")
    print("  " + "  ".join(f"{p}:{primitive_root(p)}" for p in first[:9]))
    print("  " + "  ".join(f"{p}:{primitive_root(p)}" for p in first[9:]))
    for bound in (1000, 10000, 50000):
        hits, total = two_is_primitive_share(bound)
        print(f"2 is a primitive root for {hits:>4} of {total:>4} odd primes "
              f"below {bound:>5}: {hits / total:.4f}")
    print(f"Artin's constant (conjectured density):           {ARTIN_CONSTANT:.4f}")
    print()
    print("Epistemic status: the table for n <= 60 is exact and exhaustive, and")
    print("agrees with the classification proved in the lesson. The proportions")
    print("for 2 are statistical evidence for Artin's conjecture, which remains")
    print("unproved without the generalised Riemann hypothesis.")


if __name__ == "__main__":
    main()
