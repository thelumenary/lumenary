"""Fermat, Euler and Wilson checked by machine - and the numbers that fool Fermat.

For every prime p < 200 and every a in 1..p-1 the experiment checks Fermat's
little theorem, for every n < 200 it checks Euler's theorem, and it confirms
Wilson's theorem in both directions: (n-1)! = -1 (mod n) exactly for the
primes n < 400. Then it searches all composite n < 10 000 for Fermat liars:
it finds the pseudoprimes to base 2, and tests each of them against every base
coprime to it, which leaves exactly the Carmichael numbers below 10 000. The
search is exhaustive and exact for the stated ranges, and proves nothing
beyond them.
"""

import math

EXPERIMENT = {
    "id": "congruences_fermat_test",
    "title": "Fermat, Euler, Wilson and the Carmichael numbers",
    "evidence": ["exhaustive-finite", "exact", "counterexample"],
    "lessons": ["congruences"],
    "summary": (
        "Checks Fermat's little theorem for all primes below 200, Euler's theorem "
        "for all n below 200 and Wilson's theorem (both directions) below 400. Then "
        "finds every composite n < 10,000 that passes the Fermat test to base 2, "
        "and keeps those that pass for every coprime base: the seven Carmichael "
        "numbers below 10,000, counterexamples to the converse of Fermat."
    ),
    "packages": [],
}


def is_prime(n):
    """Trial division."""
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))


def phi(n):
    """Euler's totient by counting."""
    return sum(1 for a in range(1, n + 1) if math.gcd(a, n) == 1)


def fermat_holds(p):
    """a^(p-1) = 1 (mod p) for every a in 1..p-1."""
    return all(pow(a, p - 1, p) == 1 for a in range(1, p))


def euler_holds(n):
    """a^phi(n) = 1 (mod n) for every a in 1..n coprime to n."""
    f = phi(n)
    return all(pow(a, f, n) == 1 % n
               for a in range(1, n + 1) if math.gcd(a, n) == 1)


def wilson_residue(n):
    """(n - 1)! mod n, computed with reductions along the way."""
    r = 1 % n
    for k in range(2, n):
        r = r * k % n
    return r


def fermat_liar_bases(n):
    """Bases a coprime to n with a^(n-1) = 1 (mod n)."""
    return [a for a in range(1, n)
            if math.gcd(a, n) == 1 and pow(a, n - 1, n) == 1]


def pseudoprimes_base2(limit):
    """Composite n < limit with 2^(n-1) = 1 (mod n).

    Only odd n are tried: for even n, 2^(n-1) mod n is even, never 1.
    """
    return [n for n in range(3, limit, 2)
            if pow(2, n - 1, n) == 1 and not is_prime(n)]


def carmichael_numbers(limit):
    """Composite n < limit with a^(n-1) = 1 for every a coprime to n.

    Such an n passes base 2 if it is odd, and it cannot be even: a = n - 1
    would give (-1)^(n-1) = -1 = 1 (mod n), forcing n <= 2.
    """
    return [n for n in pseudoprimes_base2(limit)
            if len(fermat_liar_bases(n)) == phi(n)]


def korselt(n):
    """Korselt's criterion: n squarefree, and p-1 | n-1 for each p | n."""
    primes = [p for p in range(2, n) if n % p == 0 and is_prime(p)]
    return (len(primes) > 1 and all(n % (p * p) for p in primes)
            and all((n - 1) % (p - 1) == 0 for p in primes))


def main():
    primes = [p for p in range(2, 200) if is_prime(p)]
    print(f"Fermat holds for all {len(primes)} primes below 200:",
          all(fermat_holds(p) for p in primes))
    print("Euler holds for every n from 1 to 199:",
          all(euler_holds(n) for n in range(1, 200)))
    wilson = [n for n in range(2, 400) if wilson_residue(n) == n - 1]
    print("Wilson: (n-1)! = -1 (mod n) exactly for the primes below 400:",
          wilson == [n for n in range(2, 400) if is_prime(n)])
    print("  (n-1)! mod n for n = 4, 6, 8, 9:",
          [wilson_residue(n) for n in (4, 6, 8, 9)])
    print()
    psp = pseudoprimes_base2(10_000)
    print(f"Composite n < 10000 with 2^(n-1) = 1 (mod n): {len(psp)}")
    print("  first few:", psp[:6])
    print("  bases that expose 341:", [a for a in range(2, 20)
                                       if math.gcd(a, 341) == 1
                                       and pow(a, 340, 341) != 1][:4])
    carm = carmichael_numbers(10_000)
    print("Fool every coprime base (Carmichael numbers):")
    print("  " + ", ".join(map(str, carm)))
    print("  all satisfy Korselt's criterion:", all(korselt(n) for n in carm))
    print()
    print("Epistemic status: exact and exhaustive for the stated ranges. The")
    print("checks agree with the theorems of Fermat, Euler and Wilson, which")
    print("are proved in the lesson; the Carmichael numbers found here are")
    print("genuine counterexamples to the converse of Fermat's theorem.")


if __name__ == "__main__":
    main()
