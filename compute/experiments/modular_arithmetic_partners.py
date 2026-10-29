"""Clock arithmetic by machine: reduce-first rules, partners and zero products.

For every modulus n from 2 to 30 the experiment builds the multiplication
table modulo n and finds which remainders a have a partner b with
a * b mod n = 1. It compares that list with the remainders that share no
factor greater than 1 with n, and it searches for "zero products" a * b = 0
with neither factor 0. It also checks the reduce-first rules for sums and
products on a finite range. Everything is exact integer arithmetic over finite
ranges: exhaustive evidence for those n, not a proof for every n.
"""

import math

EXPERIMENT = {
    "id": "modular_arithmetic_partners",
    "title": "Partners and zero products on every clock up to 30",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["modular-arithmetic"],
    "summary": (
        "Checks the reduce-first rules for sums and products for all a, b below "
        "120 and n up to 30, then builds every multiplication table modulo n for "
        "n = 2 to 30: the remainders with a multiplicative partner are exactly "
        "those sharing no factor with n, and zero products appear exactly when n "
        "is not prime. Exhaustive for these n only; the lesson proves the rules."
    ),
    "packages": [],
}


def partners(n):
    """Remainders a in 0..n-1 that have some b with a * b mod n == 1."""
    if n < 1:
        raise ValueError("n must be positive")
    return [a for a in range(n) if any(a * b % n == 1 for b in range(n))]


def partner_of(a, n):
    """The b in 0..n-1 with a * b mod n == 1, or None if there is none."""
    for b in range(n):
        if a * b % n == 1:
            return b
    return None


def coprime_remainders(n):
    """Remainders a in 0..n-1 with gcd(a, n) == 1 (no common factor > 1)."""
    return [a for a in range(n) if math.gcd(a, n) == 1 and n > 1]


def zero_products(n):
    """Pairs (a, b) of non-zero remainders with a * b mod n == 0."""
    return [(a, b) for a in range(1, n) for b in range(1, n) if a * b % n == 0]


def reduce_first_failures(n_max, a_max):
    """Count cases and failures of the sum and product rules (n = 1..n_max)."""
    cases = failures = 0
    for n in range(1, n_max + 1):
        for a in range(a_max):
            for b in range(a_max):
                cases += 1
                if (a + b) % n != (a % n + b % n) % n:
                    failures += 1
                if (a * b) % n != (a % n) * (b % n) % n:
                    failures += 1
    return cases, failures


def is_prime(n):
    """Trial division (n >= 2)."""
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def main():
    cases, bad = reduce_first_failures(30, 120)
    print(f"Reduce-first rules, a, b < 120, n <= 30: {cases} cases, {bad} failures")
    print()
    print("Who has a partner?")
    for n in (10, 11, 12):
        pairs = ", ".join(f"{a}*{partner_of(a, n)}" for a in partners(n))
        print(f"  mod {n:<2}: {pairs}")
    same = all(partners(n) == coprime_remainders(n) for n in range(2, 31))
    print(f"  partners = remainders coprime to n, for n = 2..30: {same}")
    full = [n for n in range(2, 31) if len(partners(n)) == n - 1]
    print("  n for which every non-zero remainder has a partner:")
    print(f"    {full}")
    primes = [n for n in range(2, 31) if is_prime(n)]
    print(f"  these n are exactly the primes up to 30: {full == primes}")
    print()
    print("Zero products (a * b = 0 with a, b non-zero):")
    for n in (7, 10, 12):
        zs = zero_products(n)
        shown = ", ".join(f"{a}*{b}" for a, b in zs if a <= b)
        print(f"  mod {n:<2}: {shown or 'none'}")
    no_zero = [n for n in range(2, 31) if not zero_products(n)]
    print(f"  n <= 30 with no zero products: {no_zero}")
    print()
    print("Epistemic status: exhaustive, exact evidence for the moduli and ranges")
    print("shown, nothing more. The reduce-first rules and 'a common factor blocks")
    print("a partner' are proved in the lesson for every n; 'coprime implies a")
    print("partner' is proved later with Euclid's algorithm.")


if __name__ == "__main__":
    main()
