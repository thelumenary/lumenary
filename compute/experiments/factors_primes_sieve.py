"""The sieve of Eratosthenes, factor trees, and Euclid's new primes.

The sieve finds the primes up to n by crossing out multiples. We check that
crossing out multiples of the primes up to the square root of n is enough,
count how the primes thin out, split numbers into primes along two different
factor trees (the same primes appear every time we look), and factor Euclid's
numbers 2 x 3 x ... x p + 1 to see that their prime factors are always new.
"""

import math

EXPERIMENT = {
    "id": "factors_primes_sieve",
    "title": "Sieving primes and growing factor trees",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["factors-primes"],
    "summary": (
        "Runs the sieve of Eratosthenes to 100 and 10,000, checks that stopping at the "
        "square root gives the same primes, factors every n from 2 to 5,000 along two "
        "different factor trees and finds the same primes each time (evidence for "
        "unique factorisation, not a proof), and factors Euclid's numbers to show their "
        "prime factors are new."
    ),
    "packages": [],
}


def sieve(n, stop_at=None):
    """Primes up to n by the sieve of Eratosthenes.

    Multiples are crossed out only for primes p <= stop_at (default: all p).
    """
    if n < 2:
        return []
    alive = [False, False] + [True] * (n - 1)
    for p in range(2, n + 1):
        if stop_at is not None and p > stop_at:
            break
        if alive[p]:
            for multiple in range(2 * p, n + 1, p):
                alive[multiple] = False
    return [k for k in range(n + 1) if alive[k]]


def smallest_factor(n):
    """The smallest factor of n that is bigger than 1 (n >= 2)."""
    if n < 2:
        raise ValueError("n must be at least 2")
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            return d
    return n


def tree_small_first(n):
    """Factor tree that always splits off the smallest factor; sorted leaves."""
    leaves = []
    while n > 1:
        p = smallest_factor(n)
        leaves.append(p)
        n //= p
    return leaves


def tree_middle_split(n):
    """A different factor tree: split n = a x b with a as close to sqrt(n)."""
    for a in range(math.isqrt(n), 1, -1):
        if n % a == 0:
            return sorted(tree_middle_split(a) + tree_middle_split(n // a))
    return [n] if n > 1 else []


def euclid_numbers(count):
    """(primes used, 2 x 3 x ... x p + 1, its prime factors) for the first primes."""
    primes = sieve(100)[:count]
    rows = []
    for k in range(1, count + 1):
        number = math.prod(primes[:k]) + 1
        rows.append((primes[:k], number, tree_small_first(number)))
    return rows


def main():
    small = sieve(100)
    print(f"Sieve of Eratosthenes up to 100: {len(small)} primes")
    print("  " + " ".join(map(str, small)))
    print("Crossing out multiples of 2, 3, 5 and 7 only (primes up to 10):")
    print(f"  same list? {sieve(100, stop_at=10) == small}")
    big = sieve(10_000)
    for limit in (100, 1_000, 10_000):
        count = sum(p <= limit for p in big)
        print(f"  primes up to {limit:>6,}: {count:>5,}  ({count / limit:.1%} of"
              " the numbers)")
    same = all(tree_small_first(n) == tree_middle_split(n)
               for n in range(2, 5_001))
    print()
    print("Two different factor trees for 360:")
    print(f"  smallest factor first: {' x '.join(map(str, tree_small_first(360)))}")
    print("  split 360 = 18 x 20 first: "
          f"{' x '.join(map(str, tree_middle_split(360)))}")
    print(f"  both trees give the same primes for every n from 2 to 5,000: {same}")
    print()
    print("Euclid's numbers: multiply the first primes and add 1")
    for used, number, primes in euclid_numbers(7):
        product = " x ".join(map(str, used))
        found = "prime" if len(primes) == 1 else " x ".join(map(str, primes))
        new = "new" if all(p not in used for p in primes) else "old!"
        print(f"  {product} + 1 = {number}: {found} ({new})")
    print()
    print("Epistemic status: the sieve and the factorisations are exact. Matching")
    print("factor trees for n up to 5,000 is evidence for unique factorisation,")
    print("not a proof (that comes in a later lesson). Euclid's argument proves")
    print("that the primes never run out; the table only illustrates it.")


if __name__ == "__main__":
    main()
