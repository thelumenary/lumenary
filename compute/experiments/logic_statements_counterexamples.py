"""Hunting for counterexamples to claims about every whole number.

The program tests five 'every' claims on the whole numbers up to 10000. For
each claim it counts the examples that fit and the counterexamples, and
reports the first counterexample. Some claims fail quickly; one fails only
after ten successes in a row; one (Goldbach's conjecture) has no
counterexample here or in far bigger computer searches, yet nobody has
proved it; one (the double of a number is even) is proved in the lesson.
A counterexample disproves a claim; a search without one proves nothing.
"""

import textwrap

EXPERIMENT = {
    "id": "logic_statements_counterexamples",
    "title": "Counterexample hunting up to 10000",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["logic-statements"],
    "summary": (
        "Tests five claims about every whole number on all numbers up to "
        "10000, counting fitting examples and counterexamples. Three claims "
        "are refuted by a counterexample (one only after ten successes); "
        "Goldbach's conjecture and 'double n is even' have none in range. A "
        "counterexample is a disproof; finding none is not a proof."
    ),
    "packages": [],
}

LIMIT = 10000


def primes_up_to(n):
    """is_prime[k] for 0 <= k <= n, by the sieve of Eratosthenes."""
    is_prime = [False, False] + [True] * (n - 1)
    for p in range(2, int(n ** 0.5) + 1):
        if is_prime[p]:
            for multiple in range(p * p, n + 1, p):
                is_prime[multiple] = False
    return is_prime


PRIME = primes_up_to(LIMIT + 200)


def is_prime(n):
    """Is n a prime number? (Uses the sieve, so n must be in its range.)"""
    return PRIME[n]


def sum_of_two_primes(n):
    """Can n be written as p + q with p and q prime?"""
    return any(is_prime(p) and is_prime(n - p) for p in range(2, n // 2 + 1))


# Each claim: (description, which numbers it is about, the property).
CLAIMS = [
    ("every number ending in 2 is divisible by 4",
     lambda n: n % 10 == 2, lambda n: n % 4 == 0),
    ("every odd number bigger than 1 is prime",
     lambda n: n > 1 and n % 2 == 1, is_prime),
    ("n x n + n + 11 is prime for every n (tested up to n = 100)",
     lambda n: n <= 100, lambda n: is_prime(n * n + n + 11)),
    ("every even number from 4 on is a sum of two primes",
     lambda n: n >= 4 and n % 2 == 0, sum_of_two_primes),
    ("the double of every number is even",
     lambda n: True, lambda n: (2 * n) % 2 == 0),
]


def hunt(about, holds, limit=LIMIT):
    """Count fits and counterexamples among n = 0..limit; first failure."""
    fits, counterexamples, first = 0, 0, None
    for n in range(limit + 1):
        if about(n):
            if holds(n):
                fits += 1
            else:
                counterexamples += 1
                if first is None:
                    first = n
    return fits, counterexamples, first


def main():
    print(f"Testing five claims on the whole numbers 0 to {LIMIT}.")
    for text, about, holds in CLAIMS:
        fits, bad, first = hunt(about, holds)
        print()
        print(f"Claim: {text}")
        if first is None:
            print(f"  {fits} examples fit; no counterexample found.")
        else:
            print(f"  {fits} examples fit, {bad} counterexamples;"
                  f" the first is {first}.")
    n = 10
    print()
    print(f"The n x n + n + 11 claim works for n = 0, 1, ..., 9, then fails:"
          f" {n * n + n + 11} = 11 x 11.")
    print()
    print(textwrap.fill(
        "Epistemic status: an exhaustive search of a finite range. Each "
        "counterexample found is a complete disproof of its claim. Finding "
        "no counterexample proves nothing: Goldbach's conjecture has been "
        "checked by computers far beyond this range and is still unproved, "
        "while 'the double of every number is even' is proved in the lesson "
        "by reasoning, not by checking.",
        width=78,
    ))


if __name__ == "__main__":
    main()
