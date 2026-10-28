"""Euler's prime-generating polynomial: forty successes, then a failure.

p(n) = n^2 + n + 41 is prime for n = 0, 1, 2, ..., 39 - forty cases in a row.
It is tempting to conclude "always prime". n = 40 breaks the pattern:
p(40) = 1681 = 41 * 41. Evidence, however plentiful, is not proof.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "euler_polynomial",
    "title": "Forty primes in a row, then a counterexample",
    "evidence": ["experimental", "counterexample"],
    "lessons": ["integers"],
    "summary": (
        "Tests n^2 + n + 41 for primality (exact trial division) for n = 0 to 39, "
        "where every value is prime, then finds the first failure at n = 40, "
        "where the value is 41 * 41. Forty confirming cases were evidence, not "
        "proof; one counterexample settles the question."
    ),
    "packages": [],
}


def euler(n):
    """Euler's polynomial n^2 + n + 41."""
    return n * n + n + 41


def is_prime(n):
    """Exact primality test by trial division (fine for the small numbers used here)."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def smallest_factor(n):
    """The smallest prime factor of an integer n >= 2."""
    if n < 2:
        raise ValueError("n must be at least 2")
    if n % 2 == 0:
        return 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return d
        d += 2
    return n


def first_failure(poly, start=0, stop=10_000):
    """Return the first n in start..stop-1 where poly(n) is not prime, or None."""
    for n in range(start, stop):
        if not is_prime(poly(n)):
            return n
    return None


def prime_count(poly, stop):
    """How many of poly(0), ..., poly(stop - 1) are prime."""
    return sum(is_prime(poly(n)) for n in range(stop))


def main():
    print("Euler's polynomial p(n) = n^2 + n + 41. Is p(n) always prime?")
    print()
    values = [euler(n) for n in range(40)]
    for row in range(0, 40, 8):
        cells = " ".join(f"{v:>5}" for v in values[row:row + 8])
        print(f"  n = {row:>2}..{row + 7:<2}: {cells}")
    streak = sum(is_prime(v) for v in values)
    print(f"All {streak} of these 40 values are prime (checked exactly by trial division).")
    print()
    n = first_failure(euler)
    v = euler(n)
    f = smallest_factor(v)
    print(f"First failure: n = {n}, p({n}) = {v} = {f} * {v // f}.")
    print(f"Why n = 40 had to fail: p(40) = 40*40 + 40 + 41 = 40*41 + 41 = 41*41.")
    print(f"And p(41) = 41*41 + 41 + 41 = 41 * 43 = {euler(41)} fails too.")
    print()
    for stop in (100, 1000):
        print(f"Primes among p(0), ..., p({stop - 1}): {prime_count(euler, stop)} of {stop}")
    print("Still remarkably many - but a pattern that is 'usually true' is not a theorem.")
    print()
    print(textwrap.fill(
        "Epistemic status: forty confirming cases were experimental evidence, "
        "and they were not a proof - the single counterexample at n = 40 proves "
        "that n^2+n+41 is not always prime. (No non-constant polynomial with "
        "integer coefficients gives primes for every n; that is a theorem, not "
        "something this program checked.)",
        width=78,
    ))


if __name__ == "__main__":
    main()
