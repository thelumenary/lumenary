"""Checking claims in the historical record, and crediting who corrected them.

In 1644 Marin Mersenne asserted that, for exponents p up to 257, the number
2^p - 1 is prime exactly for p = 2, 3, 5, 7, 13, 17, 19, 31, 67, 127, 257. He
gave no proof, and the list was corrected piece by piece over almost three
centuries. Today the Lucas-Lehmer test settles every case in a moment.

We run the test for every prime p <= 257, compare with Mersenne's list, and
re-check three other famous corrections: Cole's factorisation of 2^67 - 1
(1903), Euler's divisor 641 of the Fermat number 2^32 + 1 (1732), and Lander
and Parkin's counterexample to Euler's conjecture on sums of like powers
(1966).

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from math import isqrt
import textwrap

EXPERIMENT = {
    "id": "research_ethics_mersenne_list",
    "title": "Mersenne's list and other corrected claims, rechecked",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["research-ethics"],
    "summary": (
        "Runs the Lucas-Lehmer test for every prime p <= 257 and compares the "
        "Mersenne primes found with Mersenne's 1644 list, then rechecks Cole's "
        "factorisation of 2^67 - 1, Euler's factor 641 of 2^32 + 1 and Lander and "
        "Parkin's counterexample to Euler's sum-of-powers conjecture. Exact integer "
        "arithmetic; Lean rechecks the same facts in the lesson."
    ),
    "packages": [],
}

#: Mersenne's claimed exponents (Cogitata Physico-Mathematica, 1644).
MERSENNE_CLAIM = [2, 3, 5, 7, 13, 17, 19, 31, 67, 127, 257]


def is_prime(n):
    """Trial-division primality test, for small n."""
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def lucas_lehmer(p):
    """Is 2^p - 1 prime? Lucas-Lehmer test for odd prime p; p = 2 directly."""
    if p == 2:
        return True
    m = (1 << p) - 1
    s = 4
    for _ in range(p - 2):
        s = (s * s - 2) % m
    return s == 0


def mersenne_exponents(limit):
    """All primes p <= limit with 2^p - 1 prime."""
    return [p for p in range(2, limit + 1) if is_prime(p) and lucas_lehmer(p)]


def compare(claimed, actual):
    """Exponents claimed but wrong, and exponents missing from the claim."""
    return sorted(set(claimed) - set(actual)), sorted(set(actual) - set(claimed))


def main():
    actual = mersenne_exponents(257)
    wrong, missing = compare(MERSENNE_CLAIM, actual)
    print(f"Primes p <= 257 tested by Lucas-Lehmer: "
          f"{sum(is_prime(p) for p in range(258))}")
    print(f"2^p - 1 is prime for p = {', '.join(map(str, actual))}")
    print(f"Mersenne (1644) claimed p = {', '.join(map(str, MERSENNE_CLAIM))}")
    print(f"   claimed but composite: {wrong}")
    print(f"   prime but omitted:     {missing}")
    print()
    a, b = 193707721, 761838257287
    print(f"Cole (1903): {a} x {b} = 2^67 - 1: {a * b == 2 ** 67 - 1}")
    f5 = 2 ** 32 + 1
    print(f"Euler (1732): 2^32 + 1 = 641 x {f5 // 641}: {f5 % 641 == 0}")
    lhs = 27 ** 5 + 84 ** 5 + 110 ** 5 + 133 ** 5
    print(f"Lander-Parkin (1966): 27^5 + 84^5 + 110^5 + 133^5 = {lhs}")
    print(f"                      144^5                         = {144 ** 5}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact integer arithmetic. The Lucas-Lehmer test is a "
        "theorem (Lucas, 1878; Lehmer, 1930), so its output is a proof of "
        "primality or compositeness provided this short program is correct; the "
        "Lean module proves the same five corrections to Mersenne's list with "
        "Mathlib's formalised test. Computation cannot say who deserves credit: "
        "that is recorded in the lesson's history.",
        width=78,
    ))


if __name__ == "__main__":
    main()
