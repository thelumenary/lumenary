"""When factorisation is not unique - and how often numbers are coprime.

1. The Hilbert numbers 1, 5, 9, 13, ... (those of the form 4k + 1) are closed
   under multiplication. Call one irreducible if it is bigger than 1 and not a
   product of two smaller Hilbert numbers bigger than 1. Every Hilbert number
   is a product of irreducibles, but not uniquely: 441 = 9 * 49 = 21 * 21.
   We list all factorisations into irreducibles up to 1500.
2. For contrast, we check that among ordinary integers 2..1500 every number has
   exactly one factorisation into primes (as the fundamental theorem says).
3. Two numbers picked "at random" are coprime with probability 6/pi^2. We
   count exactly the coprime pairs in {1, ..., N}^2 using Euler's totient
   function, for N up to 100 000.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "divisibility_gcd_hilbert",
    "title": "Hilbert numbers and the chance of being coprime",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["divisibility-gcd"],
    "summary": (
        "Finds every Hilbert number (4k + 1) up to 1500 with two different "
        "factorisations into Hilbert irreducibles (441 = 9*49 = 21*21 is the "
        "first), confirms unique prime factorisation for ordinary integers in the "
        "same range, and counts coprime pairs up to N = 100000, whose proportion "
        "approaches 6/pi^2 = 0.6079... Finite and numerical evidence only."
    ),
    "packages": [],
}


def factorizations(n, atoms):
    """All factorisations of n as non-decreasing products of numbers in the
    sorted list ``atoms``, as tuples."""
    if n == 1:
        return [()]
    out = []

    def go(m, start, acc):
        if m == 1:
            out.append(tuple(acc))
            return
        for i in range(start, len(atoms)):
            a = atoms[i]
            if a > m:
                break
            if m % a == 0:
                go(m // a, i, acc + [a])
    go(n, 0, [])
    return out


def hilbert_irreducibles(limit):
    """Hilbert numbers 5 <= n <= limit that are not a product of two smaller
    Hilbert numbers greater than 1."""
    irr = []
    for n in range(5, limit + 1, 4):
        if not any(n % a == 0 and (n // a) % 4 == 1 for a in irr if a * a <= n):
            irr.append(n)
    return irr


def primes_up_to(limit):
    """Sieve of Eratosthenes."""
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(limit ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(range(p * p, limit + 1, p)))
    return [i for i in range(limit + 1) if sieve[i]]


def totients(limit):
    """phi(0..limit) by a sieve."""
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:                     # p is prime
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    return phi


def coprime_pairs(n, phi):
    """Number of ordered pairs (a, b) in {1..n}^2 with gcd(a, b) = 1:
    2 * (phi(1) + ... + phi(n)) - 1."""
    return 2 * sum(phi[1:n + 1]) - 1


def main():
    limit = 1500
    irr = hilbert_irreducibles(limit)
    print("1. Hilbert irreducibles start:", ", ".join(map(str, irr[:12])), "...")
    print("   Hilbert numbers <= 1500 with more than one factorisation:")
    for n in range(1, limit + 1, 4):
        fs = factorizations(n, irr)
        if len(fs) > 1:
            print(f"   {n:5d} = " + " = ".join(" * ".join(map(str, f)) for f in fs))
    primes = primes_up_to(limit)
    counts = [len(factorizations(n, primes)) for n in range(2, limit + 1)]
    print(f"2. Integers 2..{limit}: every one has exactly one prime factorisation:"
          f" {all(c == 1 for c in counts)}")
    phi = totients(100_000)
    print("3. Proportion of coprime pairs in {1..N}^2 (6/pi^2 = "
          f"{6 / math.pi ** 2:.6f}):")
    for n in (10, 100, 1000, 10_000, 100_000):
        print(f"   N = {n:6d}: {coprime_pairs(n, phi) / n ** 2:.6f}")
    print()
    print("Epistemic status: parts 1 and 2 are exhaustive searches up to 1500;")
    print("part 3 is an exact count turned into decimals. They illustrate the")
    print("theorems - unique factorisation in Z, its failure for Hilbert numbers,")
    print("and the limit 6/pi^2, a classical theorem - but a finite range proves")
    print("none of them.")


if __name__ == "__main__":
    main()
