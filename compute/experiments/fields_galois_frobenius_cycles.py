"""Seeing a Galois group by factoring modulo primes (Chebotarev statistics).

For a monic integer polynomial f of degree n and a prime p not dividing its
discriminant, f factors modulo p into irreducibles whose degrees form the cycle
type of a Frobenius element of Gal(f), acting on the n roots. Chebotarev's
density theorem says each cycle type occurs for a proportion of primes equal to
the proportion of Galois-group elements with that cycle type. The program
factors x^2 - 2, x^3 - 2, x^4 + 1 and x^5 - 4x + 2 modulo every suitable prime
below 2000 (distinct-degree factorisation) and compares the frequencies with
the predictions for the groups Z/2, S3, Z/2 x Z/2 and S5.
"""

from collections import Counter
from fractions import Fraction

EXPERIMENT = {
    "id": "fields_galois_frobenius_cycles",
    "title": "Galois groups seen through factorisation modulo primes",
    "evidence": ["exact", "statistical"],
    "lessons": ["fields-galois"],
    "summary": (
        "Factors four polynomials modulo all suitable primes below 2000 and tallies "
        "the degree patterns, which are cycle types of Frobenius elements. The "
        "frequencies approach the proportions predicted by the Galois groups Z/2, "
        "S3, (Z/2)^2 and S5 (Chebotarev's density theorem). Each factorisation is "
        "exact; the agreement of frequencies is statistical evidence."
    ),
    "packages": [],
}


def trim(a):
    """Drop leading zero coefficients (lists are lowest degree first)."""
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def pmod(a, m, p):
    """Remainder of a modulo m over F_p (m non-zero)."""
    a, m = trim(a), trim(m)
    inv = pow(m[-1], p - 2, p)
    while len(a) >= len(m):
        c = a[-1] * inv % p
        shift = len(a) - len(m)
        for i, x in enumerate(m):
            a[shift + i] = (a[shift + i] - c * x) % p
        a = trim(a)
    return a


def pmulmod(a, b, m, p):
    """a * b modulo m over F_p."""
    out = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return pmod(out, m, p)


def ppowmod(base, e, m, p):
    """base^e modulo m over F_p, by repeated squaring."""
    result, base = [1], pmod(base, m, p)
    while e:
        if e & 1:
            result = pmulmod(result, base, m, p)
        base = pmulmod(base, base, m, p)
        e >>= 1
    return result


def pgcd(a, b, p):
    """Monic gcd over F_p."""
    a, b = trim(a), trim(b)
    while b:
        a, b = b, pmod(a, b, p)
    if not a:
        return a
    inv = pow(a[-1], p - 2, p)
    return [x * inv % p for x in a]


def derivative(f):
    """Formal derivative of an integer polynomial."""
    return [k * c for k, c in enumerate(f)][1:]


def factor_degrees(f, p):
    """Degrees of the irreducible factors of f mod p (f squarefree mod p),
    by distinct-degree factorisation."""
    g = [c % p for c in f]
    degrees, k, xpk = [], 0, [0, 1]
    while len(trim(g)) - 1 >= 2 * (k + 1):
        k += 1
        xpk = ppowmod(xpk, p, g, p)            # x^(p^k) mod g
        diff = trim([(c - (1 if i == 1 else 0)) % p
                     for i, c in enumerate(xpk + [0] * (2 - len(xpk)))])
        h = pgcd(g, diff, p)
        if len(h) > 1:
            degrees += [k] * ((len(h) - 1) // k)
            g = pdiv(g, h, p)
    if len(trim(g)) > 1:
        degrees.append(len(trim(g)) - 1)
    return tuple(sorted(degrees))


def pdiv(a, b, p):
    """Exact quotient a / b over F_p."""
    a, b = trim(a), trim(b)
    q = [0] * (len(a) - len(b) + 1)
    inv = pow(b[-1], p - 2, p)
    while len(a) >= len(b) and a:
        c = a[-1] * inv % p
        shift = len(a) - len(b)
        q[shift] = c
        for i, x in enumerate(b):
            a[shift + i] = (a[shift + i] - c * x) % p
        a = trim(a)
    return q


def primes_below(n):
    """Sieve of Eratosthenes."""
    sieve = [True] * n
    sieve[0:2] = [False, False]
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = [False] * len(sieve[i * i::i])
    return [i for i, s in enumerate(sieve) if s]


def is_squarefree_mod(f, p):
    """f mod p has no repeated factor (so p does not divide the discriminant)."""
    return len(pgcd([c % p for c in f], [c % p for c in derivative(f)], p)) == 1


#: polynomial (lowest degree first), Galois group, predicted cycle-type shares
EXAMPLES = [
    ("x^2-2", [-2, 0, 1], "Z/2", {(1, 1): Fraction(1, 2), (2,): Fraction(1, 2)}),
    ("x^3-2", [-2, 0, 0, 1], "S3",
     {(1, 1, 1): Fraction(1, 6), (1, 2): Fraction(1, 2), (3,): Fraction(1, 3)}),
    ("x^4+1", [1, 0, 0, 0, 1], "Z/2 x Z/2",
     {(1, 1, 1, 1): Fraction(1, 4), (2, 2): Fraction(3, 4)}),
    ("x^5-4x+2", [2, -4, 0, 0, 0, 1], "S5",
     {(1, 1, 1, 1, 1): Fraction(1, 120), (1, 1, 1, 2): Fraction(10, 120),
      (1, 2, 2): Fraction(15, 120), (1, 1, 3): Fraction(20, 120),
      (2, 3): Fraction(20, 120), (1, 4): Fraction(30, 120),
      (5,): Fraction(24, 120)}),
]


def tally(f, bound):
    """Counter of factorisation patterns over primes below bound."""
    return Counter(factor_degrees(f, p) for p in primes_below(bound)
                   if is_squarefree_mod(f, p))


def main():
    bound = 2000
    for name, f, group, predicted in EXAMPLES:
        counts = tally(f, bound)
        total = sum(counts.values())
        print(f"{name}  (Galois group {group}), {total} primes below {bound}")
        parts = []
        for pattern in sorted(predicted, key=lambda t: (len(t), t), reverse=True):
            seen = counts.get(pattern, 0) / total
            parts.append(f"{'+'.join(map(str, pattern))}: "
                         f"{seen:.3f}/{float(predicted[pattern]):.3f}")
        for i in range(0, len(parts), 3):
            print("   " + "   ".join(parts[i:i + 3]))
        unexpected = set(counts) - set(predicted)
        print(f"   patterns outside the prediction: {sorted(unexpected) or 'none'}")
    print("(each entry: degrees of the factors mod p: observed/predicted share)")
    print()
    print("Epistemic status: every factorisation is exact. The match between")
    print("frequencies and group proportions is statistical evidence for these")
    print("Galois groups; Chebotarev's theorem (1922) guarantees the limits, but")
    print("finitely many primes can never prove what the Galois group is.")


if __name__ == "__main__":
    main()
