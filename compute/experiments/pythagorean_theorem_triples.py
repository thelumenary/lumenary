"""Pythagorean triples up to 100: search, count and Euclid's formula.

The experiment finds every triple of whole numbers a < b < c <= 100 with
a^2 + b^2 = c^2 by trying all pairs, picks out the primitive ones (no common
factor), and compares them with the triples produced by Euclid's formula
(m^2 - n^2, 2mn, m^2 + n^2) for m > n > 0 with no common factor and not both
odd. It also checks that every triple is a multiple of a primitive one and
tests a curious pattern: the product abc is always a multiple of 60. All of
this is exact and exhaustive for c <= 100 only.
"""

import math

EXPERIMENT = {
    "id": "pythagorean_theorem_triples",
    "title": "Pythagorean triples up to 100",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["pythagorean-theorem"],
    "summary": (
        "Finds all 52 Pythagorean triples with hypotenuse at most 100 by brute "
        "force, of which 16 are primitive, and checks that Euclid's formula with "
        "m > n coprime and not both odd produces exactly those 16. Every triple "
        "is a multiple of a primitive one, and abc is a multiple of 60 in every "
        "case found. Exhaustive for c <= 100; the general facts need proofs."
    ),
    "packages": [],
}


def triples(limit):
    """All (a, b, c) with a < b < c <= limit and a^2 + b^2 = c^2."""
    found = []
    for c in range(1, limit + 1):
        for b in range(1, c):
            a_sq = c * c - b * b
            a = math.isqrt(a_sq)
            if a < b and a > 0 and a * a == a_sq:
                found.append((a, b, c))
    return sorted(found, key=lambda t: (t[2], t[0]))


def is_primitive(t):
    """No whole number greater than 1 divides all three sides."""
    return math.gcd(math.gcd(t[0], t[1]), t[2]) == 1


def euclid(m, n):
    """Euclid's triple for m > n > 0, with the two legs in increasing order."""
    a, b, c = m * m - n * n, 2 * m * n, m * m + n * n
    return (min(a, b), max(a, b), c)


def euclid_primitives(limit):
    """Triples from Euclid's formula with m > n > 0 coprime, not both odd."""
    out = set()
    m = 2
    while m * m + 1 <= limit:
        for n in range(1, m):
            if math.gcd(m, n) == 1 and (m - n) % 2 == 1:
                t = euclid(m, n)
                if t[2] <= limit:
                    out.add(t)
        m += 1
    return sorted(out, key=lambda t: (t[2], t[0]))


def primitive_root(t):
    """Divide a triple by the common factor of its sides."""
    g = math.gcd(math.gcd(t[0], t[1]), t[2])
    return (t[0] // g, t[1] // g, t[2] // g)


def hypotenuse_counts(found):
    """How many of the triples in ``found`` have each hypotenuse c."""
    counts = {}
    for _, _, c in found:
        counts[c] = counts.get(c, 0) + 1
    return counts


def main():
    all_t = triples(100)
    prim = [t for t in all_t if is_primitive(t)]
    print(f"Triples with c <= 100: {len(all_t)}; primitive: {len(prim)}")
    print("Primitive triples:")
    for i in range(0, len(prim), 4):
        print("  " + "  ".join(f"{t}" for t in prim[i:i + 4]))
    eu = euclid_primitives(100)
    print(f"Euclid's formula (m > n coprime, not both odd): {len(eu)} triples;"
          f" same list: {eu == prim}")
    roots_ok = all(primitive_root(t) in prim for t in all_t)
    print(f"Every triple is k times a primitive triple: {roots_ok}")
    print(f"abc is a multiple of 60 for every triple found: "
          f"{all(a * b * c % 60 == 0 for a, b, c in all_t)}")
    counts = hypotenuse_counts(all_t)
    best = max(counts.values())
    tops = [c for c, k in sorted(counts.items()) if k == best]
    print(f"Hypotenuses in the most triples ({best} each): {tops}")
    print()
    print("Epistemic status: exact, exhaustive search for c <= 100. It is evidence")
    print("for, not proof of, the facts that Euclid's formula gives every primitive")
    print("triple and that 60 always divides abc; both are theorems of number")
    print("theory, proved with divisibility arguments.")


if __name__ == "__main__":
    main()
