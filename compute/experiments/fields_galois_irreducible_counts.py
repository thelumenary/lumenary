"""Counting irreducible polynomials over F_p: brute force against Gauss's formula.

Every element of the field with p^n elements is a root of X^(p^n) - X, and
that polynomial is the product of all monic irreducible polynomials over F_p
whose degree divides n. Comparing degrees gives p^n = sum over d | n of
d * N(d), where N(d) is the number of monic irreducibles of degree d, and
Mobius inversion gives Gauss's formula N(n) = (1/n) sum_{d | n} mu(d) p^(n/d).
The program sieves out reducible polynomials by multiplying all pairs of lower
degree, counts what is left, and compares with the formula. Exact and
exhaustive for the (p, n) shown.
"""

from itertools import product

EXPERIMENT = {
    "id": "fields_galois_irreducible_counts",
    "title": "How many irreducible polynomials? Sieve versus Gauss",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["fields-galois"],
    "summary": (
        "Finds all monic irreducible polynomials of small degree over F_2, F_3 and "
        "F_5 by sieving out products, and compares the counts with Gauss's formula "
        "(1/n) sum mu(d) p^(n/d), which follows from X^(p^n) - X being the product "
        "of the irreducibles of degree dividing n. Exhaustive for the cases shown."
    ),
    "packages": [],
}


def poly_mul(a, b, p):
    """Product of coefficient tuples (lowest degree first) over F_p."""
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return tuple(out)


def monic(p, d):
    """All monic polynomials of degree d over F_p."""
    return [tuple(c) + (1,) for c in product(range(p), repeat=d)]


def irreducibles(p, n):
    """Monic irreducible polynomials of degree n, by sieving out products."""
    reducible = set()
    for d in range(1, n // 2 + 1):
        for f in monic(p, d):
            for g in monic(p, n - d):
                reducible.add(poly_mul(f, g, p))
    return [f for f in monic(p, n) if f not in reducible]


def mobius(n):
    """The Mobius function by trial division."""
    result, m, q = 1, n, 2
    while q * q <= m:
        if m % q == 0:
            m //= q
            if m % q == 0:
                return 0
            result = -result
        q += 1
    return -result if m > 1 else result


def gauss_count(p, n):
    """(1/n) * sum over d | n of mu(d) p^(n/d)."""
    total = sum(mobius(d) * p ** (n // d) for d in range(1, n + 1) if n % d == 0)
    return total // n


def show(f):
    """Monic polynomial as text, highest degree first, e.g. x^3+x+1."""
    terms = []
    for k in range(len(f) - 1, -1, -1):
        c = f[k]
        if c:
            mono = "" if k == 0 else ("x" if k == 1 else f"x^{k}")
            terms.append((str(c) if c != 1 or k == 0 else "") + mono)
    return "+".join(terms)


def main():
    print(" p  n  irreducibles (sieve)  Gauss's formula  sum d*N(d) = p^n")
    ok = True
    for p, top in ((2, 8), (3, 5), (5, 3)):
        counts = {}
        for n in range(1, top + 1):
            counts[n] = len(irreducibles(p, n))
            formula = gauss_count(p, n)
            degree_sum = sum(d * counts[d] for d in counts if n % d == 0)
            ok &= counts[n] == formula and degree_sum == p ** n
            print(f"{p:>2} {n:>2}  {counts[n]:>20}  {formula:>15}  "
                  f"{degree_sum:>6} = {p ** n}")
    print(f"All counts agree: {ok}")
    print("The irreducible cubics over F_2:",
          ", ".join(show(f) for f in irreducibles(2, 3)))
    print("Irreducible quadratics over F_3:",
          ", ".join(show(f) for f in irreducibles(3, 2)))
    print()
    print("Epistemic status: exact, exhaustive counts for these p and n. The")
    print("formula holds for every prime power, as proved in the lesson from")
    print("the factorisation of X^(p^n) - X; the table is a check, not a proof.")


if __name__ == "__main__":
    main()
