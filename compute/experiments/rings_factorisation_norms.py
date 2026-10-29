"""Factorisation by norms in Z[i] and Z[sqrt(-5)].

An element x + y*sqrt(d) (d = -1 or -5) has norm N = x^2 - d*y^2, and the norm is
multiplicative, so a factor of z has a norm dividing N(z). That makes an exact
search possible: list the elements of each smaller norm and test divisibility.
The program finds every factorisation of 2, ..., 30 into irreducibles (up to
order and units) in both rings, shows that Euclidean division by 2 fails in
Z[sqrt(-5)] (every remainder has norm at least 6 > N(2) = 4), and checks that
rounding the exact quotient always works in Z[i] on a box of examples.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import product

EXPERIMENT = {
    "id": "rings_factorisation_norms",
    "title": "Unique factorisation in Z[i], and its failure in Z[sqrt(-5)]",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["rings"],
    "summary": (
        "Uses the multiplicative norm x^2 - d y^2 to search exactly for "
        "irreducible factors in Z[i] and Z[sqrt(-5)], lists every factorisation of "
        "the integers 2 to 30 into irreducibles, and tests Euclidean division. In "
        "Z[i] factorisation is always unique; in Z[sqrt(-5)] it is not (6 = 2 * 3 = "
        "(1 + sqrt(-5))(1 - sqrt(-5))). Exact for the elements shown."
    ),
    "packages": [],
}


def norm(z, d):
    """N(x + y sqrt(d)) = x^2 - d y^2 (positive for d < 0, z != 0)."""
    x, y = z
    return x * x - d * y * y


def mul(z, w, d):
    """(a + b r)(c + e r) with r^2 = d."""
    return (z[0] * w[0] + d * z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def divide(z, w, d):
    """Return z / w if it lies in Z[sqrt(d)], else None (uses z * conj(w))."""
    n = norm(w, d)
    x, y = mul(z, (w[0], -w[1]), d)
    if x % n or y % n:
        return None
    return (x // n, y // n)


def of_norm(n, d):
    """All elements of norm n (finitely many, since d < 0)."""
    bound = int(n ** 0.5) + 1
    return [(x, y) for x in range(-bound, bound + 1)
            for y in range(-bound, bound + 1) if norm((x, y), d) == n]


def units(d):
    """The units: the elements of norm 1."""
    return of_norm(1, d)


def canonical(z, d):
    """A fixed representative of z up to multiplication by units."""
    return max(mul(z, u, d) for u in units(d))


def proper_divisors(z, d):
    """Divisors a of z with 1 < N(a) < N(z), one per associate class."""
    n = norm(z, d)
    found = set()
    for m in range(2, n):
        if n % m == 0:
            for a in of_norm(m, d):
                if divide(z, a, d) is not None:
                    found.add(canonical(a, d))
    return sorted(found)


def is_irreducible(z, d):
    """Not zero, not a unit, and no factor of intermediate norm."""
    return norm(z, d) > 1 and not proper_divisors(z, d)


@lru_cache(maxsize=None)
def factorisations(z, d):
    """All factorisations of z into irreducibles, as sorted tuples of
    canonical representatives (so order and units are ignored)."""
    if is_irreducible(z, d):
        return frozenset({(canonical(z, d),)})
    result = set()
    for a in proper_divisors(z, d):
        if is_irreducible(a, d):
            for rest in factorisations(divide(z, a, d), d):
                result.add(tuple(sorted(rest + (a,))))
    return frozenset(result)


def show(z, d):
    """Format x + y*sqrt(d) compactly, e.g. 1+r or 2 or -r."""
    x, y = z
    if y == 0:
        return str(x)
    r = "i" if d == -1 else "r"
    coef = "" if abs(y) == 1 else str(abs(y))
    if x == 0:
        return f"{'-' if y < 0 else ''}{coef}{r}"
    return f"{x}{'-' if y < 0 else '+'}{coef}{r}"


def best_remainder(a, b, d, box=6):
    """Least N(a - q b) over q = (s, t) with |s|, |t| <= box."""
    return min(norm((a[0] - p[0], a[1] - p[1]), d)
               for p in (mul(q, b, d) for q in product(range(-box, box + 1),
                                                         repeat=2)))


def gaussian_rounding_works(limit=6):
    """Check N(a - q b) < N(b) with q = a/b rounded, for a, b in a box."""
    rng = range(-limit, limit + 1)
    for a in product(rng, repeat=2):
        for b in product(rng, repeat=2):
            if b == (0, 0):
                continue
            n = norm(b, -1)
            x, y = mul(a, (b[0], -b[1]), -1)
            q = (round(Fraction(x, n)), round(Fraction(y, n)))
            r = (a[0] - mul(q, b, -1)[0], a[1] - mul(q, b, -1)[1])
            if norm(r, -1) >= n:
                return False
    return True


def main():
    for d, name in ((-1, "Z[i]"), (-5, "Z[sqrt(-5)]  (r = sqrt(-5))")):
        print(f"{name}: integers 2..30 with more than one factorisation")
        several = []
        for n in range(2, 31):
            facs = factorisations((n, 0), d)
            if len(facs) > 1:
                several.append(n)
                first, second = sorted(facs, key=len)[:2]
                shown = "  =  ".join(" ".join(f"({show(p, d)})" for p in f)
                                     for f in (first, second))
                print(f"  {n:>2}: {len(facs)} ways, e.g. {shown}")
        if not several:
            print("  none: every factorisation is unique up to order and units")
    print("Irreducible but not prime in Z[sqrt(-5)]: 2 divides (1+r)(1-r) = 6,")
    print(f"  2 irreducible: {is_irreducible((2, 0), -5)}; 2 divides 1+r: "
          f"{divide((1, 1), (2, 0), -5) is not None}")
    print(f"Euclid fails in Z[sqrt(-5)]: least N((1+r) - 2q) = "
          f"{best_remainder((1, 1), (2, 0), -5)} >= N(2) = 4")
    print(f"Z[i]: rounding a/b gives N(remainder) < N(b) for all a, b with")
    print(f"  coordinates in -6..6: {gaussian_rounding_works()}")
    print()
    print("Epistemic status: exact searches, justified by the multiplicative")
    print("norm, for the integers 2..30 only. They illustrate, but do not prove,")
    print("that Z[i] is a UFD (proved via its Euclidean algorithm) and exhibit a")
    print("genuine counterexample to unique factorisation in Z[sqrt(-5)].")


if __name__ == "__main__":
    main()
