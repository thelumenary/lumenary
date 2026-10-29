"""Testing universal properties by brute force, in finite sets and finite posets.

Part 1 counts, for every pair of maps f : X -> A and g : X -> B between small
finite sets, the maps h : X -> P with p1 o h = f and p2 o h = g, for three
candidate products P. Only the cartesian product gives exactly one h every
time: a bigger set breaks uniqueness, a smaller one breaks existence.
Part 2 searches finite posets (ordered by divisibility) for greatest lower
bounds and least upper bounds - the products and coproducts of the poset
regarded as a category - and finds pairs that have none.
"""

from itertools import product
from math import gcd

EXPERIMENT = {
    "id": "products_coproducts_finite",
    "title": "Universal properties by brute force: finite sets and divisibility posets",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["products-coproducts"],
    "summary": (
        "For small finite sets, counts the maps h with p1 o h = f and p2 o h = g for "
        "every pair (f, g) and three candidate products: only A x B gives exactly one. "
        "Then checks that products and coproducts in the divisors of 60 under "
        "divisibility are gcd and lcm, and finds pairs in {2, 3, 12, 18} with neither. "
        "Exhaustive for these finite examples only."
    ),
    "packages": [],
}


def maps(dom, cod):
    """All functions dom -> cod, as dicts."""
    return [dict(zip(dom, values)) for values in product(cod, repeat=len(dom))]


def factorisations(X, P, p1, p2, f, g):
    """Number of h : X -> P with p1(h(x)) = f(x) and p2(h(x)) = g(x) for all x."""
    return sum(1 for h in maps(X, P)
               if all(p1[h[x]] == f[x] and p2[h[x]] == g[x] for x in X))


def candidates(A, B):
    """Three would-be products of A and B: (name, P, p1, p2)."""
    pairs = list(product(A, B))
    triples = list(product(A, B, (0, 1)))
    return [
        ("A x B", pairs, {p: p[0] for p in pairs}, {p: p[1] for p in pairs}),
        ("A x B x {0,1}", triples, {t: t[0] for t in triples},
         {t: t[1] for t in triples}),
        ("A, p2 constant", list(A), {a: a for a in A}, {a: B[0] for a in A}),
    ]


def count_profile(A, B, X, cand):
    """The set of factorisation counts over all pairs (f, g) for one candidate."""
    _, P, p1, p2 = cand
    return {factorisations(X, P, p1, p2, f, g)
            for f in maps(X, A) for g in maps(X, B)}


def divides(a, b):
    """The divisibility order: a <= b iff a divides b."""
    return b % a == 0


def glb(elements, leq, a, b):
    """Greatest lower bound of a and b in a finite poset, or None."""
    lower = [x for x in elements if leq(x, a) and leq(x, b)]
    best = [x for x in lower if all(leq(y, x) for y in lower)]
    return best[0] if best else None


def lub(elements, leq, a, b):
    """Least upper bound (the dual notion), or None."""
    return glb(elements, lambda x, y: leq(y, x), a, b)


def main():
    A, B = (0, 1), ("a", "b", "c")
    print("Part 1: number of h : X -> P with p1 o h = f, p2 o h = g")
    print("        (all pairs f : X -> A, g : X -> B; |A| = 2, |B| = 3)")
    for cand in candidates(A, B):
        row = []
        for n in range(3):
            row.append(sorted(count_profile(A, B, tuple(range(n)), cand)))
        print(f"  P = {cand[0]:<15} |X| = 0, 1, 2: {row}")
    print("  Exactly one h every time only for A x B.")
    divs = [d for d in range(1, 61) if 60 % d == 0]
    ok = all(glb(divs, divides, a, b) == gcd(a, b)
             and lub(divs, divides, a, b) == a * b // gcd(a, b)
             for a in divs for b in divs)
    print()
    print(f"Part 2: divisors of 60 ({len(divs)} elements) under divisibility:")
    print(f"  product = gcd and coproduct = lcm for all {len(divs) ** 2} pairs: "
          f"{ok}")
    small = [2, 3, 12, 18]
    for a, b in [(2, 3), (12, 18), (2, 12)]:
        print(f"  in {small}: product of {a}, {b} = "
              f"{glb(small, divides, a, b)}, coproduct = "
              f"{lub(small, divides, a, b)}")
    print("  2, 3: no lower bound, two minimal upper bounds 12, 18; 12, 18 dually.")
    print()
    print("Epistemic status: exhaustive checks of finitely many maps and pairs.")
    print("They illustrate the definitions; that A x B is a product of any two")
    print("sets, and that products in a poset are meets, are proved in the lesson.")


if __name__ == "__main__":
    main()
