"""The universal property of the product, checked on finite sets.

For finite sets X, A, B, maps X -> A x B correspond exactly to pairs of maps
(X -> A, X -> B). We check this bijection exhaustively for small sizes. Then
we test three candidate "products" P with maps p : P -> A and q : P -> B by
counting, for every pair (f, g) of maps from a test set X, how many maps
u : X -> P satisfy p . u = f and q . u = g. A product needs exactly one every
time. The numbers model k = a*|B| + b passes; a set with a spare coordinate
fails uniqueness; the disjoint union fails existence whatever maps we choose
(it has 5 elements but there are 6 pairs to hit), and with the maps chosen
here it also fails uniqueness. Exhaustive and exact for these small sets.
"""

from itertools import product

EXPERIMENT = {
    "id": "universal_properties_products",
    "title": "Products of finite sets: existence and uniqueness",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["universal-properties"],
    "summary": (
        "Checks exhaustively that maps X -> A x B correspond one-to-one to "
        "pairs of maps for small finite sets, then counts factorisations "
        "through three candidate products: an encoding of pairs as numbers "
        "passes, a set with a spare coordinate fails uniqueness, and the "
        "disjoint union fails existence and uniqueness. Exhaustive only for "
        "the sizes shown."
    ),
    "packages": [],
}


def maps(domain, codomain):
    """All functions domain -> codomain, as dicts."""
    domain, codomain = list(domain), list(codomain)
    return [dict(zip(domain, values))
            for values in product(codomain, repeat=len(domain))]


def pairing(f, g):
    """The map x -> (f(x), g(x)) into the product."""
    return {x: (f[x], g[x]) for x in f}


def factorisations(xs, P, p, q, f, g):
    """Number of u : X -> P with p(u(x)) = f(x) and q(u(x)) = g(x) for all x."""
    count = 1
    for x in xs:
        count *= sum(1 for z in P if p(z) == f[x] and q(z) == g[x])
    return count


def candidates(A, B):
    """Three candidate products: (name, P, p, q)."""
    nb = len(B)
    numbers = list(range(len(A) * nb))
    spare = list(product(A, B, [0, 1]))
    union = [("A", a) for a in A] + [("B", b) for b in B]
    return [
        ("numbers k = a*|B| + b", numbers,
         lambda k: A[k // nb], lambda k: B[k % nb]),
        ("A x B x {0, 1}", spare, lambda z: z[0], lambda z: z[1]),
        ("disjoint union A + B", union,
         lambda z: z[1] if z[0] == "A" else A[0],
         lambda z: z[1] if z[0] == "B" else B[0]),
    ]


def factorisation_counts(X, A, B, P, p, q):
    """The set of factorisation counts over all pairs (f, g)."""
    return {factorisations(X, P, p, q, f, g)
            for f in maps(X, A) for g in maps(X, B)}


def main():
    print("1. Maps X -> A x B versus pairs of maps (X -> A, X -> B)")
    for nx, na, nb in [(1, 2, 3), (2, 2, 2), (2, 3, 2), (3, 2, 2)]:
        X, A, B = range(nx), range(na), range(nb)
        n_pairs = len(maps(X, A)) * len(maps(X, B))
        images = {tuple(sorted(pairing(f, g).items()))
                  for f in maps(X, A) for g in maps(X, B)}
        total = len(maps(X, list(product(A, B))))
        ok = n_pairs == len(images) == total
        print(f"   |X|={nx} |A|={na} |B|={nb}: {n_pairs:>3} pairs, "
              f"{total:>3} maps, pairing is a bijection: {ok}")
    print()
    print("2. Factorisations through candidate products, |A| = 2, |B| = 3")
    A, B = ["a0", "a1"], ["b0", "b1", "b2"]
    for nx in (1, 2):
        X = range(nx)
        print(f"   test set X with {nx} element(s):")
        for name, P, p, q in candidates(A, B):
            counts = sorted(factorisation_counts(X, A, B, P, p, q))
            verdict = "product" if counts == [1] else "not a product"
            print(f"     {name:<22} counts {str(counts):<13} {verdict}")
    print()
    print("Epistemic status: exhaustive and exact for these small sets. Part 1")
    print("illustrates |A x B|^|X| = |A|^|X| |B|^|X|; part 2 shows how")
    print("existence (count >= 1) and uniqueness (count <= 1) can each fail.")
    print("The lesson proves the universal property for all sets.")


if __name__ == "__main__":
    main()
