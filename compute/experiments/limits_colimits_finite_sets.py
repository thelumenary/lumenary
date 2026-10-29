"""Limits and colimits of finite sets, computed two ways, and a functor that
fails to preserve a coproduct.

A diagram of finite sets is given by objects (sets) and arrows (functions);
we take diagrams with no composable arrows, so no composites need listing.
Its limit is the set of compatible families; the theorem "products and
equalisers give all limits" builds it instead as an equaliser of two maps
between products. We compute both and compare. Colimits glue: the colimit is
the disjoint union of the objects modulo x ~ f(x), computed with a union-find.
Finally, counting reduced words in Z/2 * Z/3 shows that the underlying set of
a coproduct of groups is far bigger than the coproduct of the underlying sets.
"""

from itertools import product

EXPERIMENT = {
    "id": "limits_colimits_finite_sets",
    "title": "Limits and colimits of finite sets, computed two ways",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["limits-colimits"],
    "summary": (
        "Computes limits of small diagrams of finite sets as compatible families and "
        "as equalisers of two maps between products, and checks they agree; computes "
        "colimits as quotients of disjoint unions with a union-find; and counts reduced "
        "words in Z/2 * Z/3 to compare it with the 5-element coproduct of the "
        "underlying sets. Exact for these finite diagrams."
    ),
    "packages": [],
}


def sections(objects, arrows):
    """Compatible families: one element per object, with f(x_src) = x_dst."""
    names = sorted(objects)
    out = []
    for choice in product(*(objects[n] for n in names)):
        x = dict(zip(names, choice))
        if all(f[x[s]] == x[t] for s, t, f in arrows):
            out.append(x)
    return out


def limit_via_equaliser(objects, arrows):
    """Equaliser of the two maps prod_j D(j) -> prod_(u : s -> t) D(t),
    x |-> (x_t)_u and x |-> (u(x_s))_u. Returns the equalised families."""
    names = sorted(objects)
    families = [dict(zip(names, c)) for c in product(*(objects[n] for n in names))]
    first = [tuple(x[t] for s, t, f in arrows) for x in families]
    second = [tuple(f[x[s]] for s, t, f in arrows) for x in families]
    return [x for x, a, b in zip(families, first, second) if a == b]


def colimit_classes(objects, arrows):
    """Classes of the disjoint union of the objects under x ~ f(x)."""
    parent = {(n, x): (n, x) for n in objects for x in objects[n]}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for s, t, f in arrows:
        for x in objects[s]:
            parent[find((s, x))] = find((t, f[x]))
    classes = {}
    for v in parent:
        classes.setdefault(find(v), []).append(v)
    return sorted(sorted(c) for c in classes.values())


def reduced_words(max_len):
    """Number of reduced words of each length <= max_len in Z/2 * Z/3: letters
    alternate between a (from Z/2) and b, b^2 (from Z/3)."""
    counts = [1]
    for n in range(1, max_len + 1):
        start_a = 2 ** (n // 2)            # a ? a ? ...
        start_b = 2 ** ((n + 1) // 2)      # ? a ? a ...
        counts.append(start_a + start_b)
    return counts


def main():
    A, B, C = range(4), range(3), range(2)
    cospan = {"A": A, "B": B, "C": C}
    cospan_arrows = [("A", "C", {a: a % 2 for a in A}),
                     ("B", "C", {b: (b + 1) % 2 for b in B})]
    pair = {"X": range(6), "Y": range(3)}
    pair_arrows = [("X", "Y", {x: x % 3 for x in range(6)}),
                   ("X", "Y", {x: (2 * x) % 3 for x in range(6)})]
    span = {"K": range(2), "P": range(3), "Q": range(4)}
    span_arrows = [("K", "P", {0: 0, 1: 2}), ("K", "Q", {0: 0, 1: 3})]
    print("Limits as compatible families and via products + equaliser:")
    for name, obj, arr in [("pullback A -> C <- B", cospan, cospan_arrows),
                           ("equaliser X => Y", pair, pair_arrows)]:
        s, e = sections(obj, arr), limit_via_equaliser(obj, arr)
        print(f"  {name:<22} families: {len(s)}, equaliser: {len(e)}, "
              f"same: {s == e}")
    print()
    print("Colimits as glued disjoint unions:")
    glued = colimit_classes(span, span_arrows)
    print(f"  pushout P <- K -> Q    {len(glued)} classes "
          f"(= 3 + 4 - 2: two paths glued at both ends)")
    coeq = colimit_classes(pair, pair_arrows)
    print(f"  coequaliser X => Y     {len(coeq)} classes: Y = {{0, 1, 2}} with 1 ~ 2")
    print()
    words = reduced_words(8)
    print("The forgetful functor Grp -> Set and coproducts:")
    print("  |Z/2 x Z/3| = 6 = 2 * 3, the product of the underlying sets, but")
    print("  |Z/2 + Z/3| = 5 as sets, while Z/2 * Z/3 has reduced words of")
    print(f"  length 0..8 numbering {words},")
    print(f"  {sum(words)} so far - and the lengths never stop.")
    print()
    print("Epistemic status: exact computations on finite examples. They illustrate")
    print("the constructions; that limits are equalisers of products in general,")
    print("and that Z/2 * Z/3 is infinite, are theorems proved in the lesson.")


if __name__ == "__main__":
    main()
