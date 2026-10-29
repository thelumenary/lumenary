"""Pointwise Kan extensions of finite set-valued functors, computed exactly.

The pointwise formulas say that a left Kan extension is a colimit over a
comma category and a right Kan extension is a limit. For diagrams of finite
sets both can be computed exactly: a colimit is a disjoint union glued by a
union-find structure, a limit is the set of compatible families. We use this
to (1) compare Lan and Ran along an inclusion of finite posets (coproducts
versus products, initial versus terminal objects), (2) see that a colimit over
a category with a terminal object is the value there, and (3) induce and
coinduce actions of subgroups H of S3, checking |G x_H X| = [G:H] |X| and
|Hom_H(G, X)| = |X|^[G:H]. This is exact, exhaustive computation in finite
cases; the general theorems are proved in the lesson.
"""

from itertools import permutations, product

EXPERIMENT = {
    "id": "kan_extensions_pointwise",
    "title": "Pointwise Kan extensions of finite sets: colimits and limits",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["kan-extensions"],
    "summary": (
        "Computes left and right Kan extensions of functors into finite sets by "
        "their pointwise formulas (colimits by union-find, limits as compatible "
        "families): Lan and Ran along a map of finite posets give coproducts and "
        "products, and Kan extension along BH -> BS3 gives induced and "
        "coinduced H-sets of sizes [G:H]|X| and |X|^[G:H]. Exact for these "
        "finite cases only; the general theorems are proved in the lesson."
    ),
    "packages": [],
}


def colimit(sets, arrows):
    """Colimit of a finite diagram of finite sets.

    ``sets`` maps each object to a list of elements; ``arrows`` is a list of
    ``(source, target, function)``. Returns the equivalence classes of the
    disjoint union {(object, element)} under (s, x) ~ (t, function(x)).
    """
    parent = {(o, x): (o, x) for o in sets for x in sets[o]}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for source, target, fn in arrows:
        for x in sets[source]:
            ra, rb = find((source, x)), find((target, fn(x)))
            if ra != rb:
                parent[ra] = rb
    classes = {}
    for a in parent:
        classes.setdefault(find(a), set()).add(a)
    return [frozenset(c) for c in classes.values()]


def limit(sets, arrows):
    """Limit of a finite diagram of finite sets: all compatible families.

    A family picks one element of each set; it is compatible when
    ``function(family[source]) == family[target]`` for every arrow. The empty
    diagram has exactly one (empty) family: the limit is a one-point set.
    """
    objects = list(sets)
    families = []
    for values in product(*(sets[o] for o in objects)):
        family = dict(zip(objects, values))
        if all(fn(family[s]) == family[t] for s, t, fn in arrows):
            families.append(family)
    return families


def thin_diagram(objects, leq, sets, fmap):
    """Restrict a functor on a poset to ``objects`` (all arrows c < c')."""
    arrows = [
        (c, c2, (lambda x, c=c, c2=c2: fmap(c, c2, x)))
        for c in objects
        for c2 in objects
        if c != c2 and leq(c, c2)
    ]
    return {c: sets[c] for c in objects}, arrows


def lan_size(C, leq_c, k, leq_d, d, sets, fmap):
    """|Lan_k F (d)|: the colimit of F over the comma category (k | d)."""
    comma = [c for c in C if leq_d(k(c), d)]
    return len(colimit(*thin_diagram(comma, leq_c, sets, fmap)))


def ran_size(C, leq_c, k, leq_d, d, sets, fmap):
    """|Ran_k F (d)|: the limit of F over the comma category (d | k)."""
    comma = [c for c in C if leq_d(d, k(c))]
    return len(limit(*thin_diagram(comma, leq_c, sets, fmap)))


def compose(p, q):
    """Composite permutation p o q (first q, then p) of tuples."""
    return tuple(p[i] for i in q)


S3 = sorted(permutations(range(3)))


def induced_diagram(G, H, X, act):
    """F o proj on the comma category (i | *) for i : BH -> BG.

    Objects are g in G; for g2 in G and h in H there is an arrow
    g2 h -> g2 acting on X by h. Its colimit is G x_H X.
    """
    sets = {g: list(X) for g in G}
    arrows = [(compose(g2, h), g2, (lambda x, h=h: act(h, x)))
              for g2 in G for h in H]
    return sets, arrows


def coinduced_diagram(G, H, X, act):
    """F o proj on (* | i): arrows g -> h g acting by h; limit Hom_H(G, X)."""
    sets = {g: list(X) for g in G}
    arrows = [(g, compose(h, g), (lambda x, h=h: act(h, x)))
              for g in G for h in H]
    return sets, arrows


def sign(p):
    """Sign of a permutation tuple (+1 or -1), by counting inversions."""
    inv = sum(1 for i in range(len(p)) for j in range(i) if p[j] > p[i])
    return -1 if inv % 2 else 1


# Poset example: C = {a, b} discrete inside D = {bot < a, b < top}.
POSET_C = ["a", "b"]
POSET_D = ["bot", "a", "b", "top"]
POSET_SETS = {"a": [0, 1], "b": [0, 1, 2]}


def leq_d(x, y):
    """The order of D = {bot < a, b < top}."""
    return x == y or x == "bot" or y == "top"


def leq_discrete(x, y):
    """The discrete order: only x <= x."""
    return x == y


# Chain example: 0 < 1 < 2 with F(0) -> F(1) -> F(2).
CHAIN = [0, 1, 2]
CHAIN_SETS = {0: list(range(4)), 1: list(range(3)), 2: list(range(2))}


def chain_map(c, c2, x):
    """F(c <= c2): halve from F(0) to F(1), take parity from F(1) to F(2)."""
    if c == 0 and c2 >= 1:
        x, c = x // 2, 1
    if c == 1 and c2 == 2:
        x = x % 2
    return x


def subgroup_cases():
    """(name, H, X, action) for the induction table."""
    swap = [(0, 1, 2), (1, 0, 2)]
    a3 = [p for p in S3 if sign(p) == 1]
    return [
        ("H = <(0 1)>, X = {+1,-1}, sign", swap, [1, -1],
         lambda h, x: sign(h) * x),
        ("H = A3, X = {0,1,2}, rotation", a3, [0, 1, 2],
         lambda h, x: h[x]),
        ("H = 1, X = {*}", [(0, 1, 2)], ["*"], lambda h, x: x),
    ]


def main():
    print("1. Lan and Ran along C = {a, b} (discrete) -> D = {bot < a, b < top}")
    print("   with |F a| = 2, |F b| = 3:")
    print("   d     |Lan F(d)|  |Ran F(d)|")
    for d in POSET_D:
        lan = lan_size(POSET_C, leq_discrete, lambda c: c, leq_d, d,
                       POSET_SETS, None)
        ran = ran_size(POSET_C, leq_discrete, lambda c: c, leq_d, d,
                       POSET_SETS, None)
        print(f"   {d:<5} {lan:>10}  {ran:>10}")
    print("   Lan(top) is the coproduct 2 + 3, Ran(bot) the product 2 x 3;")
    print("   Lan(bot) = 0 is an empty colimit, Ran(top) = 1 an empty limit.")
    print()
    print("2. Along C = {0 < 1 < 2} -> 1 with |F| = 4, 3, 2:")
    sets, arrows = thin_diagram(CHAIN, lambda x, y: x <= y, CHAIN_SETS,
                                chain_map)
    print(f"   colim F has {len(colimit(sets, arrows))} elements = |F(2)|"
          f" (2 is terminal); lim F has {len(limit(sets, arrows))} = |F(0)|.")
    print()
    print("3. Kan extension along BH -> BG, G = S3 (|G| = 6):")
    print("   case                                 [G:H]  |Lan|  |Ran|")
    for name, H, X, act in subgroup_cases():
        index = len(S3) // len(H)
        lan = len(colimit(*induced_diagram(S3, H, X, act)))
        ran = len(limit(*coinduced_diagram(S3, H, X, act)))
        print(f"   {name:<37} {index:>5}  {lan:>5}  {ran:>5}")
    print("   Lan = G x_H X has [G:H]|X| elements; Ran = Hom_H(G, X) has")
    print("   |X|^[G:H]. For H = 1, Lan is G acting on itself: the free G-set.")
    print()
    print("Epistemic status: exact computation of finite colimits and limits;")
    print("it confirms the pointwise formulas and the induction counts only in")
    print("these finite examples. The general statements (the pointwise")
    print("formula and its consequences) are theorems proved in the lesson.")


if __name__ == "__main__":
    main()
