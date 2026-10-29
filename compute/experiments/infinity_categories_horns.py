"""Horn filling in nerves of small categories, by exhaustive search.

The nerve of a category C has as n-simplices the strings of n composable
arrows. A horn Lambda^n_k is a simplex with its k-th face (and interior)
missing; it is inner if 0 < k < n. We enumerate every horn of dimension 2 and
3 in the nerves of four small categories and count how many can be filled and
in how many ways:

* the poset 0 < 1 < 2,
* the "walking idempotent": one object, arrows 1 and e with e e = e,
* the group Z/3 as a one-object groupoid,
* the "walking isomorphism": objects 0, 1 and inverse arrows u, v.

The search confirms, in these cases, that inner horns in a nerve always have
exactly one filler (nerves are quasi-categories with unique inner fillers),
that outer horns fill in the two groupoids (their nerves are Kan complexes),
and that outer horns can fail to fill, or fill in several ways, otherwise.
Exact, exhaustive evidence for these finite categories and dimensions only.
"""

from itertools import product

EXPERIMENT = {
    "id": "infinity_categories_horns",
    "title": "Horn filling in nerves of small categories",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["infinity-categories"],
    "summary": (
        "Enumerates every 2- and 3-dimensional horn in the nerves of four small "
        "categories (a poset, a monoid with an idempotent, the group Z/3, the "
        "walking isomorphism) and counts fillers: inner horns fill uniquely, "
        "outer horns fill in groupoids and may fail or fill non-uniquely "
        "otherwise. Exhaustive for these categories and dimensions only."
    ),
    "packages": [],
}


class SmallCategory:
    """A finite category: objects, arrows with source and target, composition.

    ``compose(f, g)`` is "f then g" (diagrammatic order), defined when the
    target of f is the source of g.
    """

    def __init__(self, name, arrows, compose):
        self.name = name
        self.arrows = arrows          # dict: arrow -> (source, target)
        self.compose = compose
        self.objects = sorted({s for s, _ in arrows.values()}
                              | {t for _, t in arrows.values()})

    def hom(self, x, y):
        """All arrows from x to y."""
        return [a for a, st in self.arrows.items() if st == (x, y)]


def poset_category(n):
    """The poset 0 < 1 < ... < n-1 as a category: one arrow i -> j iff i <= j."""
    arrows = {(i, j): (i, j) for i in range(n) for j in range(i, n)}
    return SmallCategory(f"poset [{n - 1}]", arrows,
                         lambda f, g: (f[0], g[1]))


def monoid_category(name, table):
    """A one-object category from a monoid's multiplication table."""
    arrows = {m: (0, 0) for m in table}
    return SmallCategory(name, arrows, lambda f, g: table[f][g])


def walking_isomorphism():
    """Objects 0 and 1, arrows u: 0 -> 1 and v: 1 -> 0 inverse to each other."""
    arrows = {"1_0": (0, 0), "1_1": (1, 1), "u": (0, 1), "v": (1, 0)}

    def compose(f, g):
        table = {("u", "v"): "1_0", ("v", "u"): "1_1"}
        if f.startswith("1_"):
            return g
        if g.startswith("1_"):
            return f
        return table[(f, g)]

    return SmallCategory("walking iso", arrows, compose)


def edge_assignments(cat, vertices_count, edges):
    """All ways to choose objects for the vertices and arrows for ``edges``."""
    for objs in product(cat.objects, repeat=vertices_count):
        homs = [cat.hom(objs[a], objs[b]) for a, b in edges]
        for choice in product(*homs):
            yield dict(zip(edges, choice))


def triangle_commutes(cat, f, a, b, c):
    """Does the triangle on vertices a < b < c commute: f_ab ; f_bc = f_ac?"""
    return cat.compose(f[(a, b)], f[(b, c)]) == f[(a, c)]


def horn_census(cat, n, k):
    """Count horns Lambda^n_k -> N(cat), fillable horns, and the largest
    number of fillers of a single horn (n = 2 or 3)."""
    all_edges = [(a, b) for a in range(n + 1) for b in range(a + 1, n + 1)]
    if n == 2:
        # The horn has the two edges through vertex k; the filler adds the third.
        horn_edges = [e for e in all_edges if k in e]
        horns = fillable = most = 0
        for f in edge_assignments(cat, 3, horn_edges):
            horns += 1
            (missing,) = [e for e in all_edges if k not in e]
            fillers = [x for x in cat.hom(*objects_of(cat, f, missing))
                       if triangle_commutes(cat, {**f, missing: x}, 0, 1, 2)]
            fillable += bool(fillers)
            most = max(most, len(fillers))
        return horns, fillable, most
    # n == 3: the horn contains all six edges and the faces other than d_k.
    faces = [tuple(v for v in range(4) if v != i) for i in range(4)]
    horns = fillable = 0
    for f in edge_assignments(cat, 4, all_edges):
        if all(triangle_commutes(cat, f, *faces[i]) for i in range(4) if i != k):
            horns += 1
            fillable += triangle_commutes(cat, f, *faces[k])
    return horns, fillable, 1 if fillable else 0


def objects_of(cat, f, edge):
    """Source and target objects of a missing edge, read off the horn."""
    a, b = edge
    obj = {}
    for (x, y), arrow in f.items():
        obj[x], obj[y] = cat.arrows[arrow]
    return obj[a], obj[b]


CATEGORIES = [
    poset_category(3),
    monoid_category("idempotent", {"1": {"1": "1", "e": "e"},
                                         "e": {"1": "e", "e": "e"}}),
    monoid_category("group Z/3", {i: {j: (i + j) % 3 for j in range(3)}
                                  for i in range(3)}),
    walking_isomorphism(),
]


def main():
    print("Horn L(n,k): fillable horns/all horns (most fillers of one horn)")
    print(f"{'category':<12}" + "".join(f"{f'L({n},{k})':>9}"
                                       for n, k in HORNS))
    for cat in CATEGORIES:
        cells = []
        for n, k in HORNS:
            horns, ok, most = horn_census(cat, n, k)
            cells.append(f"{f'{ok}/{horns}({most})':>9}")
        print(f"{cat.name:<12}" + "".join(cells))
    print("Inner: L(2,1), L(3,1), L(3,2). Outer: L(2,0), L(2,2), L(3,0), L(3,3).")
    print()
    idem = CATEGORIES[1]
    for f01, f02 in [("e", "1"), ("e", "e")]:
        fillers = [g for g in idem.arrows if idem.compose(f01, g) == f02]
        print(f"Idempotent, outer horn L(2,0) with f01 = {f01}, f02 = {f02}: "
              f"fillers {fillers}")
    print()
    print("Epistemic status: exact, exhaustive enumeration of all 2- and")
    print("3-dimensional horns in four small categories. It illustrates, but")
    print("does not prove, that nerves have unique inner fillers in every")
    print("dimension and that nerves of groupoids are Kan complexes.")


HORNS = [(2, 1), (2, 0), (2, 2), (3, 1), (3, 2), (3, 0), (3, 3)]


if __name__ == "__main__":
    main()
