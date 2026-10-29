"""Shortest paths are free enriched categories.

A Lawvere metric space is a category enriched in ([0, inf], >=, +, 0):
hom-objects are distances, composition is the triangle inequality and
identities say d(x, x) = 0. Just as a directed graph generates a free
category (whose morphisms are paths), a directed graph with lengths generates
a free Lawvere metric: the shortest-path distance. Composition of hom-objects
becomes "min-plus" (tropical) matrix multiplication, and a Lawvere metric is
exactly a matrix D with zero diagonal and D (x) D = D.

We compute this for walking times in a small hill town, where going uphill
takes longer than coming down, check every axiom on every triple, and
measure the asymmetry. Replacing (min, +) by (or, and) computes the free
preorder (reachability) - the same algorithm for truth-value enrichment.
Finally we check that the asymmetric Hausdorff distance between sets of
places is again a Lawvere metric. Exact integer arithmetic; exhaustive.
"""

import itertools

EXPERIMENT = {
    "id": "enriched_categories_shortest_paths",
    "title": "Shortest paths as free Lawvere metric spaces",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["enriched-categories"],
    "summary": (
        "Computes the shortest-path distance of a small directed graph of "
        "uphill/downhill walking times by min-plus matrix multiplication (free "
        "[0, inf]-enriched category), checks d(x, x) = 0, the triangle "
        "inequality and D (x) D = D on all triples, counts asymmetric pairs, "
        "computes reachability with (or, and), and checks the asymmetric "
        "Hausdorff distance on all sets of places."
    ),
    "packages": [],
}

INF = float("inf")
PLACES = ["Market", "School", "Clinic", "Spring", "Ridge"]
# Walking times in minutes along footpaths (directed: uphill is slower).
PATHS = {
    ("Market", "School"): 6, ("School", "Market"): 4,
    ("School", "Clinic"): 9, ("Clinic", "School"): 5,
    ("Market", "Spring"): 3, ("Spring", "Market"): 3,
    ("Spring", "Clinic"): 12, ("Clinic", "Spring"): 7,
    ("Clinic", "Ridge"): 15, ("Ridge", "Clinic"): 8,
    ("Ridge", "Market"): 20,
}


def weight_matrix(places, paths):
    """Direct walking times: 0 on the diagonal, inf where there is no path."""
    n = len(places)
    idx = {p: i for i, p in enumerate(places)}
    w = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for (a, b), t in paths.items():
        w[idx[a]][idx[b]] = min(w[idx[a]][idx[b]], t)
    return w


def min_plus(a, b):
    """Tropical matrix product: (A (x) B)[i][k] = min_j A[i][j] + B[j][k]."""
    n = len(a)
    return [[min(a[i][j] + b[j][k] for j in range(n)) for k in range(n)]
            for i in range(n)]


def closure(w, product=min_plus):
    """Iterate D -> D (x) D until it stabilises (the free enriched category)."""
    d = w
    while True:
        nxt = product(d, d)
        if nxt == d:
            return d
        d = nxt


def is_lawvere_metric(d):
    """d(x, x) = 0 and d(x, z) <= d(x, y) + d(y, z) for all x, y, z."""
    n = len(d)
    if any(d[i][i] != 0 for i in range(n)):
        return False
    return all(d[i][k] <= d[i][j] + d[j][k]
               for i, j, k in itertools.product(range(n), repeat=3))


def asymmetric_pairs(d):
    """Unordered pairs {x, y} with d(x, y) != d(y, x)."""
    n = len(d)
    return [(i, j) for i in range(n) for j in range(i + 1, n)
            if d[i][j] != d[j][i]]


def or_and(a, b):
    """Boolean matrix product: (A (x) B)[i][k] = OR_j A[i][j] AND B[j][k]."""
    n = len(a)
    return [[any(a[i][j] and b[j][k] for j in range(n)) for k in range(n)]
            for i in range(n)]


def hausdorff(d, s, t):
    """Asymmetric Hausdorff distance: max over s of the distance to t."""
    if not s:
        return 0
    return max(min((d[x][y] for y in t), default=INF) for x in s)


def main():
    w = weight_matrix(PLACES, PATHS)
    d = closure(w)
    n = len(PLACES)
    print("Shortest walking times d(x, y) in minutes (row x, column y):")
    print("          " + "".join(f"{p[:6]:>8}" for p in PLACES))
    for name, row in zip(PLACES, d):
        print(f"  {name:<8}" + "".join(f"{v:>8}" for v in row))
    triples = n ** 3
    print(f"d(x, x) = 0 and triangle inequality on all {triples} triples: "
          f"{is_lawvere_metric(d)}")
    print(f"D (x) D = D (composition is idempotent):        "
          f"{min_plus(d, d) == d}")
    print(f"direct paths are never shorter than d:          "
          f"{all(d[i][j] <= w[i][j] for i in range(n) for j in range(n))}")
    asym = asymmetric_pairs(d)
    i, j = asym[0]
    print(f"asymmetric pairs: {len(asym)} of {n * (n - 1) // 2}, e.g. "
          f"d({PLACES[i]}, {PLACES[j]}) = {d[i][j]}, "
          f"d({PLACES[j]}, {PLACES[i]}) = {d[j][i]}")
    reach = closure([[v < INF for v in row] for row in w], product=or_and)
    print(f"truth-value enrichment (reachability) agrees: "
          f"{reach == [[v < INF for v in row] for row in d]}")
    subsets = [s for k in range(1, n + 1)
               for s in itertools.combinations(range(n), k)]
    h = [[hausdorff(d, s, t) for t in subsets] for s in subsets]
    print(f"asymmetric Hausdorff distance, {len(subsets)} nonempty sets of "
          f"places: Lawvere metric? {is_lawvere_metric(h)}")
    print()
    print("Epistemic status: exact computation, exhaustive over this one "
          "small graph\n(every triple of places, every triple of sets). It "
          "illustrates, but does\nnot prove, the general facts in the lesson: "
          "shortest-path distance is the\nfree Lawvere metric on a weighted "
          "graph, and Hausdorff distances obey the\ntriangle inequality.")


if __name__ == "__main__":
    main()
