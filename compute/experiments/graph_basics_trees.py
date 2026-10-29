"""Trees and isomorphism, by exhaustive search on small vertex sets.

Every set of n - 1 edges on the vertices 0..n-1 (n <= 7) is examined: it is
connected exactly when it has no cycle, exactly when it is a tree - the
"two out of three" property proved in the lesson - and the labelled trees
number n^(n-2), as Cayley's formula predicts. The trees are then sorted into
isomorphism classes with a canonical code (Aho-Hopcroft-Ullman: root the tree
at its centre and encode it recursively). Finally an isomorphism between a
pentagon and a pentagram is found by trying all 120 bijections, and two
graphs with the same degrees are told apart by connectedness.
"""

import itertools

EXPERIMENT = {
    "id": "graph_basics_trees",
    "title": "Counting trees and sorting graphs by isomorphism",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["graph-basics"],
    "summary": (
        "Checks every set of n - 1 edges on n <= 7 labelled vertices: connected "
        "exactly when acyclic, and there are n^(n-2) labelled trees (Cayley's "
        "formula). Sorts the trees into isomorphism classes with a canonical "
        "code (1, 1, 1, 2, 3, 6, 11 classes), finds an isomorphism between a "
        "pentagon and a pentagram by trying all 120 bijections, and separates "
        "two graphs with equal degrees by connectedness. Small cases only."
    ),
    "packages": [],
}


def components(n, edges):
    """Number of connected pieces, by merging endpoints (union-find)."""
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for a, b in edges:
        parent[root(a)] = root(b)
    return len({root(v) for v in range(n)})


def has_cycle(n, edges):
    """True if some edge joins two vertices already joined by a path."""
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for a, b in edges:
        ra, rb = root(a), root(b)
        if ra == rb:
            return True
        parent[ra] = rb
    return False


def tree_census(n):
    """(edge sets of size n-1, connected ones, acyclic ones), all trees."""
    pairs = list(itertools.combinations(range(n), 2))
    total = conn = acyc = 0
    trees = []
    for edges in itertools.combinations(pairs, n - 1):
        total += 1
        c, a = components(n, edges) == 1, not has_cycle(n, edges)
        conn, acyc = conn + c, acyc + a
        if c:
            trees.append(edges)
    return total, conn, acyc, trees


def canonical_tree(n, edges):
    """A code equal for two trees exactly when they are isomorphic (AHU)."""
    nbrs = {v: set() for v in range(n)}
    for a, b in edges:
        nbrs[a].add(b)
        nbrs[b].add(a)
    layer, left = [v for v in nbrs if len(nbrs[v]) <= 1], set(nbrs)
    while len(left) > 2:  # strip leaves until the centre (1 or 2 vertices)
        left -= set(layer)
        layer = [v for v in left if len(nbrs[v] & left) <= 1]

    def code(v, parent):
        return "(" + "".join(sorted(code(w, v) for w in nbrs[v]
                                    if w != parent)) + ")"

    return min(code(c, None) for c in left)


def find_isomorphism(n, edges1, edges2):
    """A bijection of 0..n-1 carrying edges1 onto edges2, or None."""
    target = {frozenset(e) for e in edges2}
    for perm in itertools.permutations(range(n)):
        if {frozenset((perm[a], perm[b])) for a, b in edges1} == target:
            return perm
    return None


def main():
    print(" n  edge sets  connected  acyclic  trees  n^(n-2)  classes")
    for n in range(2, 8):
        total, conn, acyc, trees = tree_census(n)
        classes = len({canonical_tree(n, t) for t in trees})
        print(f"{n:2d}  {total:9d}  {conn:9d}  {acyc:7d}  {len(trees):5d}"
              f"  {n ** (n - 2):7d}  {classes:7d}")
    print("(n = 1: one tree, one class.)")
    print()
    pentagon = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    pentagram = [(0, 2), (2, 4), (4, 1), (1, 3), (3, 0)]
    print(f"Pentagon -> pentagram isomorphism: "
          f"{find_isomorphism(5, pentagon, pentagram)}")
    hexagon = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]
    triangles = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
    print("Hexagon vs two triangles: all six degrees 2 in both;")
    print(f"  pieces {components(6, hexagon)} vs "
          f"{components(6, triangles)}; isomorphism: "
          f"{find_isomorphism(6, hexagon, triangles)}")
    print()
    print("Epistemic status: exhaustive search over all edge sets for n <= 7")
    print("(evidence for the tree theorems and Cayley's formula, which hold")
    print("for every n) and over all bijections for the two examples (a")
    print("complete check, so those isomorphism verdicts are certain).")


if __name__ == "__main__":
    main()
