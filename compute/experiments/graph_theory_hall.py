"""Hall's condition, augmenting paths and Konig's theorem on random graphs.

For a bipartite graph with parts A and B, Hall's theorem says: there is a
matching covering A if and only if |N(S)| >= |S| for every S subset of A.
We test it on 400 seeded random bipartite graphs with |A| = |B| = 5:

* Hall's condition is checked directly, over all 2^5 subsets S of A;
* a maximum matching is found by augmenting paths (Kuhn's algorithm);
* the deficiency form of Hall's theorem, max matching = |A| - max(|S| -
  |N(S)|), and Konig's theorem, max matching = min vertex cover (found by
  brute force over all 2^10 vertex sets), are checked as well.

This is experimental evidence on small graphs. The proofs are in the lesson.
"""

import itertools
import random

EXPERIMENT = {
    "id": "graph_theory_hall",
    "title": "Hall's marriage theorem and Konig's theorem, tested",
    "evidence": ["exact", "experimental"],
    "lessons": ["graph-theory"],
    "summary": (
        "On 400 seeded random bipartite graphs with five vertices on each side, "
        "compares Hall's condition (all subsets) with augmenting-path matchings, "
        "and checks the deficiency version of Hall's theorem and Konig's theorem "
        "(maximum matching = minimum vertex cover, by brute force). Experimental "
        "evidence on small graphs only."
    ),
    "packages": [],
}


def random_bipartite(a, b, p, rng):
    """Neighbour sets N(i) in range(b) for each i in range(a)."""
    return [frozenset(j for j in range(b) if rng.random() < p) for _ in range(a)]


def neighbourhood(adj, subset):
    """N(S): all vertices of B adjacent to some vertex of S."""
    out = set()
    for i in subset:
        out |= adj[i]
    return out


def hall_violator(adj):
    """A set S with |N(S)| < |S|, or None if Hall's condition holds."""
    for size in range(1, len(adj) + 1):
        for subset in itertools.combinations(range(len(adj)), size):
            if len(neighbourhood(adj, subset)) < size:
                return subset
    return None


def max_deficiency(adj):
    """max over S of |S| - |N(S)|, including S = empty set (value 0)."""
    return max(len(s) - len(neighbourhood(adj, s))
               for size in range(len(adj) + 1)
               for s in itertools.combinations(range(len(adj)), size))


def maximum_matching(adj):
    """Kuhn's augmenting-path algorithm; return a dict B-vertex -> A-vertex."""
    match = {}

    def augment(i, seen):
        for j in sorted(adj[i]):
            if j not in seen:
                seen.add(j)
                if j not in match or augment(match[j], seen):
                    match[j] = i
                    return True
        return False

    for i in range(len(adj)):
        augment(i, set())
    return match


def min_vertex_cover(adj, b):
    """Smallest set of vertices touching every edge, by brute force."""
    edges = [(i, j) for i, nbrs in enumerate(adj) for j in nbrs]
    vertices = [("A", i) for i in range(len(adj))] + [("B", j) for j in range(b)]
    for size in range(len(vertices) + 1):
        for cover in itertools.combinations(vertices, size):
            chosen = set(cover)
            if all(("A", i) in chosen or ("B", j) in chosen for i, j in edges):
                return size
    return len(vertices)


def main():
    rng = random.Random(1935)
    a = b = 5
    graphs = [random_bipartite(a, b, rng.choice([0.25, 0.35, 0.5]), rng)
              for _ in range(400)]
    hall_ok = covering = agree = deficiency_ok = konig_ok = 0
    example = None
    for adj in graphs:
        violator = hall_violator(adj)
        m = len(maximum_matching(adj))
        hall_ok += violator is None
        covering += m == a
        agree += (violator is None) == (m == a)
        deficiency_ok += m == a - max_deficiency(adj)
        konig_ok += m == min_vertex_cover(adj, b)
        interesting = violator is not None and len(violator) >= 2
        if interesting and example is None and all(adj):
            example = (adj, violator)
    print(f"400 random bipartite graphs, |A| = |B| = {a}")
    print(f"  Hall's condition holds:               {hall_ok}")
    print(f"  a matching covers A (augmenting):     {covering}")
    print(f"  the two answers agree:                {agree}/400")
    print(f"  max matching = |A| - max deficiency:  {deficiency_ok}/400")
    print(f"  max matching = min vertex cover:      {konig_ok}/400")
    adj, s = example
    nbrs = sorted(neighbourhood(adj, s))
    print("A graph failing Hall's condition, though every vertex has a neighbour:")
    for i, row in enumerate(adj):
        print(f"  a{i} -> {sorted(row)}")
    print(f"  S = {[f'a{i}' for i in s]} has only {len(nbrs)} neighbours {nbrs}")
    print()
    print("Epistemic status: exact computations on 400 seeded random graphs, "
          "all\nconsistent with Hall's theorem, its deficiency form and Konig's "
          "theorem.\nThis is experimental evidence for small graphs; the "
          "theorems are proved in\nthe lesson (and Hall's theorem in Lean).")


if __name__ == "__main__":
    main()
