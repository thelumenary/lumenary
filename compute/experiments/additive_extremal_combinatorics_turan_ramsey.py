"""Extremal graphs and Ramsey numbers by exhaustive search.

1. Turan's theorem on 6 vertices: we run through all 2^15 = 32768 labelled
   graphs on 6 vertices, find the maximum number of edges with no triangle and
   with no K4, and check that every extremal graph is a Turan graph
   (complete multipartite with parts as equal as possible).
2. R(4, 4) > 17: the Paley graph on Z/17 (x ~ y when x - y is a non-zero
   square) has no 4-clique and no independent set of 4 vertices; we check all
   2380 four-element subsets.
3. Bounds for diagonal Ramsey numbers: Erdos's first-moment bound, the
   improvement from the deletion method, and the Erdos-Szekeres upper bound.
"""

import itertools
import math

EXPERIMENT = {
    "id": "additive_extremal_combinatorics_turan_ramsey",
    "title": "Turan graphs and Ramsey numbers by exhaustive search",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["additive-extremal-combinatorics"],
    "summary": (
        "Checks all 32768 labelled graphs on 6 vertices to confirm Turan's theorem "
        "there (ex(6, K3) = 9, ex(6, K4) = 12, extremal graphs exactly the Turan "
        "graphs), verifies that the Paley graph on 17 vertices has no 4-clique or "
        "independent 4-set, so R(4, 4) > 17, and tabulates probabilistic and "
        "Erdos-Szekeres bounds for R(k, k). Exhaustive for the cases shown only."
    ),
    "packages": [],
}


def edge_bits(n):
    """Map each pair {i, j}, i < j, of range(n) to a bit position."""
    return {e: b for b, e in enumerate(itertools.combinations(range(n), 2))}


def clique_masks(n, r, bits):
    """Bit masks of the edge sets of all r-cliques of K_n."""
    masks = []
    for S in itertools.combinations(range(n), r):
        m = 0
        for e in itertools.combinations(S, 2):
            m |= 1 << bits[e]
        masks.append(m)
    return masks


def is_free(graph, masks):
    """True if the graph (an edge bit mask) contains none of the given cliques."""
    return all(graph & m != m for m in masks)


def non_adjacency_classes(graph, n, bits):
    """Sizes of the classes of 'equal or non-adjacent', if it is an equivalence
    relation (i.e. the graph is complete multipartite); otherwise None."""
    def adj(i, j):
        return i != j and graph >> bits[(min(i, j), max(i, j))] & 1
    classes, seen = [], set()
    for i in range(n):
        if i in seen:
            continue
        cls = {j for j in range(n) if not adj(i, j)}
        if any(adj(a, b) for a in cls for b in cls):
            return None
        seen |= cls
        classes.append(len(cls))
    return sorted(classes)


def turan_part_sizes(n, r):
    """Part sizes of the Turan graph T(n, r): as equal as possible."""
    return sorted([n // r + (1 if i < n % r else 0) for i in range(r)])


def turan_edges(n, r):
    """Number of edges of T(n, r)."""
    parts = turan_part_sizes(n, r)
    return (n * n - sum(p * p for p in parts)) // 2


def extremal_graphs(n, r):
    """(max edges, list of extremal graphs) among K_(r+1)-free graphs on n vertices."""
    bits = edge_bits(n)
    masks = clique_masks(n, r + 1, bits)
    best, graphs = -1, []
    for g in range(1 << len(bits)):
        if is_free(g, masks):
            e = bin(g).count("1")
            if e > best:
                best, graphs = e, [g]
            elif e == best:
                graphs.append(g)
    return best, graphs


def paley_graph(q):
    """Adjacency sets of the Paley graph on Z/q (q prime, q = 1 mod 4)."""
    squares = {x * x % q for x in range(1, q)}
    return [{y for y in range(q) if (x - y) % q in squares} for x in range(q)]


def homogeneous_sets(adj, k):
    """Number of k-sets that are cliques or independent sets."""
    count = 0
    for S in itertools.combinations(range(len(adj)), k):
        pairs = [(a, b) for a, b in itertools.combinations(S, 2)]
        edges = sum(1 for a, b in pairs if b in adj[a])
        count += edges == 0 or edges == len(pairs)
    return count


def erdos_bound(k):
    """Largest n with C(n, k) 2^(1 - C(k, 2)) < 1 (so R(k, k) > n)."""
    n = k
    while math.comb(n + 1, k) * 2 < 2 ** math.comb(k, 2):
        n += 1
    return n


def deletion_bound(k):
    """max over n of floor(n - C(n, k) 2^(1 - C(k, 2))) (so R(k, k) > it).

    Exact integer arithmetic: floor(n - x) = n - ceil(x)."""
    best, n, denominator = 0, k, 2 ** math.comb(k, 2)
    while True:
        value = n - (-(-2 * math.comb(n, k) // denominator))
        if value < best - 50:
            return best
        best = max(best, value)
        n += 1


def main():
    n = 6
    bits = edge_bits(n)
    print(f"1. All {2 ** len(bits)} labelled graphs on {n} vertices:")
    for r in (2, 3):
        best, graphs = extremal_graphs(n, r)
        shapes = {tuple(non_adjacency_classes(g, n, bits) or ()) for g in graphs}
        print(f"   no K{r + 1}: max {best} edges (T({n},{r}) has "
              f"{turan_edges(n, r)}); {len(graphs)} extremal graphs,")
        print(f"   all complete multipartite with parts {sorted(shapes)} "
              f"(Turan: {tuple(turan_part_sizes(n, r))})")
    print()
    adj = paley_graph(17)
    print("2. Paley graph on Z/17 (x ~ y iff x - y is a non-zero square):")
    print(f"   degree {len(adj[0])}; 4-sets that are cliques or independent: "
          f"{homogeneous_sets(adj, 4)} of {math.comb(17, 4)}")
    print(f"   triangles or independent 3-sets: {homogeneous_sets(adj, 3)}")
    print("   so R(4, 4) > 17 (and R(4, 4) = 18: Greenwood-Gleason, 1955)")
    print()
    print("3. Bounds for R(k, k):")
    print("    k   first moment   deletion   Erdos-Szekeres C(2k-2, k-1)")
    for k in range(4, 11):
        print(f"   {k:2d}   {erdos_bound(k):12d}   {deletion_bound(k):8d}   "
              f"{math.comb(2 * k - 2, k - 1):27d}")
    print("   (lower bounds: R(k, k) exceeds the number shown)")
    print()
    print("Epistemic status: parts 1 and 2 are exact and exhaustive for 6 and 17")
    print("vertices, so they prove these finite statements if the code is right;")
    print("Turan's and Ramsey's theorems for all n are proved in the lesson. Part")
    print("3 is exact arithmetic applied to proved bounds; it says nothing about")
    print("the true values, which are unknown for k >= 5.")


if __name__ == "__main__":
    main()
