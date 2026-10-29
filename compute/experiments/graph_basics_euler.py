"""Euler trails: an exhaustive check of Euler's theorem on small graphs.

For every one of the 2^10 = 1024 simple graphs on five labelled vertices,
a search through all possible trails decides whether the graph has an Euler
circuit (a closed walk using every edge exactly once) or an Euler trail, and
the answer is compared with Euler's degree condition. The search knows
nothing about degrees, so the agreement is genuine evidence. Then the
Konigsberg multigraph is searched (no trail exists), the handshake lemma is
checked, and Hierholzer's algorithm - the constructive half of the lesson's
proof - builds an Euler circuit of the complete graph K5.
"""

import itertools
from functools import lru_cache

EXPERIMENT = {
    "id": "graph_basics_euler",
    "title": "Euler trails on every graph with five vertices",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["graph-basics"],
    "summary": (
        "Searches all trails in each of the 1024 simple graphs on five "
        "labelled vertices and confirms Euler's criterion for every connected "
        "one: an Euler circuit exists exactly when all degrees are even, an "
        "Euler trail exactly when 0 or 2 degrees are odd. Also shows that the "
        "Konigsberg multigraph has no Euler trail and builds an Euler circuit "
        "of K5 with Hierholzer's algorithm. Exhaustive for five vertices only."
    ),
    "packages": [],
}

KONIGSBERG = [(0, 1), (0, 1), (0, 2), (0, 2), (0, 3), (1, 3), (2, 3)]


def degrees(n, edges):
    """Degree of each vertex 0..n-1: the number of edge-ends there."""
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    return deg


def is_connected(n, edges):
    """True if all n vertices lie in one piece (n >= 1)."""
    seen, stack = {0}, [0]
    while stack:
        v = stack.pop()
        for a, b in edges:
            for x, y in ((a, b), (b, a)):
                if x == v and y not in seen:
                    seen.add(y)
                    stack.append(y)
    return len(seen) == n


def euler_trail_exists(n, edges, closed):
    """Search every trail; True if one uses each edge exactly once."""
    m = len(edges)
    full = (1 << m) - 1

    @lru_cache(maxsize=None)
    def finish(v, used, start):
        if used == full:
            return not closed or v == start
        for i, (a, b) in enumerate(edges):
            if not used >> i & 1 and v in (a, b):
                if finish(b if v == a else a, used | 1 << i, start):
                    return True
        return False

    return any(finish(v, 0, v) for v in range(n))


def hierholzer(n, edges, start=0):
    """An Euler circuit (as a vertex list) of a connected all-even graph."""
    unused = list(range(len(edges)))
    stack, circuit = [start], []
    while stack:
        v = stack[-1]
        nxt = next((i for i in unused if v in edges[i]), None)
        if nxt is None:
            circuit.append(stack.pop())
        else:
            unused.remove(nxt)
            a, b = edges[nxt]
            stack.append(b if v == a else a)
    return circuit[::-1]


def check_all_graphs(n):
    """Count connected graphs on n vertices and disagreements with Euler."""
    pairs = list(itertools.combinations(range(n), 2))
    connected = disagreements = 0
    for mask in range(1 << len(pairs)):
        edges = [p for i, p in enumerate(pairs) if mask >> i & 1]
        if not is_connected(n, edges):
            continue
        connected += 1
        odd = sum(d % 2 for d in degrees(n, edges))
        if euler_trail_exists(n, edges, True) != (odd == 0):
            disagreements += 1
        if euler_trail_exists(n, edges, False) != (odd in (0, 2)):
            disagreements += 1
    return connected, disagreements


def main():
    connected, bad = check_all_graphs(5)
    print("All 1024 simple graphs on 5 labelled vertices:")
    print(f"  connected graphs: {connected}")
    print(f"  disagreements with Euler's criterion: {bad}")
    print()
    deg = degrees(4, KONIGSBERG)
    print(f"Konigsberg: degrees {deg}, sum {sum(deg)} = 2 x 7 bridges")
    print(f"  Euler trail exists: {euler_trail_exists(4, KONIGSBERG, False)}")
    k5 = list(itertools.combinations(range(5), 2))
    circuit = hierholzer(5, k5)
    print(f"K5: degrees {degrees(5, k5)}; Hierholzer's Euler circuit:")
    print("  " + " - ".join(str(v) for v in circuit))
    used = {frozenset(e) for e in zip(circuit, circuit[1:])}
    print(f"  {len(circuit) - 1} steps, {len(used)} different edges, "
          f"back at {circuit[-1]}")
    print()
    print("Epistemic status: exhaustive search over every graph with five")
    print("labelled vertices, so the criterion is verified there and only")
    print("there. The lesson proves Euler's theorem for all finite graphs;")
    print("Lean checks the necessity half.")


if __name__ == "__main__":
    main()
