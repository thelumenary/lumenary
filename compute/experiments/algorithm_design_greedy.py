"""Greedy algorithms against brute force: when they work and when they fail.

1. Kruskal's algorithm is compared with an exhaustive search over all
   spanning trees of seeded random weighted graphs on 5 vertices.
2. Dijkstra's algorithm is compared with Bellman-Ford on random directed
   acyclic graphs, first with non-negative weights and then allowing negative
   ones, where Dijkstra's greedy choice can be wrong.
3. Greedy change-making is compared with dynamic programming for every coin
   system {1, a, b} with b <= 12. By a theorem of Kozen and Zaks (1994), if
   greedy is ever suboptimal, it already fails for some amount below a + b,
   so checking those amounts decides each system completely.
"""

import heapq
import itertools
import random

EXPERIMENT = {
    "id": "algorithm_design_greedy",
    "title": "Greedy algorithms: Kruskal, Dijkstra and making change",
    "evidence": ["exhaustive-finite", "experimental", "counterexample"],
    "lessons": ["algorithm-design"],
    "summary": (
        "Checks Kruskal's algorithm against exhaustive search over all spanning "
        "trees of 300 random graphs, Dijkstra against Bellman-Ford with and "
        "without negative edge weights (finding counterexamples in the second "
        "case), and greedy change-making against dynamic programming for all "
        "coin systems {1, a, b} with b <= 12."
    ),
    "packages": [],
}


def find(parent, x):
    """Union-find root of x, with path halving."""
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def kruskal(n, edges):
    """Total weight of a minimum spanning tree; edges are (w, u, v)."""
    parent, total, used = list(range(n)), 0, 0
    for w, u, v in sorted(edges):
        ru, rv = find(parent, u), find(parent, v)
        if ru != rv:
            parent[ru] = rv
            total, used = total + w, used + 1
    if used != n - 1:
        raise ValueError("graph is not connected")
    return total


def brute_force_mst(n, edges):
    """Minimum weight over all (n-1)-edge subsets that form a spanning tree."""
    best = None
    for subset in itertools.combinations(edges, n - 1):
        parent, ok = list(range(n)), True
        for _, u, v in subset:
            ru, rv = find(parent, u), find(parent, v)
            if ru == rv:
                ok = False
                break
            parent[ru] = rv
        if ok:
            weight = sum(w for w, _, _ in subset)
            best = weight if best is None else min(best, weight)
    return best


def dijkstra(n, adj, source=0):
    """Distances by Dijkstra's algorithm; a vertex is final once popped."""
    dist, done = [None] * n, [False] * n
    dist[source], heap = 0, [(0, source)]
    while heap:
        d, u = heapq.heappop(heap)
        if done[u]:
            continue
        done[u] = True
        for v, w in adj[u]:
            if not done[v] and (dist[v] is None or d + w < dist[v]):
                dist[v] = d + w
                heapq.heappush(heap, (dist[v], v))
    return dist


def bellman_ford(n, adj, source=0):
    """Distances by Bellman-Ford (correct with negative weights, no negative cycles)."""
    dist = [None] * n
    dist[source] = 0
    for _ in range(n - 1):
        for u in range(n):
            if dist[u] is None:
                continue
            for v, w in adj[u]:
                if dist[v] is None or dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
    return dist


def random_dag(n, rng, low, high):
    """Random DAG on 0..n-1 (edges i -> j for i < j), weights in [low, high]."""
    adj = [[] for _ in range(n)]
    for i, j in itertools.combinations(range(n), 2):
        if rng.random() < 0.5:
            adj[i].append((j, rng.randint(low, high)))
    return adj


def greedy_coins(coins, amount):
    """Number of coins used by the greedy method (coins include 1)."""
    count = 0
    for c in sorted(coins, reverse=True):
        count += amount // c
        amount %= c
    return count


def optimal_coins(coins, limit):
    """Fewest coins for every amount 0..limit, by dynamic programming."""
    best = [0] + [None] * limit
    for x in range(1, limit + 1):
        best[x] = 1 + min(best[x - c] for c in coins if c <= x)
    return best


def first_greedy_failure(coins):
    """Smallest amount below a + b (the two largest coins) where greedy is worse."""
    a, b = sorted(coins)[-2:]
    best = optimal_coins(coins, a + b)
    for x in range(a + b):
        if greedy_coins(coins, x) > best[x]:
            return x
    return None


def main():
    rng = random.Random(7)
    agree = 0
    for _ in range(300):
        edges = [(rng.randint(1, 9), u, v)
                 for u, v in itertools.combinations(range(5), 2)]
        agree += kruskal(5, edges) == brute_force_mst(5, edges)
    print(f"1. Kruskal = exhaustive minimum over spanning trees: {agree}/300")
    for low, label in [(0, "weights 0..9"), (-4, "weights -4..9")]:
        same = sum(dijkstra(6, g) == bellman_ford(6, g)
                   for g in (random_dag(6, rng, low, 9) for _ in range(300)))
        print(f"2. Dijkstra = Bellman-Ford, {label}: {same}/300 graphs")
    adj = [[(1, 1), (2, 2)], [], [(1, -2)]]
    print(f"   s->a (1), s->b (2), b->a (-2): Dijkstra gives d(a) ="
          f" {dijkstra(3, adj)[1]}, true d(a) = {bellman_ford(3, adj)[1]}")
    systems = [(1, a, b) for a in range(2, 12) for b in range(a + 1, 13)]
    fails = {s: first_greedy_failure(s) for s in systems}
    good = sum(1 for x in fails.values() if x is None)
    print(f"3. Coin systems {{1, a, b}}, b <= 12: greedy optimal for {good}"
          f" of {len(systems)}")
    print(f"   {{1, 3, 4}}: first failure at {fails[(1, 3, 4)]}"
          f" (greedy {greedy_coins((1, 3, 4), 6)} coins, best"
          f" {optimal_coins((1, 3, 4), 6)[6]})")
    print(f"   {{1, 5, 10}}: failures below 15: {fails[(1, 5, 10)]}")
    print()
    print("Epistemic status: parts 1 and 2 test random instances - evidence")
    print("that agrees with the correctness proofs of Kruskal (cut property)")
    print("and Dijkstra (non-negative weights), and counterexamples showing")
    print("the weight hypothesis is needed. Part 3 is an exhaustive check of")
    print("finitely many coin systems, conclusive only because of the")
    print("Kozen-Zaks bound.")


if __name__ == "__main__":
    main()
