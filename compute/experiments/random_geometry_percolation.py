"""Phase transitions: bond percolation on a grid and the giant component.

Part 1. Bond percolation on a square grid: each edge is open with
probability p. We estimate by simulation the probability that open edges
connect the left side of an (L + 1) x L rectangle to its right side. As L
grows the curve sharpens into a step at p = 1/2, Kesten's critical value;
at p = 1/2 the crossing probability is exactly 1/2 for every L, because the
rectangle is chosen to be self-dual.

Part 2. The Erdos-Renyi random graph with n vertices and m = c n / 2 random
edges (asymptotically the same as G(n, c/n)). The largest component has a
vanishing fraction of the vertices when c < 1 and a fraction close to the
positive root beta of beta = 1 - exp(-c beta) when c > 1.

Evidence: statistical (Monte Carlo with a fixed seed, small sizes and few
trials, with approximate standard errors). Simulations near a critical
point estimate behaviour; the exact critical values are theorems.
"""

import math
import random

EXPERIMENT = {
    "id": "random_geometry_percolation",
    "title": "Percolation crossings and the Erdos-Renyi giant component",
    "evidence": ["statistical", "experimental"],
    "lessons": ["random-geometry"],
    "summary": (
        "Monte Carlo estimates of left-right crossing probabilities for bond "
        "percolation on self-dual (L+1) x L rectangles (L = 8, 24) for p from "
        "0.35 to 0.65, which sharpen around Kesten's p_c = 1/2, and of the "
        "largest component of "
        "random graphs with n = 2000 vertices and average degree c, compared "
        "with the branching-process prediction beta = 1 - exp(-c beta). "
        "Statistical evidence from small samples, not proof."
    ),
    "packages": [],
}


def find(parent, x):
    """Root of x in a union-find forest, with path halving."""
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def union(parent, size, a, b):
    """Merge the components of a and b (union by size)."""
    ra, rb = find(parent, a), find(parent, b)
    if ra == rb:
        return
    if size[ra] < size[rb]:
        ra, rb = rb, ra
    parent[rb] = ra
    size[ra] += size[rb]


def crosses(n, p, rng):
    """Is there an open left-right crossing of the self-dual rectangle R_n?

    R_n has n interior columns x = 1..n and n + 1 rows y = 0..n. Each row
    has n + 1 horizontal edges, from the left side (x = 0) through the
    interior to the right side (x = n + 1), and each interior column has n
    vertical edges. Its planar dual is a rotated copy of R_n, so at p = 1/2
    a crossing occurs with probability exactly 1/2.
    """
    count = n * (n + 1) + 2
    parent, size = list(range(count)), [1] * count
    left, right = count - 2, count - 1

    def node(x, y):
        return y * n + (x - 1)

    for y in range(n + 1):
        if rng.random() < p:
            union(parent, size, left, node(1, y))
        if rng.random() < p:
            union(parent, size, node(n, y), right)
        for x in range(1, n):
            if rng.random() < p:
                union(parent, size, node(x, y), node(x + 1, y))
    for x in range(1, n + 1):
        for y in range(n):
            if rng.random() < p:
                union(parent, size, node(x, y), node(x, y + 1))
    return find(parent, left) == find(parent, right)


def crossing_probability(n, p, trials, rng):
    """Fraction of trials with an open left-right crossing."""
    return sum(crosses(n, p, rng) for _ in range(trials)) / trials


def largest_component_fraction(n, c, rng):
    """Largest component of a random graph with n vertices and c n / 2 edges."""
    parent, size = list(range(n)), [1] * n
    for _ in range(round(c * n / 2)):
        a, b = rng.randrange(n), rng.randrange(n)
        if a != b:
            union(parent, size, a, b)
    return max(size[find(parent, v)] for v in range(n)) / n


def giant_fraction(c, iterations=200):
    """Largest root of beta = 1 - exp(-c beta) in [0, 1].

    For c <= 1 the only root is 0 (proved in the lesson's Lean file); for
    c > 1 iterating beta -> 1 - exp(-c beta) from beta = 1 converges to the
    positive root.
    """
    if c <= 1:
        return 0.0
    beta = 1.0
    for _ in range(iterations):
        beta = 1 - math.exp(-c * beta)
    return beta


def main():
    rng = random.Random(1957)
    ps = [0.35, 0.45, 0.5, 0.55, 0.65]
    trials = 200
    print(f"Part 1: P(left-right open crossing), {trials} trials per entry")
    print("  p    " + "".join(f"{p:>8}" for p in ps))
    for n in [8, 24]:
        est = [crossing_probability(n, p, trials, rng) for p in ps]
        print(f"  L = {n:<3}" + "".join(f"{e:>8.2f}" for e in est))
    print(f"  (standard error of each entry at most about "
          f"{0.5 / math.sqrt(trials):.2f})")
    print()
    n, reps = 2000, 5
    print(f"Part 2: random graph, n = {n} vertices, average degree c "
          f"({reps} samples)")
    print(f"  {'c':>4}{'largest component / n':>24}{'beta(c) theory':>17}")
    for c in [0.5, 0.9, 1.5, 2.0, 3.0]:
        sim = sum(largest_component_fraction(n, c, rng)
                  for _ in range(reps)) / reps
        print(f"  {c:>4}{sim:>24.3f}{giant_fraction(c):>17.3f}")
    print("  (for c < 1 the largest component has O(log n) vertices,")
    print("  so its fraction tends to 0 only slowly as n grows)")
    print()
    print("Epistemic status: Monte Carlo estimates from a few hundred random")
    print("samples on small systems (statistical evidence). They are")
    print("consistent with Kesten's theorem p_c = 1/2 and the Erdos-Renyi")
    print("theorem, but cannot determine critical values or exponents exactly.")


if __name__ == "__main__":
    main()
