"""Recovering the interval decomposition of a representation of linear A_n.

A representation of 1 -> 2 -> ... -> n over F_p is a list of matrices. The
lesson proves it is a direct sum of interval modules [a, b] (k at vertices
a..b, identity maps inside), and that the multiplicity of [i, j] is
    m(i, j) = r(i, j) - r(i-1, j) - r(i, j+1) + r(i-1, j+1),
where r(i, j) is the rank of the composite map V_i -> V_j (and r = 0 when
i = 0 or j = n + 1). We build random representations as sums of known
intervals, hide the decomposition by random changes of basis at each vertex,
and recover the multiplicities from ranks alone. Exact arithmetic mod p,
seeded random examples.
"""

import random

EXPERIMENT = {
    "id": "path_algebras_barcodes",
    "title": "Recovering interval decompositions of linear A_n",
    "evidence": ["exact", "experimental"],
    "lessons": ["path-algebras"],
    "summary": (
        "Builds 200 seeded random representations of the linear quiver A_5 "
        "over F_7 as sums of interval modules, disguises them by random "
        "changes of basis, and recovers every multiplicity from ranks of "
        "composite maps by inclusion-exclusion. Exact modular arithmetic; "
        "evidence for these examples, while the lesson proves the "
        "classification and the rank formula in general."
    ),
    "packages": [],
}

P = 7


def matmul(a, b, p=P):
    """Matrix product mod p (a is m x k, b is k x n, lists of rows)."""
    if not a or not b or not b[0]:
        return [[0] * (len(b[0]) if b else 0) for _ in a]
    return [[sum(x * y for x, y in zip(row, col)) % p for col in zip(*b)]
            for row in a]


def rank(mat, p=P):
    """Rank mod p by row reduction."""
    rows = [[v % p for v in r] for r in mat]
    r = 0
    for c in range(len(rows[0]) if rows else 0):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [v * inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                k = rows[i][c]
                rows[i] = [(x - k * y) % p for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def inverse(mat, p=P):
    """Inverse of an invertible square matrix mod p (Gauss-Jordan)."""
    n = len(mat)
    aug = [[v % p for v in row] + [int(i == j) for j in range(n)]
           for i, row in enumerate(mat)]
    for c in range(n):
        piv = next(i for i in range(c, n) if aug[i][c])
        aug[c], aug[piv] = aug[piv], aug[c]
        inv = pow(aug[c][c], p - 2, p)
        aug[c] = [v * inv % p for v in aug[c]]
        for i in range(n):
            if i != c and aug[i][c]:
                k = aug[i][c]
                aug[i] = [(x - k * y) % p for x, y in zip(aug[i], aug[c])]
    return [row[n:] for row in aug]


def random_invertible(n, rng, p=P):
    """A random invertible n x n matrix mod p."""
    while True:
        m = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
        if rank(m, p) == n:
            return m


def interval_sum(n, intervals):
    """Dimensions and maps (V_k -> V_(k+1), rows = target) of a sum of
    interval modules [a, b], vertices 1..n."""
    dims = [sum(1 for a, b in intervals if a <= k <= b) for k in range(1, n + 1)]
    maps = []
    for k in range(1, n):
        src = [t for t, (a, b) in enumerate(intervals) if a <= k <= b]
        dst = [t for t, (a, b) in enumerate(intervals) if a <= k + 1 <= b]
        maps.append([[int(s == d) for s in src] for d in dst])
    return dims, maps


def disguise(dims, maps, rng):
    """Change basis at every vertex: f_k -> g_(k+1) f_k g_k^(-1)."""
    g = [random_invertible(d, rng) for d in dims]
    return [matmul(matmul(g[k + 1], f), inverse(g[k]))
            for k, f in enumerate(maps)]


def composite_rank(dims, maps, i, j):
    """Rank of V_i -> V_j (1 <= i <= j <= n); 0 outside that range."""
    n = len(dims)
    if i < 1 or j > n:
        return 0
    if dims[i - 1] == 0:
        return 0
    m = [[int(r == c) for c in range(dims[i - 1])] for r in range(dims[i - 1])]
    for k in range(i, j):
        if dims[k] == 0:
            return 0
        m = matmul(maps[k - 1], m)
    return rank(m)


def multiplicities(dims, maps):
    """{(i, j): m(i, j)} from ranks by inclusion-exclusion."""
    n = len(dims)

    def r(i, j):
        return composite_rank(dims, maps, i, j)

    return {(i, j): r(i, j) - r(i - 1, j) - r(i, j + 1) + r(i - 1, j + 1)
            for i in range(1, n + 1) for j in range(i, n + 1)}


def main():
    rng = random.Random(1972)
    n, trials, recovered = 5, 200, 0
    example = None
    for _ in range(trials):
        intervals = sorted((a, b) for a, b in
                           (sorted(rng.choices(range(1, n + 1), k=2))
                            for _ in range(rng.randint(1, 6))))
        dims, maps = interval_sum(n, intervals)
        hidden = disguise(dims, maps, rng)
        mult = multiplicities(dims, hidden)
        truth = {(i, j): intervals.count((i, j))
                 for i in range(1, n + 1) for j in range(i, n + 1)}
        recovered += mult == truth
        if example is None and len(intervals) >= 4:
            example = (intervals, dims, hidden, mult)
    intervals, dims, hidden, mult = example
    print(f"Linear A_{n} over F_{P}: {n * (n + 1) // 2} interval modules "
          "[a, b] are the indecomposables.")
    print(f"Hidden barcode {intervals}")
    print(f"  dimension vector {dims}; after random changes of basis the map")
    print(f"  V_1 -> V_2 is {hidden[0]}")
    found = sorted(k for k, v in mult.items() for _ in range(v))
    print(f"  recovered from ranks: {found}")
    print(f"Barcode recovered exactly in {recovered} of {trials} random trials")
    print()
    print("Epistemic status: exact arithmetic mod 7 on 200 seeded random "
          "examples; evidence\nthat the rank formula recovers the "
          "decomposition, not a proof. The lesson proves\nthe interval "
          "decomposition and the formula for every representation.")


if __name__ == "__main__":
    main()
