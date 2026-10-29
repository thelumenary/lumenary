"""Counting paths: when is a path algebra finite-dimensional?

The path algebra kQ has a basis of all paths, including one trivial path at
each vertex. If A is the adjacency matrix of Q (A[i][j] = number of arrows
i -> j), the number of paths of length k from i to j is the (i, j) entry of
A^k, so dim kQ = sum over k of the entries of A^k. This is finite exactly when
A is nilpotent, that is, when Q has no oriented cycles; then the Cartan
matrix C = I + A + A^2 + ... = (I - A)^(-1) records dim e_i kQ e_j, the number
of paths from i to j. We compute these for several quivers, and the growth of
the number of paths when there are cycles. Exact integer arithmetic.
"""

EXPERIMENT = {
    "id": "path_algebras_path_counting",
    "title": "Counting paths: dimensions of path algebras",
    "evidence": ["exact"],
    "lessons": ["path-algebras"],
    "summary": (
        "Counts paths in quivers with powers of the adjacency matrix: the "
        "dimension of the path algebra for linear A_n (n(n+1)/2), other "
        "orientations, D_4 and the Kronecker quiver, the Cartan matrix of "
        "path counts, and the growth of path counts for the one-loop and "
        "two-loop quivers, where the path algebra is k[x] or a free algebra. "
        "Exact counts for these quivers."
    ),
    "packages": [],
}


def matmul(a, b):
    """Product of square integer matrices."""
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def identity(n):
    """The n x n identity matrix."""
    return [[int(i == j) for j in range(n)] for i in range(n)]


def adjacency(n, arrows):
    """Adjacency matrix from a list of arrows (i, j), vertices 0..n-1."""
    a = [[0] * n for _ in range(n)]
    for i, j in arrows:
        a[i][j] += 1
    return a


def paths_by_length(a, max_len):
    """Total number of paths of each length 0..max_len."""
    counts, power = [], identity(len(a))
    for _ in range(max_len + 1):
        counts.append(sum(map(sum, power)))
        power = matmul(power, a)
    return counts


def is_acyclic(a):
    """Q has no oriented cycle iff A^n = 0, n = number of vertices."""
    power = identity(len(a))
    for _ in range(len(a)):
        power = matmul(power, a)
    return all(v == 0 for row in power for v in row)


def cartan(a):
    """C = I + A + A^2 + ... for acyclic Q: C[i][j] = paths from i to j."""
    n = len(a)
    total, power = identity(n), identity(n)
    for _ in range(n):
        power = matmul(power, a)
        total = [[x + y for x, y in zip(r, s)] for r, s in zip(total, power)]
    return total


QUIVERS = {
    "A_4 linear 0->1->2->3": (4, [(0, 1), (1, 2), (2, 3)]),
    "A_4 zigzag 0->1<-2->3": (4, [(0, 1), (2, 1), (2, 3)]),
    "D_4, arms into centre": (4, [(1, 0), (2, 0), (3, 0)]),
    "Kronecker 0 => 1": (2, [(0, 1), (0, 1)]),
    "A_3 cyclic 0->1->2->0": (3, [(0, 1), (1, 2), (2, 0)]),
    "one loop (Jordan)": (1, [(0, 0)]),
    "two loops": (1, [(0, 0), (0, 0)]),
}


def main():
    print("Quiver                     acyclic  dim kQ   paths of length 0..6")
    for name, (n, arrows) in QUIVERS.items():
        a = adjacency(n, arrows)
        counts = paths_by_length(a, 6)
        dim = sum(map(sum, cartan(a))) if is_acyclic(a) else "inf"
        print(f"{name:26} {str(is_acyclic(a)):7}  {str(dim):6}   {counts}")
    lin = [sum(map(sum, cartan(adjacency(n, [(i, i + 1) for i in range(n - 1)]))))
           for n in range(1, 9)]
    print("dim kA_n, linear A_n, n = 1..8:", lin)
    print("  equal to n(n+1)/2:", lin == [n * (n + 1) // 2 for n in range(1, 9)])
    print("Cartan matrix of linear A_4 (row i: paths from i to j):")
    for row in cartan(adjacency(4, QUIVERS["A_4 linear 0->1->2->3"][1])):
        print("  ", row)
    print()
    print("Epistemic status: exact counts for the listed quivers and lengths. "
          "That dim kQ\nis finite exactly for acyclic finite quivers is proved "
          "in the lesson (and its\ntwo halves in Lean); the growth figures for "
          "cyclic quivers are illustrations.")


if __name__ == "__main__":
    main()
