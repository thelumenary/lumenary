"""Gaussian elimination in exact arithmetic, and rank-nullity on many matrices.

The experiment row-reduces matrices with Python fractions, so every step is
exact: no rounding errors can create or destroy a pivot. It reduces the worked
example of the lesson, reads off a basis of the null space from the free
columns, and then checks rank + nullity = number of columns on a few hundred
random integer matrices whose rank is known in advance (they are built as a
product of an m x r and an r x n matrix). This is exact computation on finitely
many cases: evidence for the theorem, not a proof of it.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "linear_algebra_rank_nullity",
    "title": "Exact Gaussian elimination and rank-nullity",
    "evidence": ["exact", "experimental"],
    "lessons": ["linear-algebra"],
    "summary": (
        "Row-reduces matrices with exact fractions, reads off pivots, rank and a "
        "basis of the null space, and checks that every basis vector solves Ax = 0 "
        "and that rank + nullity = n. Run on the lesson's worked example and on "
        "300 random integer matrices of prescribed rank: exact arithmetic, but "
        "only finitely many cases."
    ),
    "packages": [],
}


def rref(matrix):
    """Return (R, pivots): the reduced row echelon form and pivot columns."""
    rows = [[Fraction(x) for x in row] for row in matrix]
    m = len(rows)
    n = len(rows[0]) if m else 0
    pivots = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        lead = rows[r][c]
        rows[r] = [x / lead for x in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                factor = rows[i][c]
                rows[i] = [a - factor * b for a, b in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
        if r == m:
            break
    return rows, pivots


def rank(matrix):
    """The number of pivots in the reduced row echelon form."""
    return len(rref(matrix)[1])


def null_space(matrix):
    """A basis of {x : Ax = 0}, one vector per free column."""
    reduced, pivots = rref(matrix)
    n = len(matrix[0])
    basis = []
    for free in (c for c in range(n) if c not in pivots):
        v = [Fraction(0)] * n
        v[free] = Fraction(1)
        for row, p in zip(reduced, pivots):
            v[p] = -row[free]
        basis.append(v)
    return basis


def mat_vec(matrix, v):
    """The product A v."""
    return [sum(Fraction(a) * x for a, x in zip(row, v)) for row in matrix]


def mat_mul(a, b):
    """The product of two matrices given as lists of rows."""
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)]
            for row in a]


def random_matrix_of_rank(rng, m, n, r):
    """An m x n integer matrix (B C with B m x r, C r x n); rank <= r."""
    b = [[rng.randint(-4, 4) for _ in range(r)] for _ in range(m)]
    c = [[rng.randint(-4, 4) for _ in range(n)] for _ in range(r)]
    return mat_mul(b, c)


def check_rank_nullity(matrix):
    """True if rank + nullity = n and every null vector solves Ax = 0."""
    basis = null_space(matrix)
    solves = all(all(x == 0 for x in mat_vec(matrix, v)) for v in basis)
    return solves and rank(matrix) + len(basis) == len(matrix[0])


def fmt(v):
    """Format a vector of fractions compactly."""
    return "(" + ", ".join(str(x) for x in v) + ")"


def main():
    a = [[1, 2, 1], [2, 4, 3]]
    augmented = [[1, 2, 1, 4], [2, 4, 3, 9]]
    reduced, pivots = rref(augmented)
    print("Worked example: x + 2y + z = 4, 2x + 4y + 3z = 9")
    print("RREF of the augmented matrix [A | b]:")
    for row in reduced:
        print(f"   {fmt(row)}")
    print(f"pivot columns {pivots}: x and z are pivots, y is free")
    print(f"rank of A = {rank(a)}, nullity = {len(null_space(a))}, n = 3")
    print("null space basis:", ", ".join(fmt(v) for v in null_space(a)))
    print("so the solutions form the line (3, 0, 1) + t(-2, 1, 0).")
    print()
    rng = random.Random(2024)
    trials, ok, exact_rank = 0, 0, 0
    deficit = {}
    for _ in range(300):
        m, n = rng.randint(2, 6), rng.randint(2, 7)
        r = rng.randint(1, min(m, n))
        mat = random_matrix_of_rank(rng, m, n, r)
        trials += 1
        ok += check_rank_nullity(mat)
        k = rank(mat)
        exact_rank += k == r
        deficit[r - k] = deficit.get(r - k, 0) + 1
    print(f"Random integer matrices B*C of rank at most r: {trials}")
    print(f"  rank + nullity = n and A v = 0 checked: {ok} of {trials}")
    print(f"  rank came out exactly r: {exact_rank} of {trials}")
    print(f"  rank deficit r - rank -> count: {dict(sorted(deficit.items()))}")
    print("A random product usually has full rank r; a deficit happens when")
    print("the small random factors are accidentally dependent.")
    print()
    print("Epistemic status: exact rational arithmetic, so each case is a")
    print("genuine check with no rounding; but 300 matrices are finitely many")
    print("examples. Rank-nullity itself is proved in the lesson and in Lean.")


if __name__ == "__main__":
    main()
