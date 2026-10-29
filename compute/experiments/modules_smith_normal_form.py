"""Smith normal form over the integers: classifying abelian groups by matrices.

A finitely generated abelian group given by generators and relations is
Z^m / (column span of an integer relation matrix A). Row and column operations
over Z (invertible over Z) bring A to diagonal form diag(d1, d2, ...) with
d1 | d2 | ..., and then the group is Z/d1 + Z/d2 + ... + Z^(free rank).
This experiment implements the reduction, checks the divisibility chain and
the determinantal-divisor identity d1 d2 ... dk = gcd of k x k minors (which
proves the d_i do not depend on the choices made), and compares two ways of
counting abelian groups of order n: invariant-factor chains versus products
of partition numbers (elementary divisors). Exact integer arithmetic.
"""

from itertools import combinations
from math import gcd, prod
import random

EXPERIMENT = {
    "id": "modules_smith_normal_form",
    "title": "Smith normal form and the classification of abelian groups",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["modules"],
    "summary": (
        "Reduces integer relation matrices to Smith normal form, reads off the "
        "abelian group they present, checks the divisibility chain and the "
        "determinantal-divisor identity on every 2 x 2 matrix with entries in "
        "[-3, 3] and on 300 random 3 x 3 matrices, and counts abelian groups "
        "of order n <= 100 in two independent ways. Exact arithmetic; the "
        "lesson proves the structure theorem for every PID."
    ),
    "packages": [],
}


def smith_diagonal(matrix):
    """Invariant factors d1 | d2 | ... (with zeros last) of an integer matrix."""
    a = [list(row) for row in matrix]
    m, n = len(a), len(a[0]) if a else 0
    diag = []
    for t in range(min(m, n)):
        entries = [(abs(a[i][j]), i, j) for i in range(t, m)
                   for j in range(t, n) if a[i][j]]
        if not entries:
            break
        while True:
            _, i, j = min(entries)
            a[t], a[i] = a[i], a[t]
            for row in a:
                row[t], row[j] = row[j], row[t]
            done = True
            for i in range(t + 1, m):           # clear column t
                q = a[i][t] // a[t][t]
                a[i] = [x - q * y for x, y in zip(a[i], a[t])]
                done &= a[i][t] == 0
            for j in range(t + 1, n):           # clear row t
                q = a[t][j] // a[t][t]
                for row in a:
                    row[j] -= q * row[t]
                done &= a[t][j] == 0
            bad = [(i, j) for i in range(t + 1, m) for j in range(t + 1, n)
                   if a[i][j] % a[t][t]]
            if done and bad:                    # pivot must divide the rest
                i = bad[0][0]
                a[t] = [x + y for x, y in zip(a[t], a[i])]
                done = False
            if done:
                break
            entries = [(abs(a[i][j]), i, j) for i in range(t, m)
                       for j in range(t, n) if a[i][j]]
        diag.append(abs(a[t][t]))
    return diag + [0] * (min(m, n) - len(diag))


def cokernel(matrix):
    """(free rank, torsion orders > 1) of Z^m / column span of the matrix."""
    m = len(matrix)
    diag = smith_diagonal(matrix)
    nonzero = [d for d in diag if d]
    return m - len(nonzero), [d for d in nonzero if d > 1]


def det(mat):
    """Integer determinant by Laplace expansion (small matrices only)."""
    if len(mat) == 1:
        return mat[0][0]
    return sum((-1) ** j * mat[0][j] * det([r[:j] + r[j + 1:] for r in mat[1:]])
               for j in range(len(mat)))


def determinantal_divisor(matrix, k):
    """gcd of all k x k minors of the matrix."""
    rows, cols = range(len(matrix)), range(len(matrix[0]))
    g = 0
    for r in combinations(rows, k):
        for c in combinations(cols, k):
            g = gcd(g, det([[matrix[i][j] for j in c] for i in r]))
    return g


def chain_ok(diag):
    """d1 | d2 | ... among the non-zero entries, zeros only at the end."""
    nz = [d for d in diag if d]
    tail_zero = all(d == 0 for d in diag[len(nz):])
    return tail_zero and all(b % a == 0 for a, b in zip(nz, nz[1:]))


def identity_ok(matrix):
    """d1 ... dk equals the k-th determinantal divisor for every k."""
    diag = smith_diagonal(matrix)
    return all(prod(diag[:k]) == determinantal_divisor(matrix, k)
               for k in range(1, len(diag) + 1))


def partitions(n):
    """Number of partitions of n."""
    p = [1] + [0] * n
    for part in range(1, n + 1):
        for total in range(part, n + 1):
            p[total] += p[total - part]
    return p[n]


def groups_by_elementary_divisors(n):
    """Abelian groups of order n: product of p(e) over prime powers p^e || n."""
    count, q = 1, 2
    while n > 1:
        e = 0
        while n % q == 0:
            n, e = n // q, e + 1
        count *= partitions(e)
        q += 1
    return count


def groups_by_invariant_factors(n, prev=1):
    """Chains d1 | d2 | ... | dk with d1 >= 2, prev | d1 and product n."""
    if n == 1:
        return 1
    return sum(groups_by_invariant_factors(n // d, d) for d in range(2, n + 1)
               if n % d == 0 and d % prev == 0)


def main():
    examples = [("Z^2 / <(2,0), (0,3)>", [[2, 0], [0, 3]]),
                ("Z^2 / <(4,6), (6,4)>", [[4, 6], [6, 4]]),
                ("Z^3 / <(2,4,6), (4,8,12)>", [[2, 4], [4, 8], [6, 12]]),
                ("Z^3 / <(1,1,1), (0,2,4), (0,0,6)>",
                 [[1, 0, 0], [1, 2, 0], [1, 4, 6]])]
    print("Presented abelian groups (relations are the columns):")
    for name, mat in examples:
        free, tors = cokernel(mat)
        parts = [f"Z/{d}" for d in tors] + ["Z"] * free
        print(f"  {name:34} = {' + '.join(parts) or '0'}")
    small = [[[a, b], [c, d]] for a in range(-3, 4) for b in range(-3, 4)
             for c in range(-3, 4) for d in range(-3, 4)]
    ok2 = sum(chain_ok(smith_diagonal(m)) and identity_ok(m) for m in small)
    rng = random.Random(2024)
    big = [[[rng.randint(-9, 9) for _ in range(3)] for _ in range(3)]
           for _ in range(300)]
    ok3 = sum(chain_ok(smith_diagonal(m)) and identity_ok(m) for m in big)
    print("Divisibility chain and minor identity d1...dk = gcd of k x k minors:")
    print(f"  all {len(small)} 2x2 matrices, entries in [-3, 3]: hold for {ok2}")
    print(f"  300 random 3x3 matrices, entries in [-9, 9]: hold for {ok3}")
    agree = all(groups_by_elementary_divisors(n) == groups_by_invariant_factors(n)
                for n in range(1, 101))
    print("Abelian groups of order n, two ways, agree for n <= 100:", agree)
    print("  n = 8, 16, 72, 64:", [groups_by_elementary_divisors(n)
                                  for n in (8, 16, 72, 64)])
    print()
    print("Epistemic status: exact integer arithmetic, exhaustive over the "
          "finite range\nstated and seeded-random elsewhere. The minor identity "
          "shows that the d_i\ndepend only on the matrix, not on the "
          "operations chosen. Finite checks are\nevidence; the structure "
          "theorem is proved in the lesson for every PID.")


if __name__ == "__main__":
    main()
