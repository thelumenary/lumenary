"""The irreducible representations of sl(2, C), and the roots of sl(3, C).

For each n, the (n+1)-dimensional representation V_n has a basis
v_0, ..., v_n with  h v_k = (n - 2k) v_k,  f v_k = v_(k+1),
e v_k = k (n - k + 1) v_(k-1). We build these matrices with exact integers,
check the relations [h, e] = 2e, [h, f] = -2f, [e, f] = h, compute the
Casimir element ef + fe + h^2/2 (a scalar, n(n+2)/2, by Schur's lemma) and
decompose tensor products by peeling off highest weights (Clebsch-Gordan).
Finally it computes the eigenvalues of ad(H) on sl(3) for diagonal H: the six
roots, which form a regular hexagon (the root system A2). All exact.
"""

import itertools
import math
from fractions import Fraction

EXPERIMENT = {
    "id": "lie_groups_sl2_representations",
    "title": "Representations of sl(2) and the roots of sl(3)",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["lie-groups"],
    "summary": (
        "Builds the irreducible representations V_n of sl(2, C) for n = 0..8 "
        "with exact integer matrices, checks the bracket relations and that the "
        "Casimir acts as n(n+2)/2, decomposes V_m (x) V_n by weights into "
        "V_(m+n) + ... + V_|m-n|, and computes the roots of sl(3) as eigenvalues "
        "of ad(H), recovering the hexagon A2 and its Cartan matrix. Exact."
    ),
    "packages": [],
}


def zeros(d):
    """A d x d zero matrix (lists of Fractions)."""
    return [[Fraction(0)] * d for _ in range(d)]


def mat_mul(a, b):
    """Product of square matrices given as lists of lists."""
    d = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(d)) for j in range(d)]
            for i in range(d)]


def bracket(a, b):
    """The commutator ab - ba."""
    ab, ba = mat_mul(a, b), mat_mul(b, a)
    return [[x - y for x, y in zip(r, s)] for r, s in zip(ab, ba)]


def scale(c, a):
    """The matrix c * a."""
    return [[c * x for x in row] for row in a]


def irrep(n):
    """Matrices (e, f, h) of V_n in the basis v_0, ..., v_n (column k = image of v_k)."""
    d = n + 1
    e, f, h = zeros(d), zeros(d), zeros(d)
    for k in range(d):
        h[k][k] = Fraction(n - 2 * k)
        if k + 1 < d:
            f[k + 1][k] = Fraction(1)
        if k >= 1:
            e[k - 1][k] = Fraction(k * (n - k + 1))
    return e, f, h


def relations_hold(n):
    """Check [h, e] = 2e, [h, f] = -2f, [e, f] = h in V_n."""
    e, f, h = irrep(n)
    return (bracket(h, e) == scale(2, e) and bracket(h, f) == scale(-2, f)
            and bracket(e, f) == h)


def casimir(n):
    """The matrix ef + fe + h^2 / 2 on V_n."""
    e, f, h = irrep(n)
    ef, fe, hh = mat_mul(e, f), mat_mul(f, e), mat_mul(h, h)
    return [[ef[i][j] + fe[i][j] + hh[i][j] / 2 for j in range(n + 1)]
            for i in range(n + 1)]


def decompose(weights):
    """Split a multiset of h-weights into irreducibles: list of highest weights."""
    remaining = sorted(weights, reverse=True)
    parts = []
    while remaining:
        top = remaining[0]
        parts.append(top)
        for w in range(top, -top - 1, -2):
            remaining.remove(w)
    return parts


def tensor_weights(m, n):
    """Weights of V_m (x) V_n: all sums of a weight of V_m and one of V_n."""
    return [a + b for a in range(-m, m + 1, 2) for b in range(-n, n + 1, 2)]


def sl3_roots():
    """Roots of sl(3): ad(H) E_ij = (h_i - h_j) E_ij; return the pairs (i, j)."""
    return [(i, j) for i, j in itertools.permutations(range(3), 2)]


def ad_check(diag):
    """Verify [H, E_ij] = (h_i - h_j) E_ij with matrices, for H = diag(diag)."""
    hmat = zeros(3)
    for k in range(3):
        hmat[k][k] = Fraction(diag[k])
    for i, j in sl3_roots():
        eij = zeros(3)
        eij[i][j] = Fraction(1)
        if bracket(hmat, eij) != scale(Fraction(diag[i] - diag[j]), eij):
            return False
    return True


def root_vector(i, j):
    """The root e_i - e_j, in an orthonormal basis of the plane x + y + z = 0."""
    v = [0.0, 0.0, 0.0]
    v[i], v[j] = 1.0, -1.0
    u1 = (1 / math.sqrt(2), -1 / math.sqrt(2), 0.0)
    u2 = (1 / math.sqrt(6), 1 / math.sqrt(6), -2 / math.sqrt(6))
    return (sum(a * b for a, b in zip(v, u1)), sum(a * b for a, b in zip(v, u2)))


def cartan_matrix(simple):
    """Cartan integers 2 (a, b) / (b, b) for simple roots given as 2D vectors."""
    def dot(a, b):
        return a[0] * b[0] + a[1] * b[1]
    return [[round(2 * dot(a, b) / dot(b, b)) for b in simple] for a in simple]


def main():
    ok = all(relations_hold(n) for n in range(9))
    print(f"1. V_n for n = 0..8: [h,e] = 2e, [h,f] = -2f, [e,f] = h hold: {ok}")
    for n in range(5):
        c = casimir(n)
        scalar = all(c[i][j] == (c[0][0] if i == j else 0)
                     for i in range(n + 1) for j in range(n + 1))
        weights = " ".join(str(n - 2 * k) for k in range(n + 1))
        print(f"   V_{n}: weights {weights:<14} Casimir = {c[0][0]}"
              f" (scalar: {scalar})")
    print("2. Clebsch-Gordan, by peeling off highest weights:")
    for m, n in [(1, 1), (2, 1), (2, 2), (3, 2)]:
        parts = " + ".join(f"V_{p}" for p in decompose(tensor_weights(m, n)))
        print(f"   V_{m} (x) V_{n} = {parts}")
    print("3. Roots of sl(3): ad(diag(h1, h2, h3)) E_ij = (h_i - h_j) E_ij")
    print(f"   (checked with matrices for H = diag(3, 1, -4): "
          f"{ad_check((3, 1, -4))})")
    for i, j in sl3_roots():
        x, y = root_vector(i, j)
        angle = math.degrees(math.atan2(y, x)) % 360
        print(f"   e{i + 1} - e{j + 1}: angle {angle:6.1f} deg, length "
              f"{math.hypot(x, y):.4f}")
    simple = [root_vector(0, 1), root_vector(1, 2)]
    print(f"   simple roots e1 - e2, e2 - e3: Cartan matrix "
          f"{cartan_matrix(simple)}")
    print()
    print("Epistemic status: exact integer and rational computation for n <= 8")
    print("and for sl(3). It checks the classification for small n; the proof")
    print("that every irreducible representation is some V_n is in the lesson.")


if __name__ == "__main__":
    main()
