"""Intersection forms of 4-manifolds: rank, signature, parity, determinant.

The intersection form of a closed simply connected 4-manifold is a symmetric
unimodular integer matrix (determinant +-1). We compute, exactly:

* the determinant and the signature (by diagonalising the form by congruence
  over the rationals; Sylvester's law of inertia says the signs of the
  diagonal entries do not depend on how we do it);
* the parity (even if every diagonal entry is even, as for E8);

and apply three theorems that the computation itself cannot prove:
Freedman (1982): every unimodular form is the form of a closed simply
connected topological 4-manifold; Rokhlin (1952): if a smooth one has an even
form, the signature is divisible by 16; Donaldson (1983): if a smooth one has
a definite form, the form is diagonal (+-1's) after a change of basis.
We also compute |det| of linking matrices of framed links, which is the order
of H_1 of the 3-manifold obtained by integral surgery (infinite if det = 0).
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "low_dimensional_topology_intersection_forms",
    "title": "Intersection forms: E8, Rokhlin, Freedman and Donaldson",
    "evidence": ["exact"],
    "lessons": ["low-dimensional-topology"],
    "summary": (
        "Computes exactly the rank, determinant, signature (by rational "
        "diagonalisation) and parity of unimodular forms including E8, E8 + E8 "
        "and the K3 form, and reads off what the theorems of Freedman, Rokhlin "
        "and Donaldson say about topological and smooth 4-manifolds with these "
        "forms; also |det| of linking matrices, the order of H_1 after surgery. "
        "Exact linear algebra; the topology is cited."
    ),
    "packages": [],
}

E8_EDGES = [(0, 2), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]


def e8():
    """The E8 form (Cartan matrix, same labelling as Mathlib's CartanMatrix.E 8)."""
    m = [[2 if i == j else 0 for j in range(8)] for i in range(8)]
    for i, j in E8_EDGES:
        m[i][j] = m[j][i] = -1
    return m


def direct_sum(*blocks):
    """Block-diagonal sum of square integer matrices."""
    n = sum(len(b) for b in blocks)
    m = [[0] * n for _ in range(n)]
    k = 0
    for b in blocks:
        for i, row in enumerate(b):
            for j, v in enumerate(row):
                m[k + i][k + j] = v
        k += len(b)
    return m


def scale(m, c):
    """The matrix c * m."""
    return [[c * v for v in row] for row in m]


H = [[0, 1], [1, 0]]


def diagonalise(m):
    """Diagonal entries of a rational congruence diagonalisation P^T M P."""
    a = [[Fraction(v) for v in row] for row in m]
    n = len(a)
    diag = []
    for i in range(n):
        if a[i][i] == 0:
            j = next((j for j in range(i + 1, n) if a[j][j] != 0), None)
            if j is None:
                j = next((j for j in range(i + 1, n) if a[i][j] != 0), None)
                if j is not None:  # replace e_i by e_i + e_j
                    for k in range(n):
                        a[i][k] += a[j][k]
                    for k in range(n):
                        a[k][i] += a[k][j]
            else:
                a[i], a[j] = a[j], a[i]
                for row in a:
                    row[i], row[j] = row[j], row[i]
        p = a[i][i]
        diag.append(p)
        if p == 0:
            continue
        for r in range(i + 1, n):
            f = a[r][i] / p
            for k in range(n):
                a[r][k] -= f * a[i][k]
            for k in range(n):
                a[k][r] -= f * a[k][i]
    return diag


def invariants(m):
    """(rank, signature, determinant, even?) of a symmetric integer matrix."""
    d = diagonalise(m)
    det = Fraction(1)
    for v in d:
        det *= v
    sig = sum(1 for v in d if v > 0) - sum(1 for v in d if v < 0)
    even = all(m[i][i] % 2 == 0 for i in range(len(m)))
    return len(m), sig, int(det), even


FORMS = [
    ("<1>        (CP^2)", [[1]]),
    ("<1>+<-1>   (CP^2 # -CP^2)", [[1, 0], [0, -1]]),
    ("H          (S^2 x S^2)", H),
    ("E8", e8()),
    ("E8+E8", direct_sum(e8(), e8())),
    ("2(-E8)+3H  (K3 surface)", direct_sum(scale(e8(), -1), scale(e8(), -1),
                                           H, H, H)),
]


def main():
    print("form                         rank  sign  det  parity  smooth?")
    for name, m in FORMS:
        rank, sig, det, even = invariants(m)
        definite = abs(sig) == rank
        if even and sig % 16:
            verdict = "no (Rokhlin)"
        elif even and definite:
            verdict = "no (Donaldson)"
        else:
            verdict = "yes"
        parity = "even" if even else "odd"
        print(f"{name:27s} {rank:5d} {sig:5d} {det:4d}  {parity:6s}  {verdict}")
    print("Freedman: each form above is realised by a topological manifold.")
    print()
    print("Integral surgery on a framed link: |H_1| = |det(linking matrix)|")
    links = [("0-surgery on the unknot", [[0]]),
             ("5-surgery on the unknot (L(5,1))", [[5]]),
             ("Hopf link, framings 2 and 3", [[2, 1], [1, 3]]),
             ("E8 plumbing, framings -2", scale(e8(), -1))]
    for name, m in links:
        det = invariants(m)[2]
        order = "infinite (S^1 x S^2)" if det == 0 else str(abs(det))
        print(f"  {name:34s} |H_1| = {order}")
    print("The last is the Poincare homology sphere: H_1 = 0, yet pi_1 has")
    print("order 120 (the binary icosahedral group).")
    print()
    print("Epistemic status: the ranks, signatures, determinants and parities")
    print("are exact rational computations. The 'smooth?' column applies the")
    print("theorems of Rokhlin and Donaldson, and the existence statement is")
    print("Freedman's theorem; none of these is proved by this program, and")
    print("'yes' only means these obstructions do not apply (each such form is")
    print("in fact realised by a smooth manifold, named in the first column).")


if __name__ == "__main__":
    main()
