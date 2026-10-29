"""Maschke's theorem and its failure when the characteristic divides |G|.

Over F_p, the shear J = [[1, 1], [0, 1]] has order p, so g -> J^g is a
representation of the cyclic group of order p on F_p^2. We list all p + 1
lines of F_p^2 and find the invariant ones: there is exactly one, so it has
no invariant complement and the representation is not completely reducible.
For contrast, the swap S = [[0, 1], [1, 0]] (a representation of the group of
order 2) has two complementary invariant lines when p is odd but only one
when p = 2. Finally we run Maschke's averaging on a projection: for p odd,
(pi + S pi S) / 2 is an equivariant projection; for p = 2 the division by
|G| = 2 is impossible, and the sum pi + S pi S is not a projection.
"""

EXPERIMENT = {
    "id": "representation_theory_maschke_char_p",
    "title": "Maschke's theorem fails in characteristic p",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["representation-theory"],
    "summary": (
        "Lists all lines of F_p^2 for p = 2, 3, 5, 7 and finds those invariant "
        "under the shear (order p) and under the swap (order 2): the shear has "
        "a single invariant line, so Maschke fails exactly when p divides the "
        "group order. It also runs the averaging argument of Maschke's proof, "
        "which works for p odd and breaks for p = 2. Exhaustive and exact."
    ),
    "packages": [],
}


def lines(p):
    """One spanning vector for each of the p + 1 lines of F_p^2."""
    return [(1, a) for a in range(p)] + [(0, 1)]


def apply(m, v, p):
    """Matrix times vector mod p."""
    return ((m[0][0] * v[0] + m[0][1] * v[1]) % p,
            (m[1][0] * v[0] + m[1][1] * v[1]) % p)


def on_line(w, v, p):
    """Is w a multiple of v mod p?"""
    return (w[0] * v[1] - w[1] * v[0]) % p == 0


def invariant_lines(m, p):
    """Lines of F_p^2 mapped into themselves by m."""
    return [v for v in lines(p) if on_line(apply(m, v, p), v, p)]


def matmul(a, b, p):
    """2 x 2 matrix product mod p."""
    return [[sum(a[i][k] * b[k][j] for k in range(2)) % p for j in range(2)]
            for i in range(2)]


def order(m, p):
    """Multiplicative order of an invertible 2 x 2 matrix mod p."""
    k, x = 1, m
    while x != [[1, 0], [0, 1]]:
        x, k = matmul(x, m, p), k + 1
    return k


SHEAR = [[1, 1], [0, 1]]
SWAP = [[0, 1], [1, 0]]
# projection onto the line spanned by (1, 1) along the line spanned by (1, 0)
PI = [[0, 1], [0, 1]]


def averaged(p):
    """sum over G = {1, S} of g pi g^-1, divided by |G| = 2 if possible."""
    total = [[(PI[i][j] + matmul(matmul(SWAP, PI, p), SWAP, p)[i][j]) % p
              for j in range(2)] for i in range(2)]
    if p == 2:
        return total
    half = pow(2, p - 2, p)
    return [[x * half % p for x in row] for row in total]


def main():
    print(" p  order of shear  invariant lines (shear)  invariant lines (swap)")
    for p in (2, 3, 5, 7):
        print(f"{p:2}  {order(SHEAR, p):14}  {str(invariant_lines(SHEAR, p)):23}"
              f"  {invariant_lines(SWAP, p)}")
    for p in (3, 5, 2):
        e = averaged(p)
        proj = matmul(e, e, p) == e
        equiv = matmul(e, SWAP, p) == matmul(SWAP, e, p)
        label = "(pi + S pi S)/2" if p != 2 else "pi + S pi S (no 1/2)"
        print(f"p = {p}: {label} = {e}")
        print(f"  idempotent: {proj}; commutes with S: {equiv}")
    print()
    print("Epistemic status: exhaustive over all lines of F_p^2 for the four "
          "primes shown,\nwith exact modular arithmetic: genuine "
          "counterexamples to complete reducibility\nwhen p divides |G|. "
          "Maschke's theorem itself is proved in the lesson.")


if __name__ == "__main__":
    main()
