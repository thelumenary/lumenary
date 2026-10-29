"""Fox colourings and the determinant of a knot.

From a planar diagram (PD) code we find the arcs of the diagram (edges joined
where they pass over a crossing) and the colouring equations: at a crossing
whose over-arc is x and whose under-arcs are y and z, 2x = y + z mod p. The
number of Fox p-colourings is p to the power of the dimension of the solution
space, found by Gaussian elimination mod p. The determinant of the knot is
the absolute value of any (n-1) x (n-1) minor of the colouring matrix,
computed with exact fractions. A knot has a non-constant p-colouring (p an
odd prime) exactly when p divides its determinant. Brute force over all
colourings checks the linear algebra on the smallest cases. Evidence: exact
computation for these diagrams.
"""

from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "knot_theory_fox_colourings",
    "title": "Fox colourings and knot determinants",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["knot-theory"],
    "summary": (
        "Builds the colouring equations 2x = y + z of six knot diagrams from "
        "their PD codes, counts Fox p-colourings for p = 3, 5, 7 by linear "
        "algebra mod p (cross-checked by brute force on small cases) and "
        "computes each determinant exactly. It shows tricolourability matches "
        "3 | det, and that 4_1 and 5_1 have the same counts although they are "
        "different knots. Exact, for these diagrams."
    ),
    "packages": [],
}

KNOTS = {
    "unknot (1 kink)": [(1, 2, 2, 1)],
    "3_1": [(1, 5, 2, 4), (3, 1, 4, 6), (5, 3, 6, 2)],
    "4_1": [(4, 2, 5, 1), (8, 6, 1, 5), (6, 3, 7, 4), (2, 7, 3, 8)],
    "5_1": [(1, 6, 2, 7), (3, 8, 4, 9), (5, 10, 6, 1), (7, 2, 8, 3),
            (9, 4, 10, 5)],
    "5_2": [(1, 4, 2, 5), (3, 8, 4, 9), (5, 10, 6, 1), (9, 6, 10, 7),
            (7, 2, 8, 3)],
    "6_1": [(1, 4, 2, 5), (7, 10, 8, 11), (3, 9, 4, 8), (9, 3, 10, 2),
            (5, 12, 6, 1), (11, 6, 12, 7)],
}


def arcs(pd):
    """Map each edge label to its arc number (edges j, l continue over)."""
    parent = {}

    def find(x):
        while parent.setdefault(x, x) != x:
            x = parent[x]
        return x

    for (i, j, k, l) in pd:
        for e in (i, k):
            find(e)
        parent[find(j)] = find(l)
    roots = sorted({find(e) for c in pd for e in c})
    return {e: roots.index(find(e)) for c in pd for e in c}


def colouring_matrix(pd):
    """Rows 2x - y - z, one per crossing, columns indexed by arcs."""
    arc = arcs(pd)
    n = len(set(arc.values()))
    rows = []
    for (i, j, k, l) in pd:
        row = [0] * n
        row[arc[j]] += 2
        row[arc[i]] -= 1
        row[arc[k]] -= 1
        rows.append(row)
    return rows


def rank_mod_p(rows, p):
    """Rank of an integer matrix over the field Z/p (p prime)."""
    m = [[x % p for x in row] for row in rows]
    rank, cols = 0, len(m[0]) if m else 0
    for c in range(cols):
        pivot = next((r for r in range(rank, len(m)) if m[r][c]), None)
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        inv = pow(m[rank][c], p - 2, p)
        m[rank] = [x * inv % p for x in m[rank]]
        for r in range(len(m)):
            if r != rank and m[r][c]:
                f = m[r][c]
                m[r] = [(x - f * y) % p for x, y in zip(m[r], m[rank])]
        rank += 1
    return rank


def count_colourings(pd, p):
    """Number of Fox p-colourings = p^(arcs - rank mod p)."""
    rows = colouring_matrix(pd)
    return p ** (len(rows[0]) - rank_mod_p(rows, p))


def brute_force_count(pd, p):
    """Count Fox p-colourings by trying every assignment (small cases)."""
    rows = colouring_matrix(pd)
    n = len(rows[0])
    return sum(all(sum(a * c for a, c in zip(row, col)) % p == 0
                   for row in rows)
               for col in product(range(p), repeat=n))


def determinant(rows):
    """Exact determinant of a square matrix by Gaussian elimination."""
    m = [[Fraction(x) for x in row] for row in rows]
    det = Fraction(1)
    for c in range(len(m)):
        pivot = next((r for r in range(c, len(m)) if m[r][c] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != c:
            m[c], m[pivot] = m[pivot], m[c]
            det = -det
        det *= m[c][c]
        for r in range(c + 1, len(m)):
            f = m[r][c] / m[c][c]
            m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return det


def knot_determinant(pd):
    """|det| of the colouring matrix with its last row and column deleted."""
    rows = colouring_matrix(pd)
    if len(rows) == 1:
        return 1
    minor = [row[:-1] for row in rows[:-1]]
    return abs(int(determinant(minor)))


def main():
    print("Fox colourings: 2 * over = under + under (mod p) at each crossing")
    print("  knot            arcs  det  3-col  5-col  7-col  tricolourable")
    for name, pd in KNOTS.items():
        n = len(colouring_matrix(pd)[0])
        det = knot_determinant(pd)
        counts = [count_colourings(pd, p) for p in (3, 5, 7)]
        tri = "yes" if counts[0] > 3 else "no"
        print(f"  {name:<15} {n:4d} {det:4d} {counts[0]:6d} {counts[1]:6d}"
              f" {counts[2]:6d}  {tri}")
    checks = [(name, p) for name in ("3_1", "4_1", "5_1") for p in (3, 5)]
    agree = all(count_colourings(KNOTS[k], p) == brute_force_count(KNOTS[k], p)
                for k, p in checks)
    print(f"  brute force agrees on {len(checks)} small cases: {agree}")
    print()
    print("Constant colourings always work, giving p of them. A non-constant")
    print("p-colouring exists exactly when p divides the determinant. 3_1 is")
    print("tricolourable and the unknot is not, so 3_1 is knotted. 4_1 and 5_1")
    print("share det = 5 and the colouring counts above, yet they are different")
    print("knots: their Jones polynomials differ. Invariants can fail to")
    print("distinguish; they never wrongly separate.")
    print()
    print("Epistemic status: exact computation for these PD codes, with brute")
    print("force confirming the linear algebra on small cases. That colouring")
    print("counts are knot invariants is proved in the lesson (Reidemeister).")


if __name__ == "__main__":
    main()
