"""Cellular homology of four surfaces, and the universal coefficient theorem.

Glue the sides of a square in pairs by a word such as "a b a' b'" (a' is a
inverse, read counter-clockwise from the bottom-left corner). This gives a
cell complex with one 2-cell, the distinct edge letters as 1-cells and the
classes of identified corners as 0-cells, with cellular chain complex
Z --d2--> Z^E --d1--> Z^V. We build d2 and d1 from the word, check d1 d2 = 0,
and compute homology over Z (Smith normal form: Betti numbers and torsion),
over F_2, F_3 and over Q (ranks). Then we check the universal coefficient
theorem dim H_n(X; F_p) = b_n + t_n(p) + t_(n-1)(p), where t_n(p) counts the
torsion factors of H_n(X; Z) divisible by p, and the Euler characteristic.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "homological_algebra_surface_homology",
    "title": "Homology of glued squares and universal coefficients",
    "evidence": ["exact"],
    "lessons": ["homological-algebra"],
    "summary": (
        "Builds the cellular chain complexes of the torus, Klein bottle, "
        "sphere and real projective plane from square gluing words, checks "
        "d1 d2 = 0, computes integral homology by Smith normal form and "
        "homology over F_2, F_3 and Q by ranks, and verifies the universal "
        "coefficient theorem and the Euler characteristic in each case. Exact "
        "computations for four complexes."
    ),
    "packages": [],
}

WORDS = {
    "torus": "a b a' b'",
    "Klein bottle": "a b a' b",
    "sphere": "a a' b b'",
    "projective plane": "a b a b",
}


def cell_complex(word):
    """(d2, d1) as integer matrices (lists of rows) for a square gluing word."""
    sides = [(s[0], -1 if s.endswith("'") else 1) for s in word.split()]
    letters = sorted({s for s, _ in sides})
    parent = list(range(4))                  # corners 0..3, union-find

    def find(c):
        while parent[c] != c:
            c = parent[c]
        return c

    ends = {}                                # letter -> (tail, head) corners
    for k, (s, e) in enumerate(sides):
        tail, head = (k, (k + 1) % 4) if e == 1 else ((k + 1) % 4, k)
        if s in ends:
            for old, new in zip(ends[s], (tail, head)):
                parent[find(old)] = find(new)
        else:
            ends[s] = (tail, head)
    vertices = sorted({find(c) for c in range(4)})
    d2 = [[sum(e for s, e in sides if s == letter)] for letter in letters]
    d1 = [[0] * len(letters) for _ in vertices]
    for j, letter in enumerate(letters):
        tail, head = ends[letter]
        d1[vertices.index(find(head))][j] += 1
        d1[vertices.index(find(tail))][j] -= 1
    return d2, d1


def matmul(a, b):
    """Product of integer matrices given as lists of rows."""
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)]
            for row in a]


def rank(mat, p=None):
    """Rank over F_p (p prime) or over Q (p = None)."""
    rows = [[Fraction(v) if p is None else v % p for v in r] for r in mat]
    r, cols = 0, len(rows[0]) if rows else 0
    for c in range(cols):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = 1 / rows[r][c] if p is None else pow(rows[r][c], p - 2, p)
        rows[r] = [v * inv if p is None else v * inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                k = rows[i][c]
                rows[i] = [(a - k * b) if p is None else (a - k * b) % p
                           for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def smith_diagonal(matrix):
    """Smith normal form diagonal (d1 | d2 | ...) of an integer matrix."""
    a = [list(row) for row in matrix]
    m, n = len(a), len(a[0]) if a else 0
    diag = []
    for t in range(min(m, n)):
        cells = [(abs(a[i][j]), i, j) for i in range(t, m)
                 for j in range(t, n) if a[i][j]]
        if not cells:
            break
        while True:
            _, i, j = min(cells)
            a[t], a[i] = a[i], a[t]
            for row in a:
                row[t], row[j] = row[j], row[t]
            done = True
            for i in range(t + 1, m):
                q = a[i][t] // a[t][t]
                a[i] = [x - q * y for x, y in zip(a[i], a[t])]
                done &= a[i][t] == 0
            for j in range(t + 1, n):
                q = a[t][j] // a[t][t]
                for row in a:
                    row[j] -= q * row[t]
                done &= a[t][j] == 0
            bad = [i for i in range(t + 1, m) for j in range(t + 1, n)
                   if a[i][j] % a[t][t]]
            if done and bad:
                a[t] = [x + y for x, y in zip(a[t], a[bad[0]])]
                done = False
            if done:
                break
            cells = [(abs(a[i][j]), i, j) for i in range(t, m)
                     for j in range(t, n) if a[i][j]]
        diag.append(abs(a[t][t]))
    return diag


def torsion(mat):
    """Invariant factors > 1 of an integer matrix: the torsion of its cokernel."""
    return [d for d in smith_diagonal(mat) if d > 1]


def homology(word, p=None):
    """Betti numbers (b0, b1, b2) over Q or F_p, plus integral torsion."""
    d2, d1 = cell_complex(word)
    v, e = len(d1), len(d2)
    r1, r2 = rank(d1, p), rank(d2, p)
    betti = (v - r1, e - r1 - r2, 1 - r2)
    return betti, {0: torsion(d1), 1: torsion(d2), 2: []}


def main():
    print("Surface            V E F  d1d2=0  H_0, H_1, H_2 over Z        chi")
    uct_ok = True
    for name, word in WORDS.items():
        d2, d1 = cell_complex(word)
        zero = all(x == 0 for row in matmul(d1, d2) for x in row)
        b, tors = homology(word)
        groups = []
        for n in range(3):
            parts = ["Z"] * b[n] + [f"Z/{t}" for t in tors[n]]
            groups.append(" + ".join(parts) or "0")
        chi = len(d1) - len(d2) + 1
        print(f"{name:18} {len(d1)} {len(d2)} 1  {str(zero):6}  "
              f"{', '.join(groups):26} {chi}")
        for p in (2, 3):
            bp, _ = homology(word, p)
            t = [sum(1 for f in tors[n] if f % p == 0) for n in range(3)]
            predicted = tuple(b[n] + t[n] + (t[n - 1] if n else 0)
                              for n in range(3))
            uct_ok = uct_ok and bp == predicted
            uct_ok = uct_ok and chi == bp[0] - bp[1] + bp[2] == b[0] - b[1] + b[2]
    print("Betti numbers over F_2 for the Klein bottle and RP^2:",
          homology(WORDS["Klein bottle"], 2)[0],
          homology(WORDS["projective plane"], 2)[0])
    print("Universal coefficients over F_2, F_3 and chi = V - E + F agree:",
          uct_ok)
    print()
    print("Epistemic status: exact integer and modular arithmetic for four "
          "small cell\ncomplexes; it confirms the theorems in these cases "
          "only. The universal\ncoefficient theorem is stated in the lesson "
          "and proved in the references.")


if __name__ == "__main__":
    main()
