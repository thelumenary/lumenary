"""Simplicial homology of four surfaces, computed exactly over the integers.

For a triangulated surface we build the boundary matrices d1 (edges to
vertices) and d2 (triangles to edges) with the usual signs, put them in Smith
normal form over Z, and read off H_n = Z^(b_n) + torsion. We also compute the
Betti numbers with coefficients in Z/2 and check the Euler-Poincare formula
V - E + F = b0 - b1 + b2. This is exact computation for these particular
triangulations; that the answers do not depend on the triangulation is a
theorem (homotopy invariance of homology), not something the computation shows.
"""

from itertools import combinations

EXPERIMENT = {
    "id": "algebraic_topology_homology",
    "title": "Homology of the sphere, torus, Klein bottle and projective plane",
    "evidence": ["exact"],
    "lessons": ["algebraic-topology"],
    "summary": (
        "Builds simplicial boundary matrices for explicit triangulations of S^2, "
        "the torus, the Klein bottle and RP^2, computes their Smith normal forms "
        "over Z and ranks over Z/2, and reports Betti numbers, torsion and the "
        "Euler characteristic. Exact for these complexes; independence of the "
        "triangulation is a theorem, not a consequence of the computation."
    ),
    "packages": [],
}


def grid_surface(twist):
    """Triangulate a 3x3 grid of squares with opposite sides glued.

    twist=False gives the torus; twist=True glues top to bottom with a flip,
    giving the Klein bottle. Returns a list of triangles (sorted vertex tuples).
    """
    def label(a, b):
        if b % 3 == 0 and b != 0 and twist:
            a = -a
        return (a % 3) * 3 + (b % 3)
    triangles = []
    for i in range(3):
        for j in range(3):
            p, q = label(i, j), label(i + 1, j)
            r, s = label(i + 1, j + 1), label(i, j + 1)
            triangles += [tuple(sorted((p, q, r))), tuple(sorted((p, s, r)))]
    return triangles


SURFACES = {
    "sphere S^2": [tuple(t) for t in combinations(range(4), 3)],
    "torus T^2": grid_surface(False),
    "Klein bottle": grid_surface(True),
    "proj. plane RP^2": [
        (0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5),
        (1, 2, 4), (2, 3, 5), (1, 3, 4), (2, 4, 5), (1, 3, 5),
    ],
}


def boundary_matrices(triangles):
    """Return (vertices, edges, d1, d2) with integer matrices as lists of rows."""
    edges = sorted({e for t in triangles for e in combinations(t, 2)})
    verts = sorted({v for t in triangles for v in t})
    vi = {v: k for k, v in enumerate(verts)}
    ei = {e: k for k, e in enumerate(edges)}
    d1 = [[0] * len(edges) for _ in verts]
    for k, (a, b) in enumerate(edges):
        d1[vi[b]][k] += 1
        d1[vi[a]][k] -= 1
    d2 = [[0] * len(triangles) for _ in edges]
    for k, (a, b, c) in enumerate(triangles):
        for sign, face in ((1, (b, c)), (-1, (a, c)), (1, (a, b))):
            d2[ei[face]][k] += sign
    return verts, edges, d1, d2


def smith_diagonal(matrix):
    """Nonzero diagonal entries of the Smith normal form of an integer matrix."""
    m = [row[:] for row in matrix]
    diag = []
    while m and m[0]:
        entries = [(abs(x), i, j) for i, row in enumerate(m)
                   for j, x in enumerate(row) if x]
        if not entries:
            break
        _, i, j = min(entries)
        m[0], m[i] = m[i], m[0]
        for row in m:
            row[0], row[j] = row[j], row[0]
        done = False
        while not done:
            done = True
            p = m[0][0]
            for i in range(1, len(m)):
                q = m[i][0] // p
                m[i] = [x - q * y for x, y in zip(m[i], m[0])]
            for j in range(1, len(m[0])):
                q = m[0][j] // p
                for row in m:
                    row[j] -= q * row[0]
            rest = [(abs(x), i, j) for i, row in enumerate(m)
                    for j, x in enumerate(row)
                    if x and (i == 0 or j == 0) and (i, j) != (0, 0)]
            if rest:
                _, i, j = min(rest)
                if i:
                    m[0], m[i] = m[i], m[0]
                else:
                    for row in m:
                        row[0], row[j] = row[j], row[0]
                done = False
            elif any(x % p for row in m[1:] for x in row[1:]):
                i = next(i for i, row in enumerate(m)
                         if i and any(x % p for x in row[1:]))
                m[0] = [x + y for x, y in zip(m[0], m[i])]
                done = False
        diag.append(abs(m[0][0]))
        m = [row[1:] for row in m[1:]]
    return diag


def rank_mod2(matrix):
    """Rank of an integer matrix reduced modulo 2 (Gaussian elimination)."""
    rows = [sum(1 << j for j, x in enumerate(r) if x % 2) for r in matrix]
    rank = 0
    for bit in range(max((r.bit_length() for r in rows), default=0)):
        pivot = next((r for r in rows if r >> bit & 1), None)
        if pivot is None:
            continue
        rows = [r ^ pivot if r >> bit & 1 else r for r in rows if r != pivot]
        rank += 1
    return rank


def homology(triangles):
    """Return (betti over Z, torsion of H_1, betti over Z/2, (V, E, F))."""
    verts, edges, d1, d2 = boundary_matrices(triangles)
    s1, s2 = smith_diagonal(d1), smith_diagonal(d2)
    nv, ne, nf = len(verts), len(edges), len(triangles)
    betti = (nv - len(s1), ne - len(s1) - len(s2), nf - len(s2))
    torsion = [d for d in s2 if d > 1]
    r1, r2 = rank_mod2(d1), rank_mod2(d2)
    betti2 = (nv - r1, ne - r1 - r2, nf - r2)
    return betti, torsion, betti2, (nv, ne, nf)


def describe(betti, torsion):
    """Human-readable H_0, H_1, H_2 such as 'Z | Z+Z/2 | 0'."""
    def group(rank, tors):
        parts = (["Z^%d" % rank] if rank > 1 else ["Z"] * rank)
        parts += ["Z/%d" % t for t in tors]
        return "+".join(parts) or "0"
    return " | ".join([group(betti[0], []), group(betti[1], torsion),
                       group(betti[2], [])])


def main():
    print("Simplicial homology over Z (exact, via Smith normal form)")
    print()
    print(f"{'surface':<18}{'V,E,F':<12}{'H0 | H1 | H2':<20}"
          f"{'b mod 2':<10}chi")
    for name, tris in SURFACES.items():
        betti, torsion, betti2, (v, e, f) = homology(tris)
        chi = v - e + f
        assert chi == betti[0] - betti[1] + betti[2]
        assert chi == betti2[0] - betti2[1] + betti2[2]
        print(f"{name:<18}{f'{v},{e},{f}':<12}{describe(betti, torsion):<20}"
              f"{','.join(map(str, betti2)):<10}{chi}")
    print()
    print("In every row V - E + F equals the alternating sum of the Betti")
    print("numbers, over Z and over Z/2 alike, although the Z/2 Betti numbers")
    print("of RP^2 and the Klein bottle differ from the integral ones: torsion")
    print("Z/2 in H_1 becomes an extra Z/2 in both H_1 and H_2 mod 2.")
    print()
    print("Epistemic status: exact integer linear algebra on four explicit")
    print("triangulations. That homology is independent of the triangulation")
    print("(indeed a homotopy invariant) is a theorem discussed in the lesson,")
    print("not something this computation establishes.")


if __name__ == "__main__":
    main()
