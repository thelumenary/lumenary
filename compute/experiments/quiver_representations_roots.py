"""Positive roots, Coxeter transformations and knitting for Dynkin quivers.

Gabriel's theorem says that a connected quiver has finitely many
indecomposable representations exactly when its underlying graph is of type
A, D or E, and that dimension vectors then match the positive roots: the
non-negative integer vectors x with Tits form q(x) = 1. We compute these roots
in three independent ways for several Dynkin quivers - by reflecting simple
roots, by brute force in a box, and by "knitting": applying the inverse
Coxeter transformation (which computes dim of tau^-1 M, the inverse
Auslander-Reiten translate) to the projective representations until an
injective is reached. For the Kronecker quiver the knitting never stops, and
the vector (1, 1) has q = 0: over F_p we count its p + 1 indecomposables, one
per point of the projective line. This is exact, exhaustive-finite evidence
for the quivers shown; Gabriel's theorem is the proof for all of them.
"""

from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "quiver_representations_roots",
    "title": "Quiver roots: reflections, brute force and knitting",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["quiver-representations"],
    "summary": (
        "For Dynkin quivers of types A, D and E it counts positive roots (Tits "
        "form 1) by reflections, by brute force, and by iterating the inverse "
        "Coxeter transformation on projectives (knitting the preprojective "
        "component). For the Kronecker quiver knitting never stops, and the "
        "indecomposables of dimension (1, 1) over F_p are counted: p + 1. Exact "
        "for these examples; Gabriel's theorem proves the pattern."
    ),
    "packages": [],
}

#: Quivers as (number of vertices, list of arrows i -> j).
QUIVERS = {
    "A4 (linear)": (4, [(0, 1), (1, 2), (2, 3)]),
    "A4 (zigzag)": (4, [(0, 1), (2, 1), (2, 3)]),
    "D4": (4, [(0, 1), (2, 1), (3, 1)]),
    "D5": (5, [(0, 2), (1, 2), (2, 3), (3, 4)]),
    "E6": (6, [(0, 1), (1, 2), (2, 3), (3, 4), (5, 2)]),
    "E7": (7, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (6, 2)]),
    "E8": (8, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (7, 4)]),
}
KRONECKER = (2, [(0, 1), (0, 1)])


def tits_form(x, arrows):
    """q(x) = sum of x_i^2 minus x_i x_j over arrows i -> j."""
    return sum(v * v for v in x) - sum(x[i] * x[j] for i, j in arrows)


def reflect(x, i, arrows):
    """Simple reflection s_i: x_i becomes (sum over neighbours of x_j) - x_i."""
    nbr = sum(x[b] for a, b in arrows if a == i) + sum(
        x[a] for a, b in arrows if b == i)
    y = list(x)
    y[i] = nbr - x[i]
    return tuple(y)


def roots_by_reflection(n, arrows):
    """Close the simple roots under simple reflections, keeping x >= 0."""
    simple = [tuple(int(k == i) for k in range(n)) for i in range(n)]
    found, todo = set(simple), list(simple)
    while todo:
        x = todo.pop()
        for i in range(n):
            y = reflect(x, i, arrows)
            if min(y) >= 0 and any(y) and y not in found:
                found.add(y)
                todo.append(y)
    return found


def roots_by_brute_force(n, arrows, bound):
    """All x in {0..bound}^n, x != 0, with q(x) = 1."""
    return {x for x in product(range(bound + 1), repeat=n)
            if any(x) and tits_form(x, arrows) == 1}


def euler_matrix(n, arrows):
    """E = I - A, A[i][j] = number of arrows i -> j; <x, y> = x^T E y."""
    e = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for i, j in arrows:
        e[i][j] -= 1
    return e


def mat_inv(m):
    """Inverse of a square matrix of Fractions (Gauss-Jordan)."""
    n = len(m)
    a = [list(row) + [Fraction(int(i == j)) for j in range(n)]
         for i, row in enumerate(m)]
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        a[c] = [v / a[c][c] for v in a[c]]
        for r in range(n):
            if r != c and a[r][c] != 0:
                a[r] = [u - a[r][c] * v for u, v in zip(a[r], a[c])]
    return [row[n:] for row in a]


def mat_mul(a, b):
    """Matrix product."""
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def coxeter_inverse(n, arrows):
    """Phi^-1 for Phi = -E^-1 E^T, so dim(tau M) = Phi dim M."""
    e = euler_matrix(n, arrows)
    et = [list(r) for r in zip(*e)]
    phi = [[-v for v in row] for row in mat_mul(mat_inv(e), et)]
    return mat_inv(phi)


def projective_dims(n, arrows):
    """dim P(i)_j = number of paths from i to j (the quiver must be acyclic)."""
    dims = []
    for i in range(n):
        count = [0] * n
        stack = [i]
        while stack:
            v = stack.pop()
            count[v] += 1
            stack.extend(b for a, b in arrows if a == v)
        dims.append(tuple(count))
    return dims


def knit(n, arrows, max_steps=60):
    """Dimension vectors tau^-k P(i), stopping when Phi^-1 leaves x >= 0."""
    cinv = coxeter_inverse(n, arrows)
    found = []
    for p in projective_dims(n, arrows):
        x = p
        for _ in range(max_steps):
            found.append(x)
            y = tuple(int(sum(cinv[i][j] * x[j] for j in range(n)))
                      for i in range(n))
            if min(y) < 0:
                break
            x = y
    return found


def kronecker_family_count(p):
    """Isoclasses of indecomposable Kronecker reps k --a,b--> k over F_p.

    (a, b) and (a', b') are isomorphic when (a', b') = t (a, b), t != 0; the
    pair (0, 0) is decomposable. So we count lines in F_p^2.
    """
    classes = set()
    for a, b in product(range(p), repeat=2):
        if (a, b) != (0, 0):
            classes.add(min(((t * a) % p, (t * b) % p) for t in range(1, p)))
    return len(classes)


def main():
    print("type          refl  brute  knit  (indecomposables = positive roots)")
    for name, (n, arrows) in QUIVERS.items():
        refl = roots_by_reflection(n, arrows)
        bound = max(max(x) for x in refl)
        brute = roots_by_brute_force(n, arrows, bound) if n <= 6 else None
        knitted = knit(n, arrows)
        same = set(knitted) == refl and len(knitted) == len(refl)
        same = same and (brute is None or brute == refl)
        shown = "-" if brute is None else len(brute)
        print(f"{name:<13} {len(refl):>4}  {shown:>5}  "
              f"{len(knitted):>4}  {'agree' if same else 'DISAGREE'}")
    print("(brute force over the box {0..max}^n, run for n <= 6 only)")
    print()
    n, arrows = 4, QUIVERS["D4"][1]
    print("D4, arrows into the centre (vector order: leaf, centre, leaf, leaf):")
    print("  " + " ".join("".join(map(str, x)) for x in knit(n, arrows)))
    print()
    n, arrows = KRONECKER
    print("Kronecker quiver 0 => 1: tau^-1 orbits never reach an injective")
    pre = knit(n, arrows, max_steps=4)
    print("  preprojectives:", ", ".join(str(x) for x in pre))
    print("  Tits form on them:", [tits_form(x, arrows) for x in pre])
    print("  q(1, 1) =", tits_form((1, 1), arrows), "(an imaginary root)")
    counts = [(p, kronecker_family_count(p)) for p in (2, 3, 5, 7)]
    print("  indecomposables of dim (1, 1) over F_p:",
          ", ".join(f"p={p}: {c}" for p, c in counts))
    print()
    print("Epistemic status: exact integer and rational arithmetic, exhaustive")
    print("for the quivers, boxes and primes shown. It checks Gabriel's count")
    print("of indecomposables against the positive roots in these cases (the")
    print("knitting uses the theorem that dim tau^-1 M = Phi^-1 dim M for")
    print("hereditary algebras); it does not prove Gabriel's theorem.")


if __name__ == "__main__":
    main()
