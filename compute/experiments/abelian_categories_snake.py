"""The snake lemma, computed: kernels, cokernels and the connecting map mod p.

Vector spaces over F_p form an abelian category in which every short exact
sequence splits, so every morphism of short exact sequences
0 -> A -> B -> C -> 0  to  0 -> A' -> B' -> C' -> 0 is, up to isomorphism,
B = A + C, B' = A' + C' with the middle map in block form
    beta = [[alpha, x], [0, gamma]],   x : C -> A' arbitrary.
For random such diagrams we compute ker and coker of alpha, beta, gamma,
the connecting map delta(w) = [x w] in coker(alpha), and check that the
six-term sequence
    0 -> ker a -> ker b -> ker c --delta--> coker a -> coker b -> coker c -> 0
is exact at every term (image dimension = kernel dimension, composites 0).
Exact modular arithmetic; seeded random examples.
"""

import random

EXPERIMENT = {
    "id": "abelian_categories_snake",
    "title": "The snake lemma, computed over a finite field",
    "evidence": ["exact", "experimental"],
    "lessons": ["abelian-categories"],
    "summary": (
        "Builds 300 seeded random morphisms of short exact sequences of F_5-"
        "vector spaces, computes kernels, cokernels and the connecting map by "
        "exact row reduction, and checks exactness of the six-term snake "
        "sequence at every term. Evidence for these cases only; the lesson "
        "proves the lemma in every abelian category."
    ),
    "packages": [],
}

P = 5


def rank(cols, p=P):
    """Rank over F_p of the matrix whose columns are the given vectors."""
    rows = [list(r) for r in zip(*cols)] if cols else []
    r = 0
    ncols = len(cols)
    for c in range(ncols):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [v * inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                k = rows[i][c]
                rows[i] = [(a - k * b) % p for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def apply(mat, vec, p=P):
    """Matrix (list of rows) times column vector, mod p."""
    return [sum(a * b for a, b in zip(row, vec)) % p for row in mat]


def columns(mat):
    """The columns of a matrix given as a list of rows."""
    return [list(c) for c in zip(*mat)] if mat and mat[0] else []


def identity(n):
    """The n x n identity matrix."""
    return [[int(i == j) for j in range(n)] for i in range(n)]


def kernel_basis(mat, n, p=P):
    """A basis of the kernel of mat : F_p^n -> F_p^m (mat has n columns)."""
    rows = [list(r) for r in mat]
    pivots = []
    r = 0
    for c in range(n):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [v * inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                k = rows[i][c]
                rows[i] = [(a - k * b) % p for a, b in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
    basis = []
    for free in (c for c in range(n) if c not in pivots):
        v = [0] * n
        v[free] = 1
        for i, c in enumerate(pivots):
            v[c] = -rows[i][free] % p
        basis.append(v)
    return basis


def rank_into_quotient(vectors, sub):
    """Rank of the span of vectors in the quotient by span(sub)."""
    return rank(vectors + sub) - rank(sub)


def random_matrix(m, n, rng, p=P, sparse=0.5):
    """A random m x n matrix over F_p with many zeros (to get kernels)."""
    return [[rng.randrange(p) if rng.random() > sparse else 0
             for _ in range(n)] for _ in range(m)]


def snake_data(a, c, a2, c2, rng):
    """Random diagram; returns dims and ranks of the six-term sequence."""
    alpha = random_matrix(a2, a, rng)
    gamma = random_matrix(c2, c, rng)
    x = random_matrix(a2, c, rng, sparse=0.2)
    beta = ([alpha[i] + x[i] for i in range(a2)]
            + [[0] * a + gamma[j] for j in range(c2)])
    ka, kb, kc = (kernel_basis(alpha, a), kernel_basis(beta, a + c),
                  kernel_basis(gamma, c))
    im_a, im_b, im_c = columns(alpha), columns(beta), columns(gamma)
    f_ka = [v + [0] * c for v in ka]               # ker a -> ker b
    g_kb = [v[a:] for v in kb]                     # ker b -> ker c
    delta = [apply(x, w) for w in kc]              # ker c -> coker a
    fp = [e + [0] * c2 for e in identity(a2)]      # f' : A' -> B'
    gp = [e[a2:] for e in identity(a2 + c2)]       # g' : B' -> C'
    dims = [len(ka), len(kb), len(kc), a2 - rank(im_a),
            a2 + c2 - rank(im_b), c2 - rank(im_c)]
    ranks = [rank(f_ka), rank(g_kb), rank_into_quotient(delta, im_a),
             rank_into_quotient(fp, im_b), rank_into_quotient(gp, im_c)]
    zero_composites = (
        rank_into_quotient([apply(x, v[a:]) for v in kb], im_a) == 0
        and rank_into_quotient([apply(x, w) + [0] * c2 for w in kc], im_b)
        == 0)
    return dims, ranks, zero_composites


def is_exact(dims, ranks):
    """Exactness of 0 -> V1 -> ... -> V6 -> 0 from dims and map ranks."""
    incoming = [0] + ranks          # rank of the map into each term
    outgoing = ranks + [0]          # rank of the map out of each term
    return all(i == d - o for i, d, o in zip(incoming, dims, outgoing))


def main():
    rng = random.Random(2025)
    trials, exact, nonzero_delta, euler_ok = 300, 0, 0, 0
    example = None
    for t in range(trials):
        a, c, a2, c2 = (rng.randint(1, 4) for _ in range(4))
        dims, ranks, zero = snake_data(a, c, a2, c2, rng)
        exact += is_exact(dims, ranks) and zero
        nonzero_delta += ranks[2] > 0
        alt = dims[0] - dims[1] + dims[2] - dims[3] + dims[4] - dims[5]
        euler_ok += alt == 0
        if example is None and ranks[2] > 0 and min(dims) > 0:
            example = (a, c, a2, c2, dims, ranks)
    print(f"Snake lemma over F_{P}: {trials} random morphisms of short exact "
          "sequences")
    print(f"  six-term sequence exact at all six terms: {exact} / {trials}")
    print(f"  connecting map delta nonzero:             {nonzero_delta}")
    print(f"  alternating sum of dimensions equal to 0: {euler_ok} / {trials}")
    if example:
        a, c, a2, c2, dims, ranks = example
        names = ["ker a", "ker b", "ker c", "coker a", "coker b", "coker c"]
        print(f"Example with dim A, C, A', C' = {a}, {c}, {a2}, {c2}:")
        print("  dimensions: " + ", ".join(
            f"{n} = {d}" for n, d in zip(names[:3], dims[:3])))
        print("              " + ", ".join(
            f"{n} = {d}" for n, d in zip(names[3:], dims[3:])))
        print(f"  ranks of the five maps (delta in the middle): {ranks}")
    print()
    print("Epistemic status: exact arithmetic in F_5, so each check is a true "
          "statement\nabout the diagram tested; 300 random diagrams are "
          "evidence, not proof. The\nsnake lemma itself is proved in the "
          "lesson (and in Mathlib) for every\nabelian category.")


if __name__ == "__main__":
    main()
