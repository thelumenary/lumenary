"""Mapping cones over a finite field: the long exact sequence, checked exactly.

In the homotopy category K(k) every chain map f : X -> Y sits in a
distinguished triangle X -> Y -> C(f) -> X[1], where the mapping cone has
C(f)^n = X^(n+1) + Y^n and d(x, y) = (-dx, f(x) + dy). Applying cohomology
gives a long exact sequence, which is equivalent to the dimension formula

    dim H^n(C) = (dim H^n(Y) - rank H^n(f)) + (dim H^(n+1)(X) - rank H^(n+1)(f)).

We build random complexes and random chain maps over F_101 (exact modular
arithmetic), check that d_C o d_C = 0, check the formula in every degree, and
check that f is a quasi-isomorphism exactly when C(f) is acyclic. Then we count
by brute force the morphisms of triangles that complete the identity square
for the triangle X --0--> Y -> Y + X[1] -> X[1] in D(F_p): there are p of them,
so the third map in TR3 is not unique. Exact computations on random examples
and a finite count: evidence for the theorems proved in the lesson.
"""

import random
from itertools import product

EXPERIMENT = {
    "id": "triangulated_categories_cones",
    "title": "Mapping cones over F_p: exactness and non-unique fill-ins",
    "evidence": ["exact", "experimental", "exhaustive-finite"],
    "lessons": ["triangulated-categories"],
    "summary": (
        "Builds random cochain complexes and chain maps over F_101, forms mapping "
        "cones, and checks d^2 = 0, the dimension formula equivalent to the long "
        "exact cohomology sequence, and 'f is a quasi-isomorphism iff its cone is "
        "acyclic', exactly, on 200 random examples (a quarter of them identity "
        "maps). Then counts the p fill-ins "
        "completing an identity square of triangles in D(F_p), by brute force."
    ),
    "packages": [],
}

P = 101


def rank(rows, p=P):
    """Rank of a matrix (list of rows) over F_p by Gaussian elimination."""
    m = [[v % p for v in r] for r in rows if r]
    if not m:
        return 0
    r, cols = 0, len(m[0])
    for c in range(cols):
        piv = next((i for i in range(r, len(m)) if m[i][c]), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], p - 2, p)
        m[r] = [v * inv % p for v in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                t = m[i][c]
                m[i] = [(a - t * b) % p for a, b in zip(m[i], m[r])]
        r += 1
    return r


def nullspace(rows, ncols, p=P):
    """A basis of {v : rows v = 0} over F_p."""
    m = [[v % p for v in r] for r in rows]
    pivots, r = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c]), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], p - 2, p)
        m[r] = [v * inv % p for v in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                t = m[i][c]
                m[i] = [(a - t * b) % p for a, b in zip(m[i], m[r])]
        pivots.append(c)
        r += 1
    basis = []
    for free in (c for c in range(ncols) if c not in pivots):
        v = [0] * ncols
        v[free] = 1
        for i, c in enumerate(pivots):
            v[c] = -m[i][free] % p
        basis.append(v)
    return basis


def matmul(a, b, p=P):
    """Product of matrices given as lists of rows (handles empty shapes)."""
    if not a or not b:
        return [[0] * (len(b[0]) if b else 0) for _ in a]
    return [[sum(x * y for x, y in zip(row, col)) % p for col in zip(*b)]
            for row in a]


def zeros(r, c):
    """The r x c zero matrix."""
    return [[0] * c for _ in range(r)]


def random_complex(rng, length=4, max_dim=3):
    """A random complex: dims[n] and differentials d[n] : X^n -> X^(n+1).

    Built as a sum of pieces k (in one degree) and k --1--> k, then hidden by
    random changes of basis, so that d o d = 0 holds by construction.
    """
    pieces = []
    for n in range(length):
        pieces += [("H", n)] * rng.randint(0, max_dim - 1)
        if n + 1 < length:
            pieces += [("A", n)] * rng.randint(0, 1)
    dims = [0] * length
    where = []
    for kind, n in pieces:
        where.append((kind, n, dims[n], dims[n + 1] if kind == "A" else None))
        dims[n] += 1
        if kind == "A":
            dims[n + 1] += 1
    d = [zeros(dims[n + 1], dims[n]) for n in range(length - 1)]
    for kind, n, i, j in where:
        if kind == "A":
            d[n][j][i] = 1
    g = [random_invertible(rng, k) for k in dims]
    ginv = [inverse(m) for m in g]
    return dims, [matmul(matmul(g[n + 1], d[n]), ginv[n])
                  for n in range(length - 1)]


def random_invertible(rng, k):
    """A uniformly random invertible k x k matrix over F_p."""
    while True:
        m = [[rng.randrange(P) for _ in range(k)] for _ in range(k)]
        if rank(m) == k:
            return m


def inverse(m):
    """Inverse of an invertible matrix over F_p (Gauss-Jordan)."""
    k = len(m)
    aug = [row[:] + [int(i == j) for j in range(k)] for i, row in enumerate(m)]
    for c in range(k):
        piv = next(i for i in range(c, k) if aug[i][c] % P)
        aug[c], aug[piv] = aug[piv], aug[c]
        inv = pow(aug[c][c], P - 2, P)
        aug[c] = [v * inv % P for v in aug[c]]
        for i in range(k):
            if i != c and aug[i][c]:
                t = aug[i][c]
                aug[i] = [(a - t * b) % P for a, b in zip(aug[i], aug[c])]
    return [row[k:] for row in aug]


def random_chain_map(rng, x, y):
    """A random solution f of d_Y f^n = f^(n+1) d_X (all degrees)."""
    (dx, ddx), (dy, ddy) = x, y
    length = len(dx)
    offs, tot = [], 0
    for n in range(length):
        offs.append(tot)
        tot += dy[n] * dx[n]
    eqs = []
    for n in range(length - 1):
        for i in range(dy[n + 1]):
            for j in range(dx[n]):
                row = [0] * tot
                for k in range(dy[n]):  # (d_Y f^n)[i][j]
                    row[offs[n] + k * dx[n] + j] += ddy[n][i][k]
                for k in range(dx[n + 1]):  # (f^(n+1) d_X)[i][j]
                    row[offs[n + 1] + i * dx[n + 1] + k] -= ddx[n][k][j]
                eqs.append(row)
    basis = nullspace(eqs, tot) if eqs else [
        [int(i == j) for j in range(tot)] for i in range(tot)]
    v = [0] * tot
    for b in basis:
        c = rng.randrange(P)
        v = [(a + c * bb) % P for a, bb in zip(v, b)]
    return [[[v[offs[n] + i * dx[n] + j] for j in range(dx[n])]
             for i in range(dy[n])] for n in range(length)]


def cone(x, y, f):
    """Mapping cone, with C^n = X^(n+1) + Y^n, as (dims, differentials).

    Degrees run from -1 (where C^-1 = X^0) to length - 1.
    """
    (dx, ddx), (dy, ddy) = x, y
    length = len(dx)
    xd = lambda n: dx[n] if 0 <= n < length else 0
    yd = lambda n: dy[n] if 0 <= n < length else 0
    dims = [xd(n + 1) + yd(n) for n in range(-1, length)]
    diffs = []
    for n in range(-1, length - 1):
        m = zeros(xd(n + 2) + yd(n + 1), xd(n + 1) + yd(n))
        for i in range(xd(n + 2)):
            for j in range(xd(n + 1)):
                m[i][j] = -ddx[n + 1][i][j] % P
        for i in range(yd(n + 1)):
            for j in range(xd(n + 1)):
                m[xd(n + 2) + i][j] = f[n + 1][i][j]
            for j in range(yd(n)):
                m[xd(n + 2) + i][xd(n + 1) + j] = ddy[n][i][j]
        diffs.append(m)
    return dims, diffs


def cohomology(c):
    """dim H^n for a complex (dims, diffs) indexed from its first term."""
    dims, d = c
    out = []
    for n in range(len(dims)):
        rk_out = rank(d[n]) if n < len(d) else 0
        rk_in = rank(d[n - 1]) if n > 0 else 0
        out.append(dims[n] - rk_out - rk_in)
    return out


def cycles(c, n):
    """A basis of Z^n = ker d^n (as vectors)."""
    dims, d = c
    if n >= len(d):
        return [[int(i == j) for j in range(dims[n])] for i in range(dims[n])]
    return nullspace(d[n], dims[n])


def rank_on_cohomology(x, y, f, n):
    """rank of H^n(f) = dim(f(Z^n X) + B^n Y) - dim B^n Y."""
    image = [[sum(f[n][i][j] * z[j] for j in range(len(z))) % P
              for i in range(y[0][n])] for z in cycles(x, n)]
    bound = [list(col) for col in zip(*y[1][n - 1])] if n > 0 else []
    return rank(image + bound) - rank(bound)


def fill_in_count(p):
    """Morphisms c : Z -> Z completing (id, id) on X --0--> Y -> Z -> X[1].

    Model in D(F_p) = graded vector spaces with X = F_p, Y = F_p[1], so that
    Z = Y + X[1] has both summands in degree -1, g = inclusion of Y and
    h = projection to X[1]; conditions: c g = g and h c = h.
    """
    g = [[1], [0]]
    h = [[0, 1]]
    count = 0
    for a, b, c, d in product(range(p), repeat=4):
        m = [[a, b], [c, d]]
        if matmul(m, g, p) == g and matmul(h, m, p) == h:
            count += 1
    return count


def identity_map(x):
    """The identity chain map of a complex x."""
    return [[[int(i == j) for j in range(k)] for i in range(k)] for k in x[0]]


def main():
    rng = random.Random(2024)
    trials, d2_ok, les_ok, qis_ok, quasi = 200, 0, 0, 0, 0
    for t in range(trials):
        x = random_complex(rng)
        if t % 4 == 0:  # every fourth example: the identity, a quasi-iso
            y, f = x, identity_map(x)
        else:
            y = random_complex(rng)
            f = random_chain_map(rng, x, y)
        c = cone(x, y, f)
        d2_ok += all(not any(map(any, matmul(c[1][n + 1], c[1][n])))
                     for n in range(len(c[1]) - 1))
        hx, hy, hc = cohomology(x), cohomology(y), cohomology(c)
        length = len(hx)
        rk = [rank_on_cohomology(x, y, f, n) for n in range(length)] + [0]
        hx_ = hx + [0]
        les_ok += all(hc[n + 1] == hy[n] - rk[n] + hx_[n + 1] - rk[n + 1]
                      for n in range(length))
        is_qis = hx == hy and all(rk[n] == hx[n] for n in range(length))
        quasi += is_qis
        qis_ok += is_qis == (sum(hc) == 0)
    print(f"Chain maps of random complexes over F_{P}, degrees 0..3: {trials}")
    print(f"  cones with d o d = 0:                     {d2_ok}/{trials}")
    print(f"  dimension formula (long exact sequence):  {les_ok}/{trials}")
    print(f"  'quasi-iso <=> acyclic cone' consistent:  {qis_ok}/{trials}"
          f"  ({quasi} quasi-isos)")
    print()
    print("Fill-ins c completing (id, id) for X --0--> Y -> Y + X[1] -> X[1]")
    print("in D(F_p), X = F_p, Y = F_p[1] (c = [[1, t], [0, 1]], t free):")
    print("  " + ", ".join(f"p = {p}: {fill_in_count(p)}" for p in (2, 3, 5)))
    print()
    print("Epistemic status: exact arithmetic mod 101 on 200 pseudo-random")
    print("examples (seeded), plus an exhaustive count over 2 x 2 matrices.")
    print("This is evidence that the cone construction behaves as the lesson")
    print("proves (exactness, cones detect quasi-isomorphisms, non-unique")
    print("fill-ins); random examples over one field do not prove it.")


if __name__ == "__main__":
    main()
