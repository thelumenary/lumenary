"""Mapping cones of chain complexes, and why cones are not functorial.

Chain complexes of finite-dimensional rational vector spaces are a model for
the stable infinity-category D(Q): a morphism is a chain map, and a
commutative square up to homotopy is a square together with a chosen chain
homotopy. We compute exactly, with fractions:

1. the mapping cone Cone(f) of a chain map and its homology, checking that
   f is a quasi-isomorphism exactly when Cone(f) is acyclic (three examples);
2. a square X -> Y, X' -> Y' with a = 0 and b = 0, together with a homotopy
   h of degree +1. The induced map Cone(f) -> Cone(f') depends on h: with
   X = Q[0], Y = 0, X' = 0, Y' = Q[1], every scalar h gives a chain map on cones
   that acts on homology as multiplication by h. In the triangulated homotopy
   category all of these squares are the same square (a = b = 0), so the map on
   cones is not determined by the square: cones are not functorial. Remember
   the homotopy, as a stable infinity-category does, and the map is determined.

Exact rational arithmetic on small examples; illustrative, not a proof.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "stable_infinity_categories_cones",
    "title": "Mapping cones and the non-functoriality of cones",
    "evidence": ["exact"],
    "lessons": ["stable-infinity-categories"],
    "summary": (
        "Builds mapping cones of chain maps between small complexes of rational "
        "vector spaces with exact fractions, checks d^2 = 0 and that f is a "
        "quasi-isomorphism iff Cone(f) is acyclic, and shows that the map induced "
        "on cones by a square depends on the chosen homotopy: the same square in "
        "the homotopy category induces multiplication by any scalar. Exact, on "
        "small examples only."
    ),
    "packages": [],
}


def zeros(rows, cols):
    """A rows x cols zero matrix of Fractions."""
    return [[Fraction(0)] * cols for _ in range(rows)]


def matmul(a, b, inner, cols):
    """Product of an r x inner matrix and an inner x cols matrix (lists of
    rows). Shapes are passed explicitly so that empty matrices work."""
    return [[sum((a[i][k] * b[k][j] for k in range(inner)), Fraction(0))
             for j in range(cols)] for i in range(len(a))]


def rank(m):
    """Rank of a matrix of Fractions, by Gaussian elimination."""
    rows = [list(r) for r in m]
    r = 0
    cols = len(rows[0]) if rows else 0
    for c in range(cols):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                factor = rows[i][c] / rows[r][c]
                rows[i] = [x - factor * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


class Complex:
    """A bounded chain complex: dims[n] = dim C_n, diff[n]: C_n -> C_(n-1)."""

    def __init__(self, dims, diff=None):
        self.dims = {n: d for n, d in dims.items() if d > 0}
        self.diff = diff or {}

    def dim(self, n):
        return self.dims.get(n, 0)

    def d(self, n):
        """The differential C_n -> C_(n-1) as a dim(n-1) x dim(n) matrix."""
        if n in self.diff:
            return self.diff[n]
        return zeros(self.dim(n - 1), self.dim(n))

    def degrees(self):
        return range(min(self.dims, default=0) - 1, max(self.dims, default=0) + 2)


def is_complex(c):
    """Check d_(n-1) d_n = 0 in every degree."""
    return all(rank(matmul(c.d(n - 1), c.d(n), c.dim(n - 1), c.dim(n))) == 0
               for n in c.degrees() if c.dim(n) and c.dim(n - 2))


def betti(c):
    """Homology dimensions {n: dim H_n} (only nonzero ones)."""
    out = {}
    for n in c.degrees():
        h = c.dim(n) - rank(c.d(n)) - rank(c.d(n + 1))
        if h:
            out[n] = h
    return out


def block(top_left, top_right, bottom_left, bottom_right):
    """Assemble a 2 x 2 block matrix (blocks given as lists of rows)."""
    top = [l + r for l, r in zip(top_left, top_right)]
    bottom = [l + r for l, r in zip(bottom_left, bottom_right)]
    return top + bottom


def neg(m):
    return [[-x for x in row] for row in m]


def cone(f, x, y):
    """Mapping cone of f: X -> Y. Cone_n = X_(n-1) + Y_n with differential
    (u, v) |-> (-d u, f u + d v). ``f[n]`` is the matrix Y_n x X_n."""
    degrees = list(x.dims) + list(y.dims) + [0]
    dims = {n: x.dim(n - 1) + y.dim(n)
            for n in range(min(degrees), max(degrees) + 2)}
    diff = {}
    for n in dims:
        fm = f.get(n - 1, zeros(y.dim(n - 1), x.dim(n - 1)))
        diff[n] = block(neg(x.d(n - 1)), zeros(x.dim(n - 2), y.dim(n)),
                        fm, y.d(n))
    return Complex(dims, diff)


def is_chain_map(f, x, y):
    """Check d_Y f_n = f_(n-1) d_X in every degree."""
    get = lambda n: f.get(n, zeros(y.dim(n), x.dim(n)))
    return all(matmul(y.d(n), get(n), y.dim(n), x.dim(n)) ==
               matmul(get(n - 1), x.d(n), x.dim(n - 1), x.dim(n))
               for n in x.degrees() if x.dim(n) and y.dim(n - 1))


def q(*rows):
    """A matrix of Fractions from integer rows."""
    return [[Fraction(v) for v in row] for row in rows]


def mat(maps, n, rows, cols):
    """The degree-n component of a graded map, or the zero matrix."""
    return maps.get(n, zeros(rows, cols))


def is_homotopy(h, a, b, f, f2, x, y, x2, y2):
    """Check b f - f' a = d h + h d, for h_n: X_n -> Y'_(n+1)."""
    for n in x.degrees():
        if not (x.dim(n) and y2.dim(n)):
            continue
        cols = x.dim(n)
        bf = matmul(mat(b, n, y2.dim(n), y.dim(n)),
                    mat(f, n, y.dim(n), cols), y.dim(n), cols)
        fa = matmul(mat(f2, n, y2.dim(n), x2.dim(n)),
                    mat(a, n, x2.dim(n), cols), x2.dim(n), cols)
        dh = matmul(y2.d(n + 1), mat(h, n, y2.dim(n + 1), cols),
                    y2.dim(n + 1), cols)
        hd = matmul(mat(h, n - 1, y2.dim(n), x.dim(n - 1)), x.d(n),
                    x.dim(n - 1), cols)
        for i in range(y2.dim(n)):
            for j in range(x.dim(n)):
                if bf[i][j] - fa[i][j] != dh[i][j] + hd[i][j]:
                    return False
    return True


def cone_map(a, b, h, x, y, x2, y2):
    """The chain map Cone(f) -> Cone(f') induced by a square (a, b) and a
    homotopy h with b f - f' a = d h + h d: (u, v) |-> (a u, b v + h u)."""
    out = {}
    for n in range(min(x.degrees()[0], y.degrees()[0]),
                   max(x.degrees()[-1], y.degrees()[-1]) + 1):
        out[n] = block(mat(a, n - 1, x2.dim(n - 1), x.dim(n - 1)),
                       zeros(x2.dim(n - 1), y.dim(n)),
                       mat(h, n - 1, y2.dim(n), x.dim(n - 1)),
                       mat(b, n, y2.dim(n), y.dim(n)))
    return out


def square_example(h):
    """X = Q[0], Y = 0, X' = 0, Y' = Q[1], f = f' = 0, a = b = 0, and the
    homotopy h: X_0 -> Y'_1 given by the scalar h. Returns (is the homotopy
    valid, is the induced map a chain map of cones, its degree-1 matrix)."""
    x, y, x2, y2 = Complex({0: 1}), Complex({}), Complex({}), Complex({1: 1})
    f, f2, a, b = {}, {}, {}, {}
    hom = {0: [[Fraction(h)]]}
    phi = cone_map(a, b, hom, x, y, x2, y2)
    cf, cf2 = cone(f, x, y), cone(f2, x2, y2)
    return (is_homotopy(hom, a, b, f, f2, x, y, x2, y2),
            is_chain_map(phi, cf, cf2), phi[1])


EXAMPLES = {
    "Q[0] -> (Q =id=> Q), not a q-iso": (
        Complex({0: 1}), Complex({1: 1, 0: 1}, {1: q([1])}), {0: q([1])}),
    "Q[0] -> (Q -> Q^2), a q-iso": (
        Complex({0: 1}), Complex({1: 1, 0: 2}, {1: q([1], [0])}),
        {0: q([0], [1])}),
    "(Q =2=> Q) -> 0, both acyclic": (
        Complex({1: 1, 0: 1}, {1: q([2])}), Complex({}), {}),
}


def main():
    print("1. Cones detect quasi-isomorphisms (homology dims as {degree: dim})")
    for name, (x, y, f) in EXAMPLES.items():
        c = cone(f, x, y)
        print(f"   {name}")
        print(f"     chain map: {is_chain_map(f, x, y)}, Cone d^2 = 0: "
              f"{is_complex(c)}")
        print(f"     H(X) = {betti(x)}, H(Y) = {betti(y)}, "
              f"H(Cone) = {betti(c)}")
    print()
    print("2. One square up to homotopy, many maps on cones")
    print("   X = Q[0], Y = 0, X' = 0, Y' = Q[1], f = f' = 0, a = b = 0.")
    print("   Homotopy h: X_0 -> Y'_1 (any scalar: d h + h d = 0 = b f - f' a).")
    print("   Cone f = Q[1] = Cone f' (zero differentials), so H_1 = Cone_1.")
    for h in [0, 1, 2, Fraction(-1, 3)]:
        valid, chain, m = square_example(h)
        print(f"   h = {str(h):>4}: homotopy {valid}, chain map {chain}, "
              f"map on H_1 = multiply by {m[0][0]}")
    print("   In the homotopy category these are one square (a = b = 0), and each")
    print("   map is a valid TR3 fill: the triangulated axioms cannot choose one.")
    print()
    print("Epistemic status: exact rational arithmetic on small, explicit")
    print("complexes. It illustrates the general facts proved in the lesson")
    print("(cones detect quasi-isomorphisms; maps of cones depend on homotopies)")
    print("but checks only these examples.")


if __name__ == "__main__":
    main()
