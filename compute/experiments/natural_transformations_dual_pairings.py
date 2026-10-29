"""Is there a natural isomorphism V -> V*?  Small finite fields answer.

The dual space construction is contravariant, so "V is naturally isomorphic
to V*" cannot even be stated for all linear maps. On the groupoid of
isomorphisms it can be: a natural isomorphism amounts to a non-degenerate
bilinear form B on each space with B(gv, gw) = B(v, w) for every invertible g,
i.e. g^T B g = B. We count such forms on F_p^n for small p and n by exhaustive
search, testing invariance on a generating set of GL_n(F_p). We also count how
many invertible maps preserve the dot product, the pairing a basis gives.
"""

from itertools import product

EXPERIMENT = {
    "id": "natural_transformations_dual_pairings",
    "title": "Invariant pairings: when could V be naturally isomorphic to V*?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["natural-transformations"],
    "summary": (
        "Counts non-degenerate bilinear forms on F_p^n invariant under all of "
        "GL_n(F_p), for p = 2, 3, 5 and n <= 3, by exhaustive search tested on "
        "generators of GL_n(F_p). They exist only in a few tiny cases (lines over "
        "F_2 and F_3, the plane over F_2). Also counts the invertible maps that "
        "preserve the dot product. Exact for these cases only."
    ),
    "packages": [],
}


def mat_mul(a, b, p):
    """Product of square matrices (tuples of row tuples) over F_p."""
    n = len(a)
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(n)) % p
                       for j in range(n)) for i in range(n))


def transpose(a):
    """The transpose of a square matrix."""
    return tuple(zip(*a))


def det(a, p):
    """Determinant over F_p by Laplace expansion (fine for n <= 3)."""
    n = len(a)
    if n == 1:
        return a[0][0] % p
    total = 0
    for j in range(n):
        minor = tuple(row[:j] + row[j + 1:] for row in a[1:])
        total += (-1) ** j * a[0][j] * det(minor, p)
    return total % p


def all_matrices(n, p):
    """Every n x n matrix over F_p."""
    for entries in product(range(p), repeat=n * n):
        yield tuple(tuple(entries[i * n:(i + 1) * n]) for i in range(n))


def primitive_root(p):
    """The least generator of the multiplicative group of F_p."""
    for g in range(1, p):
        if len({pow(g, k, p) for k in range(1, p)}) == p - 1:
            return g
    raise ValueError("p must be prime")


def gl_generators(n, p):
    """Transvections I + E_ij (i != j) and diag(g, 1, ..., 1), g a primitive
    root: a standard generating set of GL_n(F_p)."""
    ident = [[int(i == j) for j in range(n)] for i in range(n)]
    gens = []
    for i, j in product(range(n), repeat=2):
        if i != j:
            m = [row[:] for row in ident]
            m[i][j] = 1
            gens.append(tuple(map(tuple, m)))
    d = [row[:] for row in ident]
    d[0][0] = primitive_root(p)
    gens.append(tuple(map(tuple, d)))
    return gens


def invariant(b, g, p):
    """Is the bilinear form with Gram matrix b preserved by g: g^T b g = b?"""
    return mat_mul(mat_mul(transpose(g), b, p), g, p) == b


def invariant_forms(n, p):
    """Non-degenerate forms on F_p^n preserved by every element of GL_n(F_p)."""
    gens = gl_generators(n, p)
    return [b for b in all_matrices(n, p)
            if det(b, p) and all(invariant(b, g, p) for g in gens)]


def dot_preserving(n, p):
    """(number of invertible g with g^T g = I, size of GL_n(F_p))."""
    ident = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
    invertible = [g for g in all_matrices(n, p) if det(g, p)]
    keep = [g for g in invertible if invariant(ident, g, p)]
    return len(keep), len(invertible)


def main():
    print("Non-degenerate bilinear forms on F_p^n fixed by all of GL_n(F_p):")
    for p, n in [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (5, 1), (5, 2)]:
        forms = invariant_forms(n, p)
        shown = " ".join(str([list(r) for r in b]) for b in forms) or "none"
        print(f"  p = {p}, n = {n}: {len(forms)}  {shown}")
    print("Over F_5 the scalar 2 has 2^2 = 4 != 1, so even a line has none;")
    print("on F_2^2 the survivor is the determinant pairing, as det(g) = 1.")
    print()
    print("The dot product (a basis-made pairing) is preserved only by")
    for p, n in [(2, 2), (3, 2), (5, 2)]:
        keep, total = dot_preserving(n, p)
        print(f"  {keep:>2} of the {total:>3} invertible maps of F_{p}^{n}")
    print()
    print("Epistemic status: exact, exhaustive computation for the listed p and n,")
    print("relying on the standard theorem that transvections and one diagonal")
    print("matrix generate GL_n(F_p). It proves nothing about other fields or")
    print("dimensions. The lesson proves that over every field with more than")
    print("three elements even a line has no invariant pairing, so V -> V* is")
    print("not natural even on the groupoid of isomorphisms.")


if __name__ == "__main__":
    main()
