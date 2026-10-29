"""Reading off a Jordan normal form from ranks, in exact arithmetic.

The lesson proves that the Jordan form of A is determined by the numbers
rank (A - lambda I)^k: the number of Jordan blocks for lambda of size at least
k is rank (A - lambda I)^(k-1) - rank (A - lambda I)^k. Here a 5 x 5 integer
matrix (built as P J P^-1 and then "forgotten") is analysed with that formula,
compared with SymPy's own jordan_form, and used to check the Cayley-Hamilton
theorem and the minimal polynomial exactly. A last pair of 4 x 4 matrices shows
that the characteristic and minimal polynomials alone do not determine the
Jordan form, while the ranks do.

All arithmetic is exact (rational), so each check is an exact verification for
these particular matrices; the general theorems are proved in the lesson.
"""

import sympy

EXPERIMENT = {
    "id": "advanced_linear_algebra_jordan",
    "title": "Jordan forms from ranks, and Cayley-Hamilton, exactly",
    "evidence": ["exact", "symbolic"],
    "lessons": ["advanced-linear-algebra"],
    "summary": (
        "Computes the ranks of (A - lambda I)^k for an integer 5 x 5 matrix, reads "
        "off its Jordan blocks with the rank formula, checks the answer against "
        "SymPy's jordan_form, verifies chi_A(A) = 0 and the minimal polynomial in "
        "exact arithmetic, and exhibits two non-similar 4 x 4 matrices with the "
        "same characteristic and minimal polynomials. Exact checks for these "
        "matrices only."
    ),
    "packages": ["sympy"],
}

X = sympy.Symbol("x")


def jordan_block(lam, size):
    """The size x size Jordan block with eigenvalue lam."""
    return sympy.Matrix(size, size, lambda i, j: lam if i == j else
                        (1 if j == i + 1 else 0))


def example_matrix():
    """A = P J P^-1 with J = J3(2) + J1(2) + J1(-1) and det P = 1."""
    p = sympy.Matrix([[1, 1, 0, 0, 0], [0, 1, 1, 0, 0], [1, 0, 1, 1, 0],
                      [0, 0, 0, 1, 1], [0, 1, 0, 0, 1]])
    j = sympy.diag(jordan_block(2, 3), jordan_block(2, 1), jordan_block(-1, 1))
    return p * j * p.inv()


def rank_sequence(a, lam):
    """[rank (A - lam I)^k for k = 0, 1, ...] until the ranks stop falling."""
    n = a.shape[0]
    shifted = a - lam * sympy.eye(n)
    ranks, power = [n], sympy.eye(n)
    while True:
        power = power * shifted
        ranks.append(power.rank())
        if ranks[-1] == ranks[-2]:
            return ranks


def block_sizes(ranks):
    """Jordan block sizes (largest first) from a rank sequence r_0, r_1, ...

    Blocks of size >= k number r_(k-1) - r_k, so blocks of size exactly k
    number r_(k-1) - 2 r_k + r_(k+1).
    """
    r = list(ranks) + [ranks[-1]]
    sizes = []
    for k in range(len(ranks) - 1, 0, -1):
        sizes += [k] * (r[k - 1] - 2 * r[k] + r[k + 1])
    return sizes


def jordan_data(a):
    """{eigenvalue: block sizes} computed with the rank formula."""
    roots = sympy.roots(a.charpoly(X).as_expr(), X)
    return {lam: block_sizes(rank_sequence(a, lam)) for lam in sorted(roots)}


def evaluate(poly_expr, a):
    """The matrix p(A) for a polynomial expression p in X (Horner's rule)."""
    result = sympy.zeros(*a.shape)
    for c in sympy.Poly(poly_expr, X).all_coeffs():
        result = result * a + c * sympy.eye(a.shape[0])
    return result


def blocks_of_jordan_matrix(j):
    """{eigenvalue: block sizes} read off a matrix already in Jordan form."""
    n, blocks, i = j.shape[0], {}, 0
    while i < n:
        k = 1
        while i + k < n and j[i + k - 1, i + k] == 1:
            k += 1
        blocks.setdefault(j[i, i], []).append(k)
        i += k
    return {lam: sorted(s, reverse=True) for lam, s in blocks.items()}


def minimal_polynomial(a):
    """prod (x - lambda)^(largest block for lambda), from the Jordan data."""
    return sympy.Mul(*[(X - lam) ** max(s) for lam, s in jordan_data(a).items()])


def main():
    a = example_matrix()
    print("A (a 5 x 5 integer matrix):")
    for i in range(5):
        print("   " + " ".join(f"{int(v):3d}" for v in a.row(i)))
    print("characteristic polynomial:", sympy.factor(a.charpoly(X).as_expr()))
    data = jordan_data(a)
    for lam, sizes in data.items():
        ranks = rank_sequence(a, lam)
        print(f"lambda = {lam}: ranks of (A - lambda I)^k, k = 0, 1, ...: "
              f"{ranks}")
        print(f"   -> Jordan block sizes {sizes}")
    _, j = a.jordan_form()
    print("SymPy's jordan_form gives the same blocks:",
          blocks_of_jordan_matrix(j) == data)
    m = minimal_polynomial(a)
    print("minimal polynomial:", m)
    chi = a.charpoly(X).as_expr()
    print("chi_A(A) = 0 (Cayley-Hamilton):", evaluate(chi, a).is_zero_matrix)
    print("m(A) = 0:", evaluate(m, a).is_zero_matrix)
    smaller = (X - 2) ** 2 * (X + 1)
    print("(x - 2)^2 (x + 1) kills A:", evaluate(smaller, a).is_zero_matrix)
    print()
    b = sympy.diag(jordan_block(0, 2), jordan_block(0, 2))
    c = sympy.diag(jordan_block(0, 2), jordan_block(0, 1), jordan_block(0, 1))
    print("B = J2(0) + J2(0) and C = J2(0) + J1(0) + J1(0):")
    print("   same characteristic polynomial:",
          b.charpoly(X) == c.charpoly(X), "  same minimal polynomial:",
          minimal_polynomial(b) == minimal_polynomial(c))
    print(f"   but rank B = {b.rank()} and rank C = {c.rank()}: "
          "not similar")
    print()
    print("Epistemic status: exact rational arithmetic on these specific "
          "matrices,\nso every 'True' above is an exact verification for them "
          "(trusting SymPy's\nimplementation). That the ranks determine the "
          "Jordan form of every\nmatrix, and that chi_A(A) = 0 always, are "
          "theorems proved in the lesson.")


if __name__ == "__main__":
    main()
