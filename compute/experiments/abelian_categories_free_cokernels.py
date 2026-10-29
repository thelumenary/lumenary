"""Where free abelian groups fail to be abelian: torsion in cokernels.

In the category F of finitely generated free abelian groups, a map
phi : Z^m -> Z^n has a kernel (subgroups of free groups are free), but its
cokernel in F is Z^n modulo the *saturation* of im(phi): the torsion of the
abelian-group cokernel Z^n / im(phi) is invisible. The canonical map
coimage -> image is then the inclusion im(phi) -> sat(im(phi)), of index
d_1 d_2 ... d_r (the invariant factors of phi), and it is an isomorphism
exactly when every invariant factor is 1. We compute invariant factors from
determinantal divisors (gcds of minors) for every 2 x 2 integer matrix with
entries in -2..2, and count how often F's coimage -> image map fails to be an
isomorphism - i.e. how often the abelian-category axiom fails.
"""

import itertools
import math

EXPERIMENT = {
    "id": "abelian_categories_free_cokernels",
    "title": "Torsion in cokernels: free abelian groups are not abelian",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["abelian-categories"],
    "summary": (
        "Computes invariant factors (via gcds of minors) of all 625 integer "
        "2 x 2 matrices with entries in -2..2. Whenever an invariant factor "
        "exceeds 1 the cokernel in Ab has torsion, and in free abelian groups "
        "the canonical coimage -> image map is not an isomorphism. Exact and "
        "exhaustive over that finite range."
    ),
    "packages": [],
}


def det(mat):
    """Determinant of a small square integer matrix (Leibniz formula)."""
    n = len(mat)
    total = 0
    for perm in itertools.permutations(range(n)):
        sign = 1
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    sign = -sign
        term = sign
        for i in range(n):
            term *= mat[i][perm[i]]
        total += term
    return total


def determinantal_divisors(mat):
    """[D_1, D_2, ...]: D_k = gcd of all k x k minors (0 if all vanish)."""
    m, n = len(mat), len(mat[0])
    out = []
    for k in range(1, min(m, n) + 1):
        g = 0
        for rows in itertools.combinations(range(m), k):
            for cols in itertools.combinations(range(n), k):
                g = math.gcd(g, det([[mat[r][c] for c in cols] for r in rows]))
        out.append(g)
    return out


def invariant_factors(mat):
    """Nonzero invariant factors d_1 | d_2 | ... of an integer matrix."""
    divisors = [1] + [d for d in determinantal_divisors(mat) if d != 0]
    return [divisors[k] // divisors[k - 1] for k in range(1, len(divisors))]


def cokernels(mat):
    """(Ab-cokernel description, F-cokernel rank) for mat : Z^cols -> Z^rows.

    Ab: list of torsion orders d > 1 plus a free rank; F: the free rank only.
    """
    factors = invariant_factors(mat)
    free_rank = len(mat) - len(factors)
    torsion = [d for d in factors if d > 1]
    return (torsion, free_rank), free_rank


def coimage_to_image_index(mat):
    """Index of im(phi) in its saturation: the product of invariant factors."""
    return math.prod(invariant_factors(mat))


def describe(torsion, free_rank):
    """A readable name such as 'Z/2 + Z' for an abelian group."""
    parts = [f"Z/{d}" for d in torsion] + ["Z"] * free_rank
    return " + ".join(parts) if parts else "0"


def main():
    print("Multiplication by k on Z, as a map of free abelian groups:")
    for k in [1, 2, 3, 0]:
        (tors, free), f_rank = cokernels([[k]])
        print(f"  k = {k}: cokernel in Ab = {describe(tors, free):<4}"
              f" cokernel in F = {describe([], f_rank):<2}"
              f" coim -> im index = {coimage_to_image_index([[k]])}")
    entries = range(-2, 3)
    mats = [[[a, b], [c, d]] for a, b, c, d in itertools.product(entries,
                                                                 repeat=4)]
    by_index = {}
    for mat in mats:
        idx = coimage_to_image_index(mat)
        by_index[idx] = by_index.get(idx, 0) + 1
    bad = sum(n for idx, n in by_index.items() if idx > 1)
    print(f"All {len(mats)} integer 2 x 2 matrices with entries in -2..2:")
    for idx in sorted(by_index):
        print(f"  index [sat(im) : im] = {idx}: {by_index[idx]:3d} matrices")
    print(f"  coimage -> image not an isomorphism in F: {bad} matrices")
    example = [[2, 0], [0, 2]]
    (tors, free), _ = cokernels(example)
    print(f"  e.g. 2 * identity: cokernel in Ab = {describe(tors, free)}, "
          "cokernel in F = 0:")
    print("  monic and epic in F, but not invertible")
    print()
    print("Epistemic status: exact integer arithmetic, exhaustive over the "
          "625\nmatrices shown. It illustrates the theorem that F is additive "
          "but not\nabelian; the proof (and the Lean file) handle the general "
          "case.")


if __name__ == "__main__":
    main()
