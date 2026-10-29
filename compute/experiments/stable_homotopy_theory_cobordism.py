"""Thom's unoriented cobordism ring, checked with Stiefel-Whitney numbers.

Thom (1954) computed the unoriented cobordism ring as a homotopy ring of a
Thom spectrum: N_* = pi_*(MO) = F_2[x_i : i not of the form 2^k - 1], so
dim N_n is the number of partitions of n into parts not of the form 2^k - 1.
Pontryagin and Thom: a closed manifold bounds iff all its Stiefel-Whitney
numbers vanish.

We compute (exactly, over F_2) the Stiefel-Whitney numbers of products of real
projective spaces from w(RP^a) = (1 + u)^(a+1), check which bound, and compare
the rank of the span of their Stiefel-Whitney number vectors with Thom's dim
N_n. In odd dimensions every such product bounds, so other generators (Dold
manifolds) are needed: the computation shows this, Thom's theorem explains it.
"""

from itertools import combinations_with_replacement
from math import comb

EXPERIMENT = {
    "id": "stable_homotopy_theory_cobordism",
    "title": "Thom's cobordism ring and Stiefel-Whitney numbers",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["stable-homotopy-theory"],
    "summary": (
        "Counts partitions of n with no part of the form 2^k - 1 (Thom's dim N_n) "
        "and computes all Stiefel-Whitney numbers of products of real projective "
        "spaces over F_2, finding which bound and the rank of the span they "
        "generate. Products of projective spaces span N_n in even degrees up "
        "to 8 but never in odd degrees. Exact; Thom's and Pontryagin's theorems are cited."
    ),
    "packages": [],
}


def partitions(n, largest=None):
    """All partitions of n as non-increasing tuples."""
    if largest is None:
        largest = n
    if n == 0:
        return [()]
    out = []
    for first in range(min(n, largest), 0, -1):
        for rest in partitions(n - first, first):
            out.append((first,) + rest)
    return out


def is_mersenne(i):
    """True when i = 2^k - 1 for some k >= 1."""
    return i >= 1 and (i + 1) & i == 0


def thom_rank(n):
    """dim N_n: partitions of n avoiding parts 1, 3, 7, 15, ..."""
    return sum(1 for p in partitions(n) if not any(is_mersenne(i) for i in p))


def sw_classes(dims):
    """The classes w_0, ..., w_n of RP^d1 x ... x RP^dr as polynomials.

    Each w_i is a set of exponent tuples (coefficients are in F_2): the
    degree-i part of the product of (1 + u_j)^(d_j + 1), truncated at
    u_j^(d_j + 1).
    """
    n = sum(dims)
    classes = []
    for i in range(n + 1):
        terms = set()
        for e in combinations_with_replacement(range(len(dims)), i):
            exps = tuple(e.count(j) for j in range(len(dims)))
            if all(x <= d for x, d in zip(exps, dims)):
                c = 1
                for x, d in zip(exps, dims):
                    c *= comb(d + 1, x)
                if c % 2:
                    terms.add(exps)
        classes.append(terms)
    return classes


def sw_number(dims, partition, classes=None):
    """w_I[RP^d1 x ... x RP^dr] in F_2, for a partition I of sum(dims):
    the coefficient of u_1^d1 ... u_r^dr in w_{i_1} ... w_{i_s}."""
    if classes is None:
        classes = sw_classes(dims)
    product = {tuple(0 for _ in dims)}
    for i in partition:
        new = set()
        for e1 in product:
            for e2 in classes[i]:
                e = tuple(a + b for a, b in zip(e1, e2))
                if all(x <= d for x, d in zip(e, dims)):
                    new ^= {e}
        product = new
    return 1 if tuple(dims) in product else 0


def rp_products(n):
    """All products RP^d1 x ... x RP^dr (d_i >= 1) of dimension n."""
    return [p for p in partitions(n)]


def rank_mod2(rows):
    """Rank over F_2 of a list of 0/1 vectors."""
    rows = [int("".join(map(str, r)), 2) for r in rows if any(r)]
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r:
            basis.append(r)
    return len(basis)


def main():
    print("Thom: dim N_n = #partitions of n with no part 1, 3, 7, 15, ...")
    print("  n:     " + " ".join(f"{n:3d}" for n in range(11)))
    print("  dim:   " + " ".join(f"{thom_rank(n):3d}" for n in range(11)))
    print()
    print("Products of real projective spaces, via Stiefel-Whitney numbers")
    print("  n  products  non-bounding  rank of span  Thom's dim N_n")
    for n in range(1, 9):
        parts = partitions(n)
        vectors = []
        for d in rp_products(n):
            classes = sw_classes(d)
            vectors.append([sw_number(d, I, classes) for I in parts])
        nonbounding = sum(1 for v in vectors if any(v))
        print(f"{n:3d}  {len(vectors):8d}  {nonbounding:12d}"
              f"  {rank_mod2(vectors):12d}  {thom_rank(n):14d}")
    v = [sw_number((2,), I) for I in partitions(2)]
    print(f"RP^2: (w_2, w_1^2) = {tuple(v)}, so RP^2 does not bound.")
    print("Odd n: every product has an odd-dimensional factor, which bounds.")
    print()
    print("Epistemic status: all Stiefel-Whitney numbers and partition counts")
    print("are exact computations over F_2, exhaustive for n <= 8. That they")
    print("decide cobordism (Pontryagin, Thom) and that N_* is polynomial on")
    print("generators in degrees not of the form 2^k - 1 (Thom) are theorems;")
    print("the agreement of the last two columns in even degrees is evidence.")


if __name__ == "__main__":
    main()
