"""Stiefel-Whitney classes of real projective spaces, computed exactly mod 2.

The cohomology ring is H*(RP^n; Z/2) = Z/2[a]/(a^(n+1)), and the tangent bundle
has total Stiefel-Whitney class w = (1 + a)^(n+1) (a theorem in the lesson). We
expand this polynomial mod 2, read off which classes are nonzero, and invert it
to get the dual classes w-bar with w * w-bar = 1. Consequences: if w is not 1,
RP^n is not parallelisable; if w-bar_k is nonzero, RP^n does not immerse in
R^(n+k-1) (Whitney duality). Exact arithmetic in a finite ring; the topology
enters only through the two theorems the computation takes as input.
"""

from math import comb

EXPERIMENT = {
    "id": "vector_bundles_characteristic_classes_stiefel_whitney",
    "title": "Stiefel-Whitney classes of projective spaces",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["vector-bundles-characteristic-classes"],
    "summary": (
        "Expands w(T RP^n) = (1 + a)^(n+1) in Z/2[a]/(a^(n+1)) for n = 1..16, lists "
        "the nonzero classes, and inverts it to find the dual classes. It recovers "
        "that RP^n can be parallelisable only if n + 1 is a power of 2 and that "
        "RP^(2^r) does not immerse in R^(2^(r+1) - 2). Exact, given the formula for "
        "w(T RP^n) and Whitney duality."
    ),
    "packages": [],
}


def total_sw(n):
    """Coefficients mod 2 of (1 + a)^(n+1), truncated at degree n."""
    return [comb(n + 1, i) % 2 for i in range(n + 1)]


def multiply(p, q, n):
    """Product of two polynomials mod 2, truncated at degree n."""
    r = [0] * (n + 1)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q[: n + 1 - i]):
                r[i + j] ^= y
    return r


def inverse(p, n):
    """Inverse of a polynomial with constant term 1 in Z/2[a]/(a^(n+1))."""
    inv = [1] + [0] * n
    for k in range(1, n + 1):
        inv[k] = sum(p[i] * inv[k - i] for i in range(1, k + 1)) % 2
    return inv


def nonzero_degrees(p):
    """Degrees of the nonzero coefficients, excluding degree 0."""
    return [i for i, x in enumerate(p) if x and i > 0]


def ranges(degrees):
    """Compress [1, 2, 3, 8] to '1-3,8'."""
    parts, start = [], None
    for i, d in enumerate(degrees):
        if start is None:
            start = d
        if i + 1 == len(degrees) or degrees[i + 1] != d + 1:
            parts.append(str(start) if start == d else f"{start}-{d}")
            start = None
    return ",".join(parts) or "-"


def immersion_bound(n):
    """Largest k with w-bar_k nonzero: RP^n does not immerse in R^(n+k-1)."""
    dual = inverse(total_sw(n), n)
    return max(nonzero_degrees(dual), default=0)


def main():
    print("w(T RP^n) = (1 + a)^(n+1) in Z/2[a]/(a^(n+1)), and its inverse w-bar")
    print()
    print(f"{'n':>3}  {'nonzero w_i':<22}{'w = 1?':<8}{'top w-bar':<11}"
          f"no immersion in")
    for n in range(1, 17):
        w = total_sw(n)
        dual = inverse(w, n)
        assert multiply(w, dual, n) == [1] + [0] * n
        assert w[n] == (n + 1) % 2  # w_n = Euler characteristic mod 2
        degs = nonzero_degrees(w)
        shown = ranges(degs)
        k = immersion_bound(n)
        bound = f"R^{n + k - 1}" if k > 1 else "-"
        print(f"{n:>3}  {shown:<22}{'yes' if not degs else 'no':<8}"
              f"{k:<11}{bound}")
    print()
    print("w = 1 exactly when n + 1 is a power of 2 (n = 1, 3, 7, 15): only")
    print("those RP^n can be parallelisable, and RP^1, RP^3, RP^7 are. For")
    print("n = 2^r the top dual class is w-bar_(n-1), so RP^(2^r) does not")
    print("immerse in R^(2n-2): Whitney's bound 2n - 1 is sharp.")
    print()
    print("Epistemic status: exact computation in Z/2[a]/(a^(n+1)) for n <= 16.")
    print("It takes as given the theorem w(T RP^n) = (1 + a)^(n+1) and Whitney")
    print("duality; parallelisability of RP^15 is NOT implied (it is false:")
    print("by Adams, only RP^1, RP^3 and RP^7 are parallelisable).")


if __name__ == "__main__":
    main()
