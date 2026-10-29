"""Which ways of combining two elements of a set work for every set at once?

A family of maps alpha_X : X x X -> X, one for each set X, is natural when
alpha_Y(f(a), f(b)) = f(alpha_X(a, b)) for every function f : X -> Y. The
lesson proves that the only natural families are the two projections. Here we
search exhaustively on the finite sets {0, 1} and {0, 1, 2}: first for tables
that commute with every bijection of the set (symmetry), then for tables that
commute with every function from the set to itself (a necessary condition for
naturality). Symmetry alone allows a third operation; the functions kill it,
and we print a square that fails.
"""

from itertools import permutations, product

EXPERIMENT = {
    "id": "natural_transformations_uniform_operations",
    "title": "Natural binary operations on finite sets: symmetry versus naturality",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["natural-transformations"],
    "summary": (
        "Enumerates every table X x X -> X on sets of sizes 2 and 3 and keeps those "
        "commuting with all bijections, then those commuting with all self-maps. On "
        "three elements, symmetry allows three operations but naturality only the two "
        "projections; a non-injective map refutes the third. Exhaustive for these "
        "sizes only; the lesson's proof covers all sets."
    ),
    "packages": [],
}


def all_tables(n):
    """Every map n x n -> n, as a tuple t with t[a * n + b] = alpha(a, b)."""
    return product(range(n), repeat=n * n)


def all_maps(m, n):
    """Every function {0..m-1} -> {0..n-1}, as a tuple of values."""
    return list(product(range(n), repeat=m))


def commutes(t_src, t_dst, f, m, n):
    """Does the square for f : m -> n commute: t_dst(f a, f b) = f(t_src(a, b))?"""
    return all(t_dst[f[a] * n + f[b]] == f[t_src[a * m + b]]
               for a in range(m) for b in range(m))


def natural_tables(n, maps):
    """Tables on n commuting with every endomap in ``maps`` (an exhaustive search)."""
    return [t for t in all_tables(n)
            if all(commutes(t, t, f, n, n) for f in maps)]


def projection(n, k):
    """The k-th projection n x n -> n (k = 0: first, k = 1: second)."""
    return tuple((a, b)[k] for a in range(n) for b in range(n))


def third_element(t):
    """On {0, 1, 2}: is t the operation (a, a) -> a, (a, b) -> the third element?"""
    want = tuple(a if a == b else 3 - a - b for a in range(3) for b in range(3))
    return t == want


def breaking_square(t, n=3):
    """The first endomap f of {0..n-1} and pair (a, b) where the square fails,
    as (f, a, b, alpha(f a, f b), f(alpha(a, b))); None if t is natural."""
    for f in all_maps(n, n):
        for a in range(n):
            for b in range(n):
                lhs, rhs = t[f[a] * n + f[b]], f[t[a * n + b]]
                if lhs != rhs:
                    return f, a, b, lhs, rhs
    return None


def main():
    print("Tables alpha : X x X -> X, searched exhaustively.")
    for n in (2, 3):
        bij = [tuple(p) for p in permutations(range(n))]
        sym = natural_tables(n, bij)
        nat = natural_tables(n, all_maps(n, n))
        print(f"|X| = {n}: {n ** (n * n):>5} tables, {len(sym)} commute with all "
              f"{len(bij)} bijections, {len(nat)} with all {n ** n} self-maps")
    sym3 = natural_tables(3, [tuple(p) for p in permutations(range(3))])
    nat3 = natural_tables(3, all_maps(3, 3))
    projections = {projection(3, 0), projection(3, 1)}
    print(f"On 3 elements the natural tables are the projections: "
          f"{set(nat3) == projections}")
    extra = [t for t in sym3 if t not in projections]
    print(f"The symmetric extra table is 'the third element': "
          f"{len(extra) == 1 and third_element(extra[0])}")
    f, a, b, lhs, rhs = breaking_square(extra[0])
    print(f"Its square fails for f = {f} (i -> f[i]) at the pair ({a}, {b}):")
    print(f"  alpha(f({a}), f({b})) = alpha({f[a]}, {f[b]}) = {lhs},  but  "
          f"f(alpha({a}, {b})) = f({extra[0][a * 3 + b]}) = {rhs}.")
    print("f is not injective: symmetry alone cannot see this failure.")
    print()
    print("Epistemic status: an exhaustive search over all 16 and 19,683 tables on")
    print("sets of sizes 2 and 3 - complete for those sizes, silent about larger")
    print("sets. That only the projections are natural on all sets is proved in")
    print("the lesson (and in Lean), using one test pair in a two-element set.")


if __name__ == "__main__":
    main()
