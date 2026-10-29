"""When does a monotone map between finite lattices have a right adjoint?

A Galois connection l -| u between posets means l(a) <= b if and only if
a <= u(b). For finite lattices the adjoint functor theorem for posets says: a
monotone map l has a right adjoint exactly when it preserves all joins (binary
joins and the least element), and then u(b) = max{a : l(a) <= b}. We test
this on every monotone map between several small lattices. Part 2 checks the
currying adjunction - x B -| (-)^B on small finite sets: the bijection
Hom(A x B, C) -> Hom(A, C^B) and its naturality in A and C.
"""

from itertools import product

EXPERIMENT = {
    "id": "adjunctions_galois_finite",
    "title": "Galois connections on finite lattices and currying, exhaustively",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["adjunctions"],
    "summary": (
        "Enumerates every monotone map between small lattices (a chain, the "
        "Boolean square, the divisors of 12) and checks that a right adjoint exists "
        "exactly for the maps preserving finite joins, computing it as "
        "u(b) = max{a : l(a) <= b}. Then verifies that currying is a natural "
        "bijection on small finite sets. Exhaustive for these examples only."
    ),
    "packages": [],
}


def chain(n):
    """The chain 0 < 1 < ... < n-1 as (elements, leq)."""
    return list(range(n)), lambda a, b: a <= b


def boolean_square():
    """Subsets of {0, 1} as bitmasks 0..3, ordered by inclusion."""
    return [0, 1, 2, 3], lambda a, b: a & b == a


def divisors(n):
    """Divisors of n ordered by divisibility."""
    return [d for d in range(1, n + 1) if n % d == 0], lambda a, b: b % a == 0


def join(P, leq, a, b):
    """Least upper bound in a finite lattice."""
    ub = [x for x in P if leq(a, x) and leq(b, x)]
    return next(x for x in ub if all(leq(x, y) for y in ub))


def bottom(P, leq):
    """Least element of a finite lattice."""
    return next(x for x in P if all(leq(x, y) for y in P))


def monotone_maps(L, M):
    """All monotone maps L -> M, as dicts."""
    (P, le_p), (Q, le_q) = L, M
    maps = (dict(zip(P, v)) for v in product(Q, repeat=len(P)))
    return [f for f in maps
            if all(le_q(f[a], f[b]) for a in P for b in P if le_p(a, b))]


def preserves_joins(f, L, M):
    """Does f preserve binary joins and the least element?"""
    (P, le_p), (Q, le_q) = L, M
    return f[bottom(P, le_p)] == bottom(Q, le_q) and all(
        f[join(P, le_p, a, b)] == join(Q, le_q, f[a], f[b]) for a in P for b in P)


def right_adjoint(f, L, M):
    """u with f(a) <= b iff a <= u(b), or None if there is none."""
    (P, le_p), (Q, le_q) = L, M
    u = {}
    for b in Q:
        below = [a for a in P if le_q(f[a], b)]
        top = [a for a in below if all(le_p(x, a) for x in below)]
        if not top:
            return None
        u[b] = top[0]
    ok = all(le_q(f[a], b) == le_p(a, u[b]) for a in P for b in Q)
    return u if ok else None


def curry(h, A, B):
    """Hom(A x B, C) -> Hom(A, C^B), with functions as dicts."""
    return {a: tuple(h[(a, b)] for b in B) for a in A}


def currying_report(A, B, C, A2, C2):
    """(is curry a bijection?, is it natural for all u : A2 -> A, v : C -> C2?)"""
    pairs = list(product(A, B))
    homs = [dict(zip(pairs, v)) for v in product(C, repeat=len(pairs))]
    images = {tuple(sorted(curry(h, A, B).items())) for h in homs}
    bijective = len(images) == len(homs) == (len(C) ** len(B)) ** len(A)
    natural = all(
        curry({(a, b): v[h[(u[a], b)]] for a in A2 for b in B}, A2, B)
        == {a: tuple(v[c] for c in curry(h, A, B)[u[a]]) for a in A2}
        for h in homs
        for u in (dict(zip(A2, w)) for w in product(A, repeat=len(A2)))
        for v in (dict(zip(C, w)) for w in product(C2, repeat=len(C))))
    return bijective, natural


def main():
    cases = [("B2", boolean_square(), "C3", chain(3)),
             ("C3", chain(3), "B2", boolean_square()),
             ("B2", boolean_square(), "B2", boolean_square()),
             ("D12", divisors(12), "C3", chain(3))]
    print("Monotone maps l : L -> M (C3 = chain 0 < 1 < 2, B2 = subsets of")
    print("{0, 1}, D12 = divisors of 12 under divisibility):")
    for name_l, L, name_m, M in cases:
        mono = monotone_maps(L, M)
        adj = [f for f in mono if right_adjoint(f, L, M) is not None]
        pres = [f for f in mono if preserves_joins(f, L, M)]
        print(f"  {name_l:>3} -> {name_m:<3} {len(mono):>3} monotone, {len(adj):>2} "
              f"with right adjoint, = join-preserving: {adj == pres}")
    L, M = chain(3), divisors(12)
    f = {0: 1, 1: 2, 2: 4}
    print(f"  e.g. l = {f} : C3 -> D12 has right adjoint")
    print(f"       u = {right_adjoint(f, L, M)}")
    print()
    print("Currying Hom(A x B, C) -> Hom(A, C^B):")
    for sizes in [(2, 2, 2), (1, 3, 2), (2, 3, 2)]:
        A, B, C = (list(range(k)) for k in sizes)
        bij, nat = currying_report(A, B, C, [0, 1], ["x", "y"])
        print(f"  |A|, |B|, |C| = {sizes}: bijection {bij}, natural in A and C "
              f"{nat}")
    print()
    print("Epistemic status: exhaustive checks over all monotone maps (and all")
    print("maps for currying) in these small examples. They are evidence for the")
    print("theorems; the lesson proves that left adjoints preserve joins and that")
    print("currying is a natural bijection for all sets.")


if __name__ == "__main__":
    main()
