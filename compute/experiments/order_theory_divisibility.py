"""Divisibility as an order: Hasse diagrams, lattices and a least fixed point.

The experiment lists the covering pairs of ({1, ..., 12}, |) - the edges of
its Hasse diagram - and its minimal and maximal elements; checks that the
divisors of 60 form a lattice with meet gcd and join lcm, while {1, ..., 12}
is not a lattice; and computes a least fixed point two ways, as the
Knaster-Tarski theorem predicts: by iterating a monotone map on the subsets of
a finite set starting from the empty set, and as the intersection of all
sets S with f(S) contained in S. Exact and exhaustive for these examples.
"""

import itertools
import math

EXPERIMENT = {
    "id": "order_theory_divisibility",
    "title": "Divisibility orders, lattices and a least fixed point",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["order-theory"],
    "summary": (
        "Computes the Hasse diagram of divisibility on {1, ..., 12} and its "
        "maximal elements, checks exhaustively that the divisors of 60 form a "
        "lattice (meet gcd, join lcm) while {1, ..., 12} does not, and finds the "
        "least fixed point of a monotone map on subsets both by iteration from "
        "the empty set and as the meet of all pre-fixed points (Knaster-Tarski)."
    ),
    "packages": [],
}


def covers(elements, leq):
    """Pairs (a, b) with a < b and nothing strictly between: Hasse edges."""
    return [(a, b) for a in elements for b in elements
            if a != b and leq(a, b)
            and not any(c not in (a, b) and leq(a, c) and leq(c, b)
                        for c in elements)]


def divides(a, b):
    """a | b."""
    return b % a == 0


def maximal(elements, leq):
    """Elements with no strictly larger element."""
    return [m for m in elements
            if not any(x != m and leq(m, x) for x in elements)]


def least_upper_bound(elements, leq, a, b):
    """The join of a and b inside `elements`, or None."""
    ups = [u for u in elements if leq(a, u) and leq(b, u)]
    least = [u for u in ups if all(leq(u, v) for v in ups)]
    return least[0] if least else None


def lattice_check(elements, leq):
    """Return the first pair without a join, or None if all joins exist."""
    for a, b in itertools.combinations(elements, 2):
        if least_upper_bound(elements, leq, a, b) is None:
            return a, b
    return None


EDGES = {0: {1, 2}, 1: {3}, 2: {3}, 3: {4}, 4: set(), 5: {6}, 6: {5}, 7: {0}}


def step(s, start=0, edges=EDGES):
    """f(S) = {start} together with every successor of S: monotone in S."""
    return frozenset({start}) | frozenset(t for v in s for t in edges[v])


def lfp_by_iteration(f):
    """Kleene iteration: empty set, f(empty), f(f(empty)), ... until stable."""
    s, rounds = frozenset(), 0
    while f(s) != s:
        s, rounds = f(s), rounds + 1
    return s, rounds


def lfp_by_prefixed_points(f, universe):
    """Intersection of all S with f(S) a subset of S (Knaster-Tarski)."""
    result = frozenset(universe)
    for r in range(len(universe) + 1):
        for s in itertools.combinations(universe, r):
            s = frozenset(s)
            if f(s) <= s:
                result &= s
    return result


def main():
    nums = list(range(1, 13))
    edges = covers(nums, divides)
    print(f"Hasse diagram of ({{1..12}}, |): {len(edges)} covering pairs")
    print("  " + " ".join(f"{a}-{b}" for a, b in edges[:12]))
    print("  " + " ".join(f"{a}-{b}" for a, b in edges[12:]))
    print("  minimal:", maximal(nums, lambda a, b: divides(b, a)),
          " maximal:", maximal(nums, divides))
    print("  pair with no join in {1..12}:", lattice_check(nums, divides))
    d60 = [d for d in range(1, 61) if 60 % d == 0]
    ok = all(least_upper_bound(d60, divides, a, b) == math.lcm(a, b)
             for a in d60 for b in d60)
    print(f"divisors of 60 ({len(d60)}): every join exists and is the lcm:", ok)
    print("  pair with no join among divisors of 60:",
          lattice_check(d60, divides))
    print()
    fix, rounds = lfp_by_iteration(step)
    meet = lfp_by_prefixed_points(step, range(8))
    print("reachable from 0 in a graph = least fixed point of S -> {0} u succ(S)")
    print(f"  iteration from the empty set: {sorted(fix)} after {rounds} rounds")
    print(f"  meet of all pre-fixed points: {sorted(meet)}")
    print("  the two agree:", fix == meet)
    print()
    print("Epistemic status: exact, exhaustive computations for these finite")
    print("examples. They illustrate the definitions and the Knaster-Tarski")
    print("theorem, which the lesson proves for every complete lattice.")


if __name__ == "__main__":
    main()
