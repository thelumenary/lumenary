"""The first stages of the cumulative hierarchy, computed exactly.

The hereditarily finite sets - the members of V_omega - can be coded by natural
numbers (Ackermann 1937): the code of a set x is the sum of 2^code(y) over its
members y, so "y is a member of x" means "bit number code(y) of code(x) is 1".
The empty set has code 0, and every natural number codes exactly one set.

In this coding V_{k+1} = P(V_k) becomes a statement about numbers: the stage
V_k consists exactly of the codes below |V_k|, and |V_{k+1}| = 2^|V_k|. We
compute the stages up to V_5 (65536 sets), compute the rank of each set by the
recursion rank(x) = sup{rank(y) + 1 : y in x}, and check exhaustively that
x is in V_k iff rank(x) < k, that every stage is transitive, and that every
non-empty set in V_5 has an element disjoint from it (the axiom of foundation).

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from collections import Counter
from functools import lru_cache
import textwrap

EXPERIMENT = {
    "id": "axiomatic_set_theory_hierarchy",
    "title": "The cumulative hierarchy V_0, ..., V_5 in Ackermann's coding",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["axiomatic-set-theory"],
    "summary": (
        "Codes hereditarily finite sets by natural numbers (y is in x iff bit y of x "
        "is 1), builds V_0, ..., V_5, computes ranks by recursion, and checks "
        "exhaustively that V_k is the set of codes below |V_k| = 2^|V_(k-1)|, that "
        "x is in V_k iff rank(x) < k, and that foundation and transitivity hold. "
        "Finite stages only: nothing here reaches V_omega or beyond."
    ),
    "packages": [],
}


def members(code):
    """Codes of the members of the set with this code (its 1-bits)."""
    if code < 0:
        raise ValueError("codes are natural numbers")
    return [y for y in range(code.bit_length()) if code >> y & 1]


def from_members(codes):
    """Code of the set whose members have the given codes."""
    return sum(1 << y for y in set(codes))


@lru_cache(maxsize=None)
def rank(code):
    """rank(x) = sup{rank(y) + 1 : y in x}, by recursion on membership."""
    return max((rank(y) + 1 for y in members(code)), default=0)


def stage_sizes(k):
    """|V_0|, ..., |V_k|, using |V_0| = 0 and |V_{j+1}| = 2^|V_j|."""
    sizes = [0]
    for _ in range(k):
        sizes.append(2 ** sizes[-1])
    return sizes


def stage(k):
    """The codes in V_k, built by iterating the power set from V_0 = {}.

    Each subset of the current stage (a bitmask s over its members) is coded
    incrementally: removing the lowest member of s gives a smaller subset.
    """
    current = []
    for _ in range(k):
        codes = [0] * (1 << len(current))
        for s in range(1, len(codes)):
            low = s & -s
            codes[s] = codes[s ^ low] + (1 << current[low.bit_length() - 1])
        current = sorted(codes)
    return current


def ranks_below(n):
    """rank(x) for every code x < n, by the same recursion: the rank of x is the
    larger of rank(x minus its least member y) and rank(y) + 1."""
    ranks = [0] * n
    for x in range(1, n):
        low = x & -x
        ranks[x] = max(ranks[x ^ low], ranks[low.bit_length() - 1] + 1)
    return ranks


def is_transitive(code):
    """Is every member of a member also a member?"""
    return all(y & ~code == 0 for y in members(code))


def has_minimal_member(code):
    """Foundation: a non-empty set has a member y with y and x disjoint."""
    return any(y & code == 0 for y in members(code))


def von_neumann(n):
    """Code of the von Neumann ordinal n = {0, 1, ..., n - 1}."""
    code = 0
    for _ in range(n):
        code += 1 << code
    return code


def show(code):
    """The set as nested braces, with 0 written as the empty set {}."""
    return "{" + ", ".join(show(y) for y in members(code)) + "}"


def main():
    sizes = stage_sizes(5)
    print(f"|V_0|, ..., |V_5| = {sizes}")
    v5 = stage(5)
    print(f"V_5 built by iterating the power set: {len(v5)} sets; "
          f"equal to codes 0..{sizes[5] - 1}: {v5 == list(range(sizes[5]))}")
    ranks = ranks_below(sizes[5])
    ok = all((ranks[c] < k) == (c < sizes[k]) for k in range(6)
             for c in range(sizes[5]))
    print(f"x in V_k  <=>  rank(x) < k, for all x in V_5 and k <= 5: {ok}")
    print(f"sets in V_5 by rank: {dict(sorted(Counter(ranks).items()))}")
    # The set V_k has the codes 0..|V_k|-1 as members, so its code is 2^|V_k| - 1.
    trans = all(is_transitive(2 ** sizes[k] - 1) for k in range(5))
    print(f"the sets V_0, ..., V_4 are transitive: {trans}")
    found = all(has_minimal_member(c) for c in range(1, sizes[5]))
    print(f"every non-empty x in V_5 has a member disjoint from x: {found}")
    print()
    print("Some codes:")
    for name, code in [("ordinal 2", von_neumann(2)), ("ordinal 3", von_neumann(3)),
                       ("ordinal 4", von_neumann(4)),
                       ("pair (0, 1)", from_members([from_members([0]),
                                                     from_members([0, 1])]))]:
        text = show(code) if len(show(code)) <= 40 else "(too long to print)"
        print(f"   {name:<11} code {code:>4}  rank {rank(code)}  {text}")
    print(f"   V_3 as a set: code {2 ** sizes[3] - 1}, {show(2 ** sizes[3] - 1)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive for the 65536 sets of V_5. It "
        "illustrates the theorems V_(k+1) = P(V_k) and 'x is in V_alpha iff "
        "rank(x) < alpha' at finite stages only; the infinite stages, and the "
        "fact that every set appears at some stage, are proved in the lesson "
        "from the axioms of replacement and foundation.",
        width=78,
    ))


if __name__ == "__main__":
    main()
