"""V_omega, the finite shadow of an inaccessible cardinal.

An inaccessible cardinal kappa makes V_kappa a model of ZFC because kappa is
regular and a strong limit. The countable cardinal omega has both properties
too: a finite union of finite sets is finite, and the power set of a finite
set is finite. Correspondingly V_omega, the set of hereditarily finite sets,
satisfies every axiom of ZFC except Infinity.

Ackermann (1937) coded hereditarily finite sets by natural numbers: m is an
element of n exactly when bit m of n is 1. So n = 0 is the empty set, 1 is
{0}, 2 is {1} = {{0}}, 3 is {0, 1}, and so on. We use the coding to compute
ranks, check that V_k consists exactly of the codes below |V_k|, check that
pairing, union and power set never leave V_omega but do leave each V_k, and
compute how fast |V_k| grows.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from functools import lru_cache
from itertools import combinations
import math
import textwrap

EXPERIMENT = {
    "id": "large_cardinals_hereditarily_finite",
    "title": "Hereditarily finite sets: V_omega in Ackermann's coding",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["large-cardinals"],
    "summary": (
        "Codes hereditarily finite sets as natural numbers (m is in n iff bit m of n "
        "is 1), computes ranks, checks that V_k is exactly the codes below |V_k| for "
        "k <= 5, that pairing, union and power set stay inside V_omega but leave each "
        "V_k, and computes |V_k|. Exact finite checks illustrating, by analogy, why "
        "inaccessible kappa make V_kappa a model of ZFC."
    ),
    "packages": [],
}


def members(n):
    """The codes of the elements of the set coded by n."""
    return [m for m in range(n.bit_length()) if n >> m & 1]


@lru_cache(maxsize=None)
def rank(n):
    """Von Neumann rank: 0 for the empty set, else 1 + max rank of members."""
    return 1 + max(rank(m) for m in members(n)) if n else 0


def pair(a, b):
    """The code of {a, b}."""
    return (1 << a) | (1 << b)


def union(n):
    """The code of the union of the members of n."""
    result = 0
    for m in members(n):
        result |= m
    return result


def power_set(n):
    """The code of the set of all subsets of n."""
    elems, result = members(n), 0
    for k in range(len(elems) + 1):
        for subset in combinations(elems, k):
            result |= 1 << sum(1 << e for e in subset)
    return result


def size_of_v(k):
    """|V_k|: |V_0| = 0 and |V_(k+1)| = 2^|V_k|."""
    size = 0
    for _ in range(k):
        size = 2 ** size
    return size


def decimal_digits_of_power_of_two(e):
    """Number of decimal digits of 2^e, without converting to a string."""
    digits = math.floor(e * math.log10(2)) + 1
    value = 1 << e
    while 10 ** digits <= value:
        digits += 1
    while digits > 1 and 10 ** (digits - 1) > value:
        digits -= 1
    return digits


def show(n):
    """Write the set coded by n with braces, e.g. 3 -> {{}, {{}}}."""
    return "{" + ", ".join(show(m) for m in members(n)) + "}"


def main():
    print("Ackermann codes:  " + ";  ".join(f"{n} = {show(n)}" for n in range(4)))
    print("V_k is exactly the set of codes below |V_k|:")
    for k in range(6):
        size = size_of_v(k)
        exact = all(rank(n) < k for n in range(size)) and rank(size) >= k
        print(f"   |V_{k}| = {size:>5}: {exact}")
    digits = decimal_digits_of_power_of_two(65536)
    print(f"   |V_6| = 2^65536 has {digits} decimal digits")
    print()
    v4 = range(16)
    print("Closure inside V_4 (codes 0..15), the first finite stage tested:")
    print(f"   pairs stay in V_4:      {all(pair(a, b) < 16 for a in v4 for b in v4)}")
    print(f"   unions stay in V_4:     {all(union(n) < 16 for n in v4)}")
    print(f"   power sets stay in V_4: {all(power_set(n) < 16 for n in v4)}")
    top = max(v4, key=rank)
    print(f"   e.g. {{{top}}} = {{{top}, {top}}} has code {pair(top, top)} and rank "
          f"{rank(pair(top, top))}: it lies in V_5, not V_4")
    print("In V_omega every pair, union and power set of a code is again a")
    print(f"finite code; e.g. 15 codes V_3, and its power set V_4 has code "
          f"{power_set(15)}.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact computations with finitely many finite sets. "
        "They show the mechanism - each stage V_k fails to be closed, but their "
        "union V_omega is closed, because omega is regular and a strong limit - "
        "and so illustrate by analogy why V_kappa satisfies ZFC when kappa is "
        "inaccessible. That theorem is proved in the lesson; nothing about "
        "uncountable cardinals is computed here.",
        width=78,
    ))


if __name__ == "__main__":
    main()
