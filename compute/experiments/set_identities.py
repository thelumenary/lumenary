"""Checking set identities exhaustively.

Every subset of a small universe U is represented as a Python ``frozenset``
(and, equivalently, as a bitmask: one bit per element). We check De Morgan's
laws and the distributive laws for *every* pair or triple of subsets, and we
show that a plausible-looking "law", A - (B - C) = (A - B) - C, is false by
finding its smallest counterexample.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import combinations, product
import textwrap

EXPERIMENT = {
    "id": "set_identities",
    "title": "Checking set identities exhaustively",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["sets"],
    "summary": (
        "Checks De Morgan's laws and both distributive laws on every pair or "
        "triple of subsets of a 4-element universe (a proof for that universe "
        "only, not for all sets), and finds the smallest counterexample to "
        "A - (B - C) = (A - B) - C, which does disprove that 'law' for sets in general."
    ),
    "packages": [],
}

UNIVERSE = frozenset({1, 2, 3, 4})


def all_subsets(universe):
    """Return all 2^n subsets of ``universe`` as frozensets, smallest first.

    Within one size, subsets are ordered by their sorted elements, so the order
    is deterministic.
    """
    elements = sorted(universe)
    return [frozenset(c) for r in range(len(elements) + 1) for c in combinations(elements, r)]


def complement(s, universe):
    """Return U - s, the elements of the universe that are not in s."""
    return frozenset(universe) - s


def to_bitmask(s, universe):
    """Encode subset s as an integer: bit i is 1 when the i-th smallest element is in s."""
    elements = sorted(universe)
    if not set(s) <= set(elements):
        raise ValueError("s must be a subset of the universe")
    return sum(1 << i for i, x in enumerate(elements) if x in s)


def from_bitmask(mask, universe):
    """Decode an integer bitmask back into a frozenset (inverse of :func:`to_bitmask`)."""
    elements = sorted(universe)
    if not 0 <= mask < (1 << len(elements)):
        raise ValueError("mask out of range for this universe")
    return frozenset(x for i, x in enumerate(elements) if mask >> i & 1)


def bit_operations_agree(universe):
    """Check union, intersection and complement against |, & and ~ on bitmasks.

    Returns the number of (A, B) pairs checked. Raises AssertionError on a mismatch.
    """
    full = (1 << len(universe)) - 1
    subsets = all_subsets(universe)
    for a, b in product(subsets, repeat=2):
        ma, mb = to_bitmask(a, universe), to_bitmask(b, universe)
        assert to_bitmask(a | b, universe) == ma | mb
        assert to_bitmask(a & b, universe) == ma & mb
        assert to_bitmask(complement(a, universe), universe) == ~ma & full
    return len(subsets) ** 2


#: (description, arity, lhs, rhs). lhs and rhs take (U, A, B[, C]).
IDENTITIES = [
    ("U - (A ∪ B) = (U - A) ∩ (U - B)", 2,
     lambda U, A, B: U - (A | B), lambda U, A, B: (U - A) & (U - B)),
    ("U - (A ∩ B) = (U - A) ∪ (U - B)", 2,
     lambda U, A, B: U - (A & B), lambda U, A, B: (U - A) | (U - B)),
    ("A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)", 3,
     lambda U, A, B, C: A & (B | C), lambda U, A, B, C: (A & B) | (A & C)),
    ("A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)", 3,
     lambda U, A, B, C: A | (B & C), lambda U, A, B, C: (A | B) & (A | C)),
]

NON_IDENTITY = ("A - (B - C) = (A - B) - C", 3,
                lambda U, A, B, C: A - (B - C), lambda U, A, B, C: (A - B) - C)


def check_identity(lhs, rhs, universe, arity):
    """Compare lhs and rhs on every tuple of ``arity`` subsets of ``universe``.

    Returns ``(cases_checked, counterexamples)`` where counterexamples is a list
    of the tuples of subsets on which the two sides differ.
    """
    U = frozenset(universe)
    subsets = all_subsets(U)
    failures = []
    cases = 0
    for sets in product(subsets, repeat=arity):
        cases += 1
        if lhs(U, *sets) != rhs(U, *sets):
            failures.append(sets)
    return cases, failures


def smallest_counterexample(lhs, rhs, universe, arity):
    """Return the counterexample with the fewest elements in total, or None.

    Ties are broken by comparing the sorted element lists, so the answer is
    deterministic.
    """
    _, failures = check_identity(lhs, rhs, universe, arity)
    if not failures:
        return None
    return min(failures, key=lambda sets: (sum(len(s) for s in sets), [sorted(s) for s in sets]))


def fmt(s):
    """Format a set as {1, 2} or ∅."""
    return "{" + ", ".join(str(x) for x in sorted(s)) + "}" if s else "∅"


def main():
    U = UNIVERSE
    n = len(U)
    print(f"Universe U = {fmt(U)} has 2^{n} = {2 ** n} subsets.")
    print(f"A subset is also a {n}-bit number: {fmt({1, 3})} -> {to_bitmask({1, 3}, U):0{n}b} (bit i = element i+1).")
    pairs = bit_operations_agree(U)
    print(f"∪, ∩ and complement match bitwise |, &, ~ on all {pairs} pairs: True")
    print()
    print(f"{'statement':<34}{'cases':>7}{'failures':>10}")
    for name, arity, lhs, rhs in IDENTITIES + [NON_IDENTITY]:
        cases, failures = check_identity(lhs, rhs, U, arity)
        print(f"{name:<34}{cases:>7}{len(failures):>10}")
    print()
    name, arity, lhs, rhs = NON_IDENTITY
    A, B, C = smallest_counterexample(lhs, rhs, U, arity)
    print(f"The last line is NOT an identity. Smallest counterexample (fewest elements):")
    print(f"  A = {fmt(A)}, B = {fmt(B)}, C = {fmt(C)}")
    print(f"  A - (B - C) = {fmt(A)} - {fmt(B - C)} = {fmt(A - (B - C))}")
    print(f"  (A - B) - C = {fmt(A - B)} - {fmt(C)} = {fmt((A - B) - C)}")
    cases, fails = check_identity(lambda U, A, B, C: (A - B) - C <= A - (B - C),
                                  lambda U, A, B, C: True, U, 3)
    print(f"What does hold: (A - B) - C ⊆ A - (B - C) in all {cases} cases ({len(fails)} failures).")
    print()
    print(textwrap.fill(
        "Epistemic status: every pair and triple of subsets of this 4-element "
        "universe was checked, so the four laws are proved for this universe "
        "only, not for all sets (the lesson's element-by-element argument does "
        "that). One counterexample, by contrast, is enough to show that "
        "A - (B - C) = (A - B) - C fails for sets in general.",
        width=78,
    ))


if __name__ == "__main__":
    main()
