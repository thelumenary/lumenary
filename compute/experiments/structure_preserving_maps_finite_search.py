"""Searching all maps between small structures for homomorphisms and isomorphisms.

A finite structure is a set with an operation table. We list every map
between two structures and keep those that preserve the operation. First,
additive maps Z/m -> Z/n for m, n <= 6: their number turns out to be
gcd(m, n). Second, we test every bijection between four 4-element groups -
clock arithmetic mod 4, the Klein four-group Z/2 x Z/2, the symmetries of a
non-square rectangle, and multiplication mod 5 on {1, 2, 3, 4} - and count
the isomorphisms. An invariant (how many x satisfy x * x = identity) explains
the zeros. Exhaustive search: complete for these structures, but the gcd
pattern for other m, n needs the lesson's proof.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import permutations, product
from math import gcd
import textwrap

EXPERIMENT = {
    "id": "structure_preserving_maps_finite_search",
    "title": "Hunting homomorphisms and isomorphisms by brute force",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["structure-preserving-maps"],
    "summary": (
        "Lists every map Z/m -> Z/n (m, n <= 6) and counts those preserving "
        "addition, finding gcd(m, n) of them; then tests all 24 bijections "
        "between four groups of order 4 and counts isomorphisms. Exhaustive for "
        "these small cases; the gcd formula in general, and the reason two "
        "groups are not isomorphic, come from proofs in the lesson."
    ),
    "packages": [],
}


def cyclic(n):
    """Z/n under addition: (elements, table) with table[(x, y)] = x + y mod n."""
    elems = list(range(n))
    return elems, {(x, y): (x + y) % n for x in elems for y in elems}


def klein():
    """Z/2 x Z/2 under componentwise addition mod 2."""
    elems = [(a, b) for a in (0, 1) for b in (0, 1)]
    table = {(x, y): ((x[0] + y[0]) % 2, (x[1] + y[1]) % 2)
             for x in elems for y in elems}
    return elems, table


def rectangle():
    """Symmetries of a non-square rectangle, as permutations of its corners.

    Corners 0, 1, 2, 3 go round the rectangle. The four symmetries are the
    identity, the half turn and the two mirror reflections; the operation
    is composition, (s * t)(c) = s(t(c)).
    """
    elems = [(0, 1, 2, 3), (2, 3, 0, 1), (1, 0, 3, 2), (3, 2, 1, 0)]
    table = {(s, t): tuple(s[t[c]] for c in range(4))
             for s in elems for t in elems}
    return elems, table


def units_mod5():
    """{1, 2, 3, 4} under multiplication mod 5."""
    elems = [1, 2, 3, 4]
    return elems, {(x, y): (x * y) % 5 for x in elems for y in elems}


def preserves(f, table_a, table_b):
    """True if f(x * y) = f(x) * f(y) for all x, y (f is a dict)."""
    return all(f[z] == table_b[(f[x], f[y])] for (x, y), z in table_a.items())


def homomorphisms(sa, sb):
    """Every operation-preserving map from structure sa to structure sb."""
    (ea, ta), (eb, tb) = sa, sb
    maps = (dict(zip(ea, values)) for values in product(eb, repeat=len(ea)))
    return [f for f in maps if preserves(f, ta, tb)]


def isomorphisms(sa, sb):
    """Every bijection sa -> sb that preserves the operation."""
    (ea, ta), (eb, tb) = sa, sb
    if len(ea) != len(eb):
        return []
    maps = (dict(zip(ea, perm)) for perm in permutations(eb))
    return [f for f in maps if preserves(f, ta, tb)]


def identity_element(s):
    """The element e with e * x = x * e = x for all x (None if there is none)."""
    elems, table = s
    for e in elems:
        if all(table[(e, x)] == x == table[(x, e)] for x in elems):
            return e
    return None


def squares_to_identity(s):
    """How many x satisfy x * x = e - a number every isomorphism preserves."""
    elems, table = s
    e = identity_element(s)
    return sum(1 for x in elems if table[(x, x)] == e)


def main():
    print("1. Additive maps Z/m -> Z/n, found by listing all n^m maps")
    print("   m\\n " + " ".join(f"{n:>3}" for n in range(1, 7)))
    agree = True
    for m in range(1, 7):
        row = [len(homomorphisms(cyclic(m), cyclic(n))) for n in range(1, 7)]
        agree &= row == [gcd(m, n) for n in range(1, 7)]
        print(f"   {m:>3} " + " ".join(f"{c:>3}" for c in row))
    print(f"   Every entry equals gcd(m, n): {agree}")
    print()
    groups = [("Z/4 (clock mod 4)", cyclic(4)), ("Z/2 x Z/2 (Klein)", klein()),
              ("rectangle symmetries", rectangle()),
              ("{1,2,3,4} times mod 5", units_mod5())]
    print("2. Isomorphisms among groups of order 4 (24 bijections tested each)")
    for i, (na, sa) in enumerate(groups):
        for nb, sb in groups[i + 1:]:
            print(f"   {na:<22} -> {nb:<22} {len(isomorphisms(sa, sb)):>2}")
    print()
    print("3. Invariant: number of x with x * x = identity")
    for name, s in groups:
        print(f"   {name:<22} {squares_to_identity(s)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exhaustive-finite. Every map in each case was "
        "tested, so these counts are certain for these structures. That the "
        "number of homomorphisms Z/m -> Z/n is gcd(m, n) for all m and n is "
        "a pattern here, which the lesson then proves. The invariant in part 3 "
        "explains the zeros in part 2, since isomorphisms preserve it.",
        width=78,
    ))


if __name__ == "__main__":
    main()
