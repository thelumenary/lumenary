"""A relation gives a Galois connection; its fixed points correspond exactly.

Any relation R between a set X of objects and a set Y of properties gives two
maps: up(S) = the properties shared by every object in S, and down(T) = the
objects having every property in T. They form an (order-reversing) Galois
connection: S <= down(T) if and only if T <= up(S). We verify this for every
pair of subsets, and then illustrate a general fact about adjunctions: the
connection restricts to a bijection between the closed sets on the two sides
(the fixed points of down o up and of up o down), here the "formal concepts".
"""

from itertools import combinations

EXPERIMENT = {
    "id": "adjunctions_formal_concepts",
    "title": "Galois connections from a relation: closed sets on both sides",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["adjunctions"],
    "summary": (
        "For the relation 'number n in 1..8 has property p' (even, odd, prime, "
        "square, divides 12, greater than 4), checks the Galois connection "
        "S <= down(T) iff T <= up(S) for all 256 x 64 pairs of subsets, and lists "
        "the closed sets on each side, which correspond bijectively. Exhaustive for "
        "this relation only."
    ),
    "packages": [],
}

OBJECTS = list(range(1, 9))
PROPERTIES = {
    "even": lambda n: n % 2 == 0,
    "odd": lambda n: n % 2 == 1,
    "prime": lambda n: n in (2, 3, 5, 7),
    "square": lambda n: n in (1, 4),
    "div12": lambda n: 12 % n == 0,
    ">4": lambda n: n > 4,
}


def subsets(items):
    """All subsets of a list, as frozensets."""
    return [frozenset(c) for k in range(len(items) + 1)
            for c in combinations(items, k)]


def up(S):
    """Properties shared by every object in S."""
    return frozenset(p for p, has in PROPERTIES.items() if all(has(n) for n in S))


def down(T):
    """Objects having every property in T."""
    return frozenset(n for n in OBJECTS if all(PROPERTIES[p](n) for p in T))


def galois_holds():
    """Number of pairs (S, T) checked, and whether S <= down(T) iff T <= up(S)."""
    xs, ys = subsets(OBJECTS), subsets(list(PROPERTIES))
    ok = all((S <= down(T)) == (T <= up(S)) for S in xs for T in ys)
    return len(xs) * len(ys), ok


def closed_objects():
    """Fixed points of down o up: the closed sets of objects."""
    return sorted({down(up(S)) for S in subsets(OBJECTS)}, key=sorted)


def main():
    pairs, ok = galois_holds()
    print(f"S <= down(T)  iff  T <= up(S): checked {pairs} pairs, holds: {ok}")
    closed = closed_objects()
    closed_props = {up(down(T)) for T in subsets(list(PROPERTIES))}
    print(f"closed sets of objects: {len(closed)}, closed sets of properties: "
          f"{len(closed_props)}")
    matches = {up(S) for S in closed} == closed_props
    inverse = all(down(up(S)) == S for S in closed)
    print(f"up maps one onto the other: {matches}; down inverts it: {inverse}")
    print("The formal concepts (closed objects <-> closed properties):")
    for S in sorted(closed, key=lambda c: (len(c), sorted(c))):
        objs = ",".join(map(str, sorted(S))) or "-"
        props = ", ".join(sorted(up(S))) or "-"
        print(f"  {{{objs}}} <-> {{{props}}}")
    print("Unit S <= down(up(S)) is not always equality: down(up({2, 4})) = "
          f"{sorted(down(up(frozenset({2, 4}))))}")
    print()
    print("Epistemic status: an exhaustive check for one small relation. That")
    print("every relation gives a Galois connection, and that every adjunction")
    print("restricts to an equivalence between its fixed points, is proved in")
    print("the lesson.")


if __name__ == "__main__":
    main()
