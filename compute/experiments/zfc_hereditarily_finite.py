"""Hereditarily finite sets: the finite levels of the ZFC universe, built.

Python's frozensets behave like pure sets: two frozensets are equal exactly
when they have the same elements (Extensionality), and a frozenset can contain
frozensets. Starting from the empty set we build the finite stages V_0, V_1,
..., V_4 of the cumulative hierarchy (V_{n+1} is the power set of V_n), the
von Neumann numerals 0 = {}, n + 1 = n U {n}, and Kuratowski pairs
{{a}, {a, b}}. We then check, exhaustively on V_4, that Kuratowski pairs never
collide while the naive encoding {a, {b}} does; that every non-empty set has an
element-minimal member (Foundation); and that Ackermann's coding
code(x) = sum of 2^code(y) over y in x is a bijection V_4 -> {0, ..., 15}
turning membership into binary digits. Evidence: exact and exhaustive, but only
for the finite sets examined.
"""

from itertools import combinations, product

EXPERIMENT = {
    "id": "zfc_hereditarily_finite",
    "title": "Hereditarily finite sets: V_n, numerals and pairs",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["zfc"],
    "summary": (
        "Builds the stages V_0..V_4 of the cumulative hierarchy as Python "
        "frozensets, the von Neumann numerals and Kuratowski pairs. Checks on all "
        "256 ordered pairs from V_4 that Kuratowski pairs never collide while the "
        "encoding {a, {b}} does, that every non-empty set in V_4 has an "
        "element-minimal member, and that Ackermann's coding maps V_4 onto 0..15 "
        "with membership read off binary digits. Exhaustive only for V_4."
    ),
    "packages": [],
}

EMPTY = frozenset()


def powerset(s):
    """All subsets of the finite set ``s``, as a frozenset of frozensets."""
    items = sorted(s, key=ackermann)
    subsets = []
    for r in range(len(items) + 1):
        subsets.extend(frozenset(c) for c in combinations(items, r))
    return frozenset(subsets)


def hierarchy(n):
    """Return [V_0, V_1, ..., V_n] with V_0 = {} and V_{k+1} = P(V_k)."""
    if n < 0:
        raise ValueError("n must be non-negative")
    stages = [EMPTY]
    for _ in range(n):
        stages.append(powerset(stages[-1]))
    return stages


def succ(x):
    """The von Neumann successor x U {x}."""
    return x | frozenset([x])


def numeral(n):
    """The von Neumann numeral for the natural number n."""
    if n < 0:
        raise ValueError("n must be non-negative")
    x = EMPTY
    for _ in range(n):
        x = succ(x)
    return x


def kpair(a, b):
    """Kuratowski's ordered pair {{a}, {a, b}}."""
    return frozenset([frozenset([a]), frozenset([a, b])])


def naive_pair(a, b):
    """A flawed encoding of ordered pairs: {a, {b}}."""
    return frozenset([a, frozenset([b])])


def collisions(universe, pair):
    """Pairs of distinct ordered pairs from ``universe`` with equal codes."""
    seen, bad = {}, []
    for a, b in product(sorted(universe, key=ackermann), repeat=2):
        code = pair(a, b)
        if code in seen and seen[code] != (a, b):
            bad.append((seen[code], (a, b)))
        seen.setdefault(code, (a, b))
    return bad


def has_minimal_element(x):
    """Foundation for one set: some y in x shares no element with x."""
    return any(not (y & x) for y in x)


def ackermann(x):
    """Ackermann's code: the sum of 2^code(y) over the elements y of x."""
    return sum(2 ** ackermann(y) for y in x)


def decode(n):
    """Inverse of ``ackermann``: the set whose elements have codes = bits of n."""
    if n < 0:
        raise ValueError("n must be non-negative")
    return frozenset(decode(i) for i in range(n.bit_length()) if n >> i & 1)


def show(x):
    """Write a hereditarily finite set with braces, {} for the empty set."""
    inner = ", ".join(show(y) for y in sorted(x, key=ackermann))
    return "{" + inner + "}"


def main():
    stages = hierarchy(4)
    sizes = ", ".join(f"|V_{k}| = {len(v)}" for k, v in enumerate(stages))
    print("1. The cumulative hierarchy, V_(n+1) = P(V_n):")
    print("   " + sizes)
    print("   |V_5| = 2^16 = 65536; |V_6| = 2^65536 has 19729 digits (not built)")
    print("2. von Neumann numerals, n + 1 = n U {n}:")
    for n in range(4):
        print(f"   {n} = {show(numeral(n))}")
    print("   Ackermann codes of 0..4:", [ackermann(numeral(n)) for n in range(5)])
    v4 = stages[4]
    good, bad = collisions(v4, kpair), collisions(v4, naive_pair)
    print("3. Ordered pairs of elements of V_4 (256 pairs):")
    print(f"   Kuratowski {{{{a}}, {{a, b}}}}: {len(good)} collisions")
    print(f"   naive {{a, {{b}}}}:          {len(bad)} collisions, for example")
    (a, b), (c, d) = bad[0]
    print(f"   a = {show(a)}, b = {show(b)}  and  c = {show(c)}, d = {show(d)}")
    print(f"   both give {show(naive_pair(a, b))}")
    nonempty = [x for x in v4 if x]
    found = sum(has_minimal_element(x) for x in nonempty)
    print(f"4. Foundation: {found} of {len(nonempty)} non-empty sets in V_4 have")
    print("   an element-minimal member (one disjoint from the set itself)")
    codes = sorted(ackermann(x) for x in v4)
    agree = all((x in y) == bool(ackermann(y) >> ackermann(x) & 1)
                for x in v4 for y in v4)
    print(f"5. Ackermann coding maps V_4 onto 0..15: {codes == list(range(16))};")
    print(f"   x in y  <=>  bit code(x) of code(y) is 1, for all 256 pairs: {agree}")
    print()
    print("Epistemic status: every check is exact and exhaustive, but only for")
    print("the sixteen sets of V_4. That Kuratowski pairs work for all sets is a")
    print("theorem proved in the lesson; Foundation for arbitrary sets is an axiom,")
    print("which no computation can confirm. That V_omega, the union of all V_n,")
    print("satisfies every ZFC axiom except Infinity is a theorem, not checked here.")


if __name__ == "__main__":
    main()
